import Lean
open Lean

/-!
# tengai-canon: the one canonical form, checked

`lake exe tengai-canon --module Tengai` lists every declaration of the library that breaks a rule of `conventions.toml` and exits 1 if there is one. It reads the ELABORATED
statement (the type of the constant), not the text, so a notation, a macro or a different spelling cannot hide a violation. It only imports Lean (the checker must not depend
on what it checks).

`--list-rules` prints the rule ids: `tests/test_canon.py` holds them equal to the ids of `conventions.toml`, so a rule cannot exist in one place only.
-/

namespace TengaiCanon

/-- one rule: its id (the key of conventions.toml) and the message a violation prints -/
structure Rule where
  id : String
  message : String

def rules : Array Rule := #[
  { id := "gt-ge", message := "a statement uses `>` or `≥`: write `<` or `≤` with the two sides swapped" },
  { id := "not-eq", message := "a statement uses `¬ a = b`: write `a ≠ b`" },
  { id := "nat-succ", message := "a statement uses `Nat.succ n`: write `n + 1`" },
  { id := "name-theorem", message := "the last component of a theorem's name is not snake_case (lowercase letters, digits, `_`, `'`)" },
  { id := "name-type", message := "the last component of an inductive type's name is not UpperCamelCase" },
  { id := "global-simp", message := "a theorem is a global `simp` lemma: make it `scoped` or `local` inside its topic (invariant I4: searchable, not active)" },
  { id := "def-irreducible", message := "a definition is not `@[irreducible]`: exported definitions are irreducible and come with API lemmas (invariant I5, no unfolding upstream)" },
  { id := "no-peek", message := "a proof unfolds a definition Tengai does not own (`unfold`, `delta`, `unseal`, or a definition as a `simp`/`dsimp`/`rw` rule): use its API lemmas (invariant I5)" },
  { id := "global-instance", message := "a declaration is a global instance: make it `scoped` or `local` inside its topic (invariant I4: searchable, not active)" }
]

/-- the declaration is registered in the GLOBAL simp set (a `scoped` or `local` simp attribute is not in this state until its namespace is opened) -/
def isGlobalSimp (env : Environment) (n : Name) : Bool :=
  (Lean.Meta.simpExtension.getState env).isLemma (.decl n)

/-- the declaration is a GLOBAL instance (a `scoped` or `local` instance is not in the imported instance table until its namespace is opened) -/
def isGlobalInstance (env : Environment) (n : Name) : Bool :=
  Lean.Meta.isInstanceCore env n

def hasGtGe (e : Expr) : Bool :=
  (e.find? fun s => s.isAppOf ``GT.gt || s.isAppOf ``GE.ge).isSome

def hasNotEq (e : Expr) : Bool :=
  (e.find? fun s => match s with
    | .app (.const ``Not _) (.app (.app (.app (.const ``Eq _) _) _) _) => true
    | _ => false).isSome

def hasNatSucc (e : Expr) : Bool :=
  (e.find? fun s => s.isConstOf ``Nat.succ).isSome

def lastComponent (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => ""

/-- names Lean itself gives to the lemmas it generates for an inductive type or a structure: the author did not write them, so no rule reads them -/
def generatedLemma (s : String) : Bool :=
  s == "sizeOf_spec" || s == "injEq"

def isSnake (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: _ => c.isLower && s.all fun d => d.isLower || d.isDigit || d == '_' || d == '\''

def isUpperCamel (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: _ => c.isUpper && s.all fun d => d.isAlphanum

/-- the head symbol of the result type of a declaration (below its binders) -/
partial def resultHead (e : Expr) : Expr :=
  match e with
  | .forallE _ _ b _ => resultHead b
  | .mdata _ b => resultHead b
  | _ => e.getAppFn

/-- the definitions Lean generates for an inductive type (a constructor-index function, the `noConfusion` pair, the eliminators): the author did not write them -/
def generatedDef (env : Environment) (n : Name) : Bool :=
  ["noConfusionType", "noConfusion", "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType", "recOn", "casesOn", "below", "brecOn", "binductionOn", "ibelow"].contains (lastComponent n)
    && (match env.find? n.getPrefix with | some (.inductInfo _) => true | _ => false)

/-- a definition that is not subject to `def-irreducible`: irreducible already; an instance (its type is a class: a global, scoped or local instance is such a definition); the lemmas and
projections Lean generates for a type -/
def irreducibleExempt (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  getReducibilityStatusCore env n == .irreducible
    || (match resultHead ci.type with | .const c _ => isClass env c | _ => false)
    || generatedDef env n || env.isProjectionFn n || isAuxRecursor env n || isNoConfusion env n || Lean.Meta.isMatcherCore env n

/-- the rule ids a declaration breaks -/
def violations (env : Environment) (n : Name) (ci : ConstantInfo) : Array String := Id.run do
  let mut out : Array String := #[]
  match ci with
  | .thmInfo _ =>
    if hasGtGe ci.type then out := out.push "gt-ge"
    if hasNotEq ci.type then out := out.push "not-eq"
    if hasNatSucc ci.type then out := out.push "nat-succ"
    if !generatedLemma (lastComponent n) && !isSnake (lastComponent n) then out := out.push "name-theorem"
    if !generatedLemma (lastComponent n) && isGlobalSimp env n then out := out.push "global-simp"  -- the lemmas Lean generates (`sizeOf_spec`, `injEq`) are global simp lemmas by construction: not the author's
  | .inductInfo _ =>
    if !isUpperCamel (lastComponent n) then out := out.push "name-type"
  | .defnInfo _ =>
    if !irreducibleExempt env n ci then out := out.push "def-irreducible"
  | _ => pure ()
  if isGlobalInstance env n then out := out.push "global-instance"
  return out

/-- the declarations to look at: those defined in a module under one of `mods`, whose name is the author's (no generated auxiliary name) -/
def selected (env : Environment) (mods : List Name) : Array (String × Name × ConstantInfo) := Id.run do
  let mut out : Array (String × Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal || n.hasMacroScopes then continue
    let some idx := env.getModuleIdxFor? n | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    if !mods.any (·.isPrefixOf m) then continue
    out := out.push (m.toString, n, ci)
  return out.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1.toString < b.2.1.toString)

/-- one line a violation: `violation<TAB>rule<TAB>declaration<TAB>module` -/
def report (env : Environment) (mods : List Name) : Array String := Id.run do
  let mut out : Array String := #[]
  for (m, n, ci) in selected env mods do
    for r in violations env n ci do
      out := out.push s!"violation\t{r}\t{n}\t{m}"
  return out

/-! ## `no-peek`: a proof that looks inside a definition it does not own (a rule on SOURCE, not on the compiled library: unfolding leaves no trace in the proof term) -/

/-- one scope of the file: the namespace it adds and the namespaces opened in it -/
structure Frame where
  ns : Name := .anonymous
  opens : List Name := []

/-- the constants an identifier can mean at this point of the file: it as written, below each enclosing namespace, below each opened namespace -/
def candidates (frames : List Frame) (id : Name) : List Name := Id.run do
  let nss := frames.reverse.foldl (fun (acc : List Name) f => acc ++ [(acc.getLast?.getD .anonymous) ++ f.ns]) [Name.anonymous]
  let mut out : List Name := [id]
  for ns in nss.reverse do out := out ++ [ns ++ id]
  for f in frames do
    for o in f.opens do out := out ++ [o ++ id]
  return out

/-- the declaration is a definition that is not Tengai's: defined in a module outside `Tengai` (a definition of the file itself is its own) -/
def foreignDef (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.defnInfo _) =>
    match env.getModuleIdxFor? c with
    | none => false
    | some idx => !(`Tengai).isPrefixOf (env.header.moduleNames[idx.toNat]?.getD .anonymous)
  | _ => false

partial def identsOf (s : Syntax) : Array Syntax :=
  match s with
  | .ident .. => #[s]
  | .node _ _ args => args.foldl (fun acc a => acc ++ identsOf a) #[]
  | _ => #[]

def peekTactics : List SyntaxNodeKind :=
  [``Lean.Parser.Tactic.unfold, ``Lean.Parser.Tactic.simp, ``Lean.Parser.Tactic.simpAll, ``Lean.Parser.Tactic.dsimp, ``Lean.Parser.Tactic.rwSeq]

/-- the rows (`what`, byte position) one command breaks `no-peek` with, given the scopes in force -/
partial def peeks (env : Environment) (frames : List Frame) (s : Syntax) : Array (String × Nat) := Id.run do
  let mut out : Array (String × Nat) := #[]
  match s with
  | .node _ k args =>
    let pos := (s.getPos?.map (·.byteIdx)).getD 0
    if (k.toString.splitOn "nseal").length > 1 then out := out.push ("unseal", pos)
    else if k == ``Lean.Parser.Tactic.delta then out := out.push ("delta", pos)
    else if peekTactics.contains k then
      for i in identsOf s do
        for c in candidates frames i.getId do
          if env.contains c then
            if foreignDef env c then out := out.push (c.toString, (i.getPos?.map (·.byteIdx)).getD pos)
            break
    for a in args do out := out ++ peeks env frames a
  | _ => pure ()
  return out

/-- the scopes after a command that opens or closes one -/
def scopeStep (frames : List Frame) (s : Syntax) : List Frame :=
  if s.isOfKind ``Lean.Parser.Command.namespace then { ns := s[1].getId } :: frames
  else if s.isOfKind ``Lean.Parser.Command.section then {} :: frames
  else if s.isOfKind ``Lean.Parser.Command.end then frames.drop 1
  else if s.isOfKind ``Lean.Parser.Command.open then
    let os := (identsOf s).toList.map (·.getId)
    match frames with
    | f :: rest => { f with opens := f.opens ++ os } :: rest
    | [] => [{ opens := os }]
  else frames

/-- `no-peek` over one source file: `violation<TAB>no-peek<TAB>what@file:line<TAB>file` -/
unsafe def peekReport (file : String) : IO (Array String) := do
  enableInitializersExecution
  let text ← IO.FS.readFile file
  let ictx := Parser.mkInputContext text file
  let (header, ps, msgs) ← Parser.parseHeader ictx
  let env ← importModules (Elab.headerToImports header) {} (trustLevel := 0) (loadExts := true)
  let st ← Elab.IO.processCommands ictx ps (Elab.Command.mkState env msgs {})
  let env := st.commandState.env
  let mut frames : List Frame := []
  let mut out : Array String := #[]
  for c in st.commands do
    -- `open X in cmd`: the scope of X is the command `cmd` only; `unseal X in cmd` is itself a peek, found by the walk
    let isIn := c.isOfKind ``Lean.Parser.Command.in
    let here := if isIn then scopeStep frames c[0] else frames
    for (what, pos) in peeks env here c do
      out := out.push s!"violation\tno-peek\t{what}@{file}:{(ictx.fileMap.toPosition ⟨pos⟩).line}\t{file}"
    if !isIn then frames := scopeStep frames c
  return out.toList.eraseDups.toArray

end TengaiCanon

unsafe def main (argv : List String) : IO UInt32 := do
  enableInitializersExecution
  if argv.contains "--list-rules" then
    for r in TengaiCanon.rules do IO.println r.id
    return 0
  let mods := ((argv.zip (argv.drop 1)).filterMap fun (a, b) => if a == "--module" then some b else none).map String.toName
  let files := (argv.zip (argv.drop 1)).filterMap fun (a, b) => if a == "--source" then some b else none
  if mods.isEmpty && files.isEmpty then
    IO.eprintln "usage: tengai-canon --module <M> [--module <M>…] [--source <FILE>…] | --list-rules"
    return 2
  initSearchPath (← findSysroot)
  let mut lines : Array String := #[]
  if !mods.isEmpty then
    let env ← importModules (mods.eraseDups.toArray.map fun m => { module := m }) {} (trustLevel := 0) (loadExts := true)
    lines := TengaiCanon.report env mods
  for f in files do lines := lines ++ (← TengaiCanon.peekReport f)
  for l in lines do IO.println l
  for l in lines do
    let rid := (l.splitOn "\t").getD 1 ""
    match TengaiCanon.rules.find? (·.id == rid) with
    | some r => IO.eprintln s!"{(l.splitOn "\t").getD 2 ""}: {r.message}"
    | none => pure ()
  return (if lines.isEmpty then 0 else 1)
