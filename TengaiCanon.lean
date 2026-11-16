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
  { id := "name-type", message := "the last component of an inductive type's name is not UpperCamelCase" }
]

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

def isSnake (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: _ => c.isLower && s.all fun d => d.isLower || d.isDigit || d == '_' || d == '\''

def isUpperCamel (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: _ => c.isUpper && s.all fun d => d.isAlphanum

/-- the rule ids a declaration breaks -/
def violations (n : Name) (ci : ConstantInfo) : Array String := Id.run do
  let mut out : Array String := #[]
  match ci with
  | .thmInfo _ =>
    if hasGtGe ci.type then out := out.push "gt-ge"
    if hasNotEq ci.type then out := out.push "not-eq"
    if hasNatSucc ci.type then out := out.push "nat-succ"
    if !isSnake (lastComponent n) then out := out.push "name-theorem"
  | .inductInfo _ =>
    if !isUpperCamel (lastComponent n) then out := out.push "name-type"
  | _ => pure ()
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
    for r in violations n ci do
      out := out.push s!"violation\t{r}\t{n}\t{m}"
  return out

end TengaiCanon

unsafe def main (argv : List String) : IO UInt32 := do
  enableInitializersExecution
  if argv.contains "--list-rules" then
    for r in TengaiCanon.rules do IO.println r.id
    return 0
  let mods := ((argv.zip (argv.drop 1)).filterMap fun (a, b) => if a == "--module" then some b else none).map String.toName
  if mods.isEmpty then
    IO.eprintln "usage: tengai-canon --module <M> [--module <M>…] | --list-rules"
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules (mods.eraseDups.toArray.map fun m => { module := m }) {} (trustLevel := 0) (loadExts := true)
  let lines := TengaiCanon.report env mods
  for l in lines do IO.println l
  for l in lines do
    let rid := (l.splitOn "\t").getD 1 ""
    match TengaiCanon.rules.find? (·.id == rid) with
    | some r => IO.eprintln s!"{(l.splitOn "\t").getD 2 ""}: {r.message}"
    | none => pure ()
  return (if lines.isEmpty then 0 else 1)
