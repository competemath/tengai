import Lean
open Lean

/-!
# tengai-replay: the content of a Tengoku export becomes a built `.olean`

`lake exe tengai-replay EXPORT.ndjson --module TengaiData.Foo --out DIR` reads a `lean4export` file (format 3.x) and replays every declaration into an environment that holds only Lean core
(`Init`), through the KERNEL (`addDecl`): a wrong proof term is refused, whatever tool produced the export (invariant I1: untrusted search, trusted checking). It then writes
`DIR/TengaiData/Foo.olean`, which `import TengaiData.Foo` reads when `DIR` is on `LEAN_PATH`.

A constant that Lean core already holds is not added again: it must have the same type, or the replay stops. What is added is exactly what Lean core lacks, so the file is the
shortest transplant of a theorem (its reduced closure, `tools/closure`). Nothing is registered (no simp set, no instance, no attribute): a replayed module is searchable and active
only through the scoped, explicit layer of a topic (invariant I4). Expression metadata is dropped (it has no meaning for the kernel).

This tool imports `Lean`; the modules it writes do not. It is never imported by the library, so `import Tengai` stays as small as its content.
-/

namespace TengaiReplay

structure Tables where
  names : Array Name := #[Name.anonymous]
  levels : Array Level := #[Level.zero]
  exprs : Array Expr := #[]

structure Stats where
  added : Nat := 0
  skipped : Nat := 0
  inductives : Nat := 0
  deriving ToJson

def fail {α : Type} (msg : String) : IO α := throw (IO.userError s!"replay: {msg}")

def has (j : Json) (k : String) : Bool := (j.getObjVal? k).toOption.isSome

def obj (j : Json) (k : String) : IO Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error e => fail s!"{k}: {e}"

def nat (j : Json) (k : String) : IO Nat :=
  match j.getObjValAs? Nat k with
  | .ok v => pure v
  | .error e => fail s!"{k}: {e}"

def str (j : Json) (k : String) : IO String :=
  match j.getObjValAs? String k with
  | .ok v => pure v
  | .error e => fail s!"{k}: {e}"

def bool (j : Json) (k : String) : IO Bool :=
  match j.getObjValAs? Bool k with
  | .ok v => pure v
  | .error e => fail s!"{k}: {e}"

def natArr (j : Json) (k : String) : IO (Array Nat) :=
  match j.getObjValAs? (Array Nat) k with
  | .ok v => pure v
  | .error e => fail s!"{k}: {e}"

def jsonArr (j : Json) (k : String) : IO (Array Json) :=
  match j.getObjValAs? (Array Json) k with
  | .ok v => pure v
  | .error e => fail s!"{k}: {e}"

def getName (t : Tables) (i : Nat) : IO Name :=
  match t.names[i]? with
  | some n => pure n
  | none => fail s!"name {i} is not defined yet"

def getLevel (t : Tables) (i : Nat) : IO Level :=
  match t.levels[i]? with
  | some l => pure l
  | none => fail s!"level {i} is not defined yet"

def getExpr (t : Tables) (i : Nat) : IO Expr :=
  match t.exprs[i]? with
  | some e => pure e
  | none => fail s!"term {i} is not defined yet"

def binderInfo (s : String) : IO BinderInfo :=
  match s with
  | "default" => pure BinderInfo.default
  | "implicit" => pure BinderInfo.implicit
  | "strictImplicit" => pure BinderInfo.strictImplicit
  | "instImplicit" => pure BinderInfo.instImplicit
  | _ => fail s!"binder info {s}"

def readName (t : Tables) (o : Json) : IO Tables := do
  let idx ← nat o "in"
  if idx != t.names.size then fail s!"name {idx} out of order"
  if has o "str" then
    let v ← obj o "str"
    let pre ← getName t (← nat v "pre")
    let s ← str v "str"
    pure { t with names := t.names.push (Name.str pre s) }
  else
    let v ← obj o "num"
    let pre ← getName t (← nat v "pre")
    let i ← nat v "i"
    pure { t with names := t.names.push (Name.num pre i) }

def readLevel (t : Tables) (o : Json) : IO Tables := do
  let idx ← nat o "il"
  if idx != t.levels.size then fail s!"level {idx} out of order"
  let l : Level ←
    if has o "succ" then
      pure (Level.succ (← getLevel t (← nat o "succ")))
    else if has o "max" then
      let a ← natArr o "max"
      pure (Level.max (← getLevel t a[0]!) (← getLevel t a[1]!))
    else if has o "imax" then
      let a ← natArr o "imax"
      pure (Level.imax (← getLevel t a[0]!) (← getLevel t a[1]!))
    else if has o "param" then
      pure (Level.param (← getName t (← nat o "param")))
    else
      fail s!"level {idx}: unknown kind"
  pure { t with levels := t.levels.push l }

def readExpr (t : Tables) (o : Json) : IO Tables := do
  let idx ← nat o "ie"
  if idx != t.exprs.size then fail s!"term {idx} out of order"
  let e : Expr ←
    if has o "bvar" then
      pure (Expr.bvar (← nat o "bvar"))
    else if has o "sort" then
      pure (Expr.sort (← getLevel t (← nat o "sort")))
    else if has o "const" then
      let v ← obj o "const"
      let us ← natArr v "us"
      let ls ← us.toList.mapM (getLevel t)
      pure (Expr.const (← getName t (← nat v "name")) ls)
    else if has o "app" then
      let v ← obj o "app"
      pure (Expr.app (← getExpr t (← nat v "fn")) (← getExpr t (← nat v "arg")))
    else if has o "lam" then
      let v ← obj o "lam"
      let bi ← binderInfo (← str v "binderInfo")
      pure (Expr.lam (← getName t (← nat v "name")) (← getExpr t (← nat v "type")) (← getExpr t (← nat v "body")) bi)
    else if has o "forallE" then
      let v ← obj o "forallE"
      let bi ← binderInfo (← str v "binderInfo")
      pure (Expr.forallE (← getName t (← nat v "name")) (← getExpr t (← nat v "type")) (← getExpr t (← nat v "body")) bi)
    else if has o "letE" then
      let v ← obj o "letE"
      let nd ← bool v "nondep"
      pure (Expr.letE (← getName t (← nat v "name")) (← getExpr t (← nat v "type")) (← getExpr t (← nat v "value")) (← getExpr t (← nat v "body")) nd)
    else if has o "proj" then
      let v ← obj o "proj"
      pure (Expr.proj (← getName t (← nat v "typeName")) (← nat v "idx") (← getExpr t (← nat v "struct")))
    else if has o "natVal" then
      pure (Expr.lit (Literal.natVal (← str o "natVal").toNat!))
    else if has o "strVal" then
      pure (Expr.lit (Literal.strVal (← str o "strVal")))
    else if has o "mdata" then
      let v ← obj o "mdata"
      getExpr t (← nat v "expr")
    else
      fail s!"term {idx}: unknown kind"
  pure { t with exprs := t.exprs.push e }

def levelParams (t : Tables) (v : Json) : IO (List Name) := do
  let a ← natArr v "levelParams"
  a.toList.mapM (getName t)

def allNames (t : Tables) (v : Json) : IO (List Name) := do
  let a ← natArr v "all"
  a.toList.mapM (getName t)

def constantVal (t : Tables) (v : Json) : IO ConstantVal := do
  let n ← getName t (← nat v "name")
  let ps ← levelParams t v
  let ty ← getExpr t (← nat v "type")
  pure { name := n, levelParams := ps, type := ty }

/-- the term without expression metadata (`@& Nat` is `mdata` around `Nat`: the export drops it, the kernel never looks at it) -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun s => match s with
    | .mdata _ b => some (stripMData b)
    | _ => none

/-- the first subterm where two terms differ (the diagnostic of a refused comparison) -/
partial def firstDiff (a b : Expr) : String :=
  if a == b then "" else
  match a, b with
  | .app f x, .app g y =>
    let d := firstDiff f g
    if d.isEmpty then firstDiff x y else d
  | .lam n1 t1 b1 i1, .lam n2 t2 b2 i2 =>
    let d := firstDiff t1 t2
    let d := if d.isEmpty then firstDiff b1 b2 else d
    if d.isEmpty then s!"lam binder: name {n1} vs {n2}, info {repr i1} vs {repr i2}, domain {(toString t1).take 120}" else d
  | .forallE n1 t1 b1 i1, .forallE n2 t2 b2 i2 =>
    let d := firstDiff t1 t2
    let d := if d.isEmpty then firstDiff b1 b2 else d
    if d.isEmpty then s!"forall binder: name {n1} vs {n2}, info {repr i1} vs {repr i2}, domain {(toString t1).take 120}" else d
  | .letE n1 t1 v1 b1 d1, .letE n2 t2 v2 b2 d2 =>
    let d := firstDiff t1 t2
    let d := if d.isEmpty then firstDiff v1 v2 else d
    let d := if d.isEmpty then firstDiff b1 b2 else d
    if d.isEmpty then s!"let: name {n1} vs {n2}, nondep {d1} vs {d2}" else d
  | .proj s1 i x, .proj s2 j y =>
    if s1 != s2 || i != j then s!"proj {s1}.{i} vs {s2}.{j}" else firstDiff x y
  | _, _ => s!"{(toString a).take 300}  <>  {(toString b).take 300}"

/-- true when Lean core already holds the constant (then its type must be the exported one) -/
def alreadyThere (env : Environment) (n : Name) (type : Expr) : IO Bool :=
  match env.find? n with
  | none => pure false
  | some ci => if stripMData ci.type == type then pure true else fail s!"{n} is in the environment with another type\n first difference: {firstDiff (stripMData ci.type) type}"

def addDecl (env : Environment) (d : Declaration) : IO Environment :=
  -- no heartbeat limit (0), the default recursion depth: the kernel is the judge, not a timer
  match env.addDeclCore 0 512 d none with
  | .ok e => pure e
  | .error ex => do fail s!"the kernel refused a declaration: {← (ex.toMessageData {}).toString}"

def readInductive (t : Tables) (env : Environment) (v : Json) (st : Stats) : IO (Environment × Stats) := do
  let types ← jsonArr v "types"
  let ctors ← jsonArr v "ctors"
  let recs ← jsonArr v "recs"
  let mut ctorTable : Array (Name × Expr) := #[]
  for c in ctors do
    ctorTable := ctorTable.push ((← getName t (← nat c "name")), (← getExpr t (← nat c "type")))
  let first := types[0]!
  let firstName ← getName t (← nat first "name")
  let firstType ← getExpr t (← nat first "type")
  if (← alreadyThere env firstName firstType) then
    return (env, { st with skipped := st.skipped + 1 })
  let ps ← levelParams t first
  let np ← nat first "numParams"
  let unsafeFlag ← bool first "isUnsafe"
  let mut its : List InductiveType := []
  for ty in types do
    let n ← getName t (← nat ty "name")
    let tp ← getExpr t (← nat ty "type")
    let cn ← (← natArr ty "ctors").toList.mapM (getName t)
    let mut cs : List Constructor := []
    for c in cn do
      match ctorTable.find? (·.1 == c) with
      | some (_, ct) => cs := cs ++ [{ name := c, type := ct : Constructor }]
      | none => fail s!"constructor {c} of {n} is not in the group"
    its := its ++ [{ name := n, type := tp, ctors := cs : InductiveType }]
  let env ← addDecl env (Declaration.inductDecl ps np its unsafeFlag)
  -- the exported recursors are redundant data: the kernel derived its own, and they must agree
  for r in recs do
    let rn ← getName t (← nat r "name")
    let rt ← getExpr t (← nat r "type")
    match env.find? rn with
    | some ci => if stripMData ci.type != rt then fail s!"the recursor {rn} differs from the exported one"
    | none => fail s!"the recursor {rn} was not derived"
  pure (env, { st with added := st.added + 1, inductives := st.inductives + 1 })

def readDecl (t : Tables) (env : Environment) (o : Json) (st : Stats) : IO (Environment × Stats) := do
  if has o "axiom" then
    let v ← obj o "axiom"
    let cv ← constantVal t v
    if (← alreadyThere env cv.name cv.type) then return (env, { st with skipped := st.skipped + 1 })
    let u ← bool v "isUnsafe"
    let env ← addDecl env (Declaration.axiomDecl { toConstantVal := cv, isUnsafe := u })
    pure (env, { st with added := st.added + 1 })
  else if has o "def" then
    let v ← obj o "def"
    let cv ← constantVal t v
    if (← alreadyThere env cv.name cv.type) then return (env, { st with skipped := st.skipped + 1 })
    let value ← getExpr t (← nat v "value")
    let hints : ReducibilityHints ←
      match (← obj v "hints") with
      | Json.str "opaque" => pure ReducibilityHints.opaque
      | Json.str "abbrev" => pure ReducibilityHints.abbrev
      | h => pure (ReducibilityHints.regular (← nat h "regular").toUInt32)
    let safety : DefinitionSafety ←
      match (← str v "safety") with
      | "unsafe" => pure DefinitionSafety.unsafe
      | "safe" => pure DefinitionSafety.safe
      | "partial" => pure DefinitionSafety.partial
      | s => fail s!"definition safety {s}"
    let all ← allNames t v
    let env ← addDecl env (Declaration.defnDecl { toConstantVal := cv, value := value, hints := hints, safety := safety, all := all })
    pure (env, { st with added := st.added + 1 })
  else if has o "thm" then
    let v ← obj o "thm"
    let cv ← constantVal t v
    if (← alreadyThere env cv.name cv.type) then return (env, { st with skipped := st.skipped + 1 })
    let value ← getExpr t (← nat v "value")
    let all ← allNames t v
    let env ← addDecl env (Declaration.thmDecl { toConstantVal := cv, value := value, all := all })
    pure (env, { st with added := st.added + 1 })
  else if has o "opaque" then
    let v ← obj o "opaque"
    let cv ← constantVal t v
    if (← alreadyThere env cv.name cv.type) then return (env, { st with skipped := st.skipped + 1 })
    let value ← getExpr t (← nat v "value")
    let u ← bool v "isUnsafe"
    let all ← allNames t v
    let env ← addDecl env (Declaration.opaqueDecl { toConstantVal := cv, value := value, isUnsafe := u, all := all })
    pure (env, { st with added := st.added + 1 })
  else if has o "quot" then
    let v ← obj o "quot"
    let cv ← constantVal t v
    if (← alreadyThere env cv.name cv.type) then return (env, { st with skipped := st.skipped + 1 })
    let env ← addDecl env Declaration.quotDecl
    pure (env, { st with added := st.added + 1 })
  else if has o "inductive" then
    readInductive t env (← obj o "inductive") st
  else
    fail s!"unknown declaration line: {(toString o).take 100}"

partial def loop (h : IO.FS.Handle) (t : Tables) (env : Environment) (st : Stats) : IO (Environment × Stats) := do
  let line ← h.getLine
  if line.isEmpty then return (env, st)
  let line := line.trimAsciiEnd.copy
  if line.isEmpty then return (← loop h t env st)
  let o ← match Json.parse line with
    | .ok j => pure j
    | .error e => fail s!"not JSON: {e}"
  if has o "meta" then
    let v ← obj (← obj (← obj o "meta") "format") "version"
    match v.getStr? with
    | .ok s => if !s.startsWith "3." then fail s!"export format {s}, this reads 3.x"
    | .error _ => fail "meta without a format version"
    loop h t env st
  else if has o "in" then
    loop h (← readName t o) env st
  else if has o "il" then
    loop h (← readLevel t o) env st
  else if has o "ie" then
    loop h (← readExpr t o) env st
  else
    let (env, st) ← readDecl t env o st
    loop h t env st

def usage : String := "usage: tengai-replay EXPORT.ndjson --module TengaiData.Foo --out DIR"

end TengaiReplay

open TengaiReplay in
unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [export_, "--module", m, "--out", out] =>
    enableInitializersExecution
    initSearchPath (← findSysroot)
    let env ← importModules #[{ module := `Init }] {} (loadExts := true)
    let h ← IO.FS.Handle.mk export_ IO.FS.Mode.read
    let (env, st) ← loop h {} env {}
    let modName := m.toName
    let env := env.setMainModule modName
    let rel := String.intercalate "/" (modName.components.map toString) ++ ".olean"
    let path : System.FilePath := (System.FilePath.mk out) / rel
    if let some p := path.parent then IO.FS.createDirAll p
    writeModule env path
    IO.println (toJson st).compress
    return 0
  | _ =>
    IO.eprintln usage
    return 2
