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
  /-- binder names and annotations to restore on the leading telescope of a constant's type (from `--ext`) -/
  fixes : Std.HashMap Name (Array (Name × BinderInfo)) := {}

structure Stats where
  added : Nat := 0
  skipped : Nat := 0
  inductives : Nat := 0
  /-- declarations left out because `--only` did not name them (they belong to another module of a layered promotion) -/
  filtered : Nat := 0
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

/-- restore the names and annotations of the leading binders (lean4export shares terms that differ only there, and keeps the first it saw) -/
def fixTelescope (e : Expr) (fx : Array (Name × BinderInfo)) (i : Nat := 0) : Expr :=
  match e with
  | .forallE _ ty b _ =>
    match fx[i]? with
    | some (n, bi') => .forallE n ty (fixTelescope b fx (i + 1)) bi'
    | none => e
  | _ => e

def fixedType (t : Tables) (n : Name) (e : Expr) : Expr :=
  match t.fixes[n]? with
  | some fx => fixTelescope e fx
  | none => e

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
  pure { name := n, levelParams := ps, type := fixedType t n ty }

/-- the term as the kernel reads it, for comparing a constant with one Lean core already holds: without expression metadata (`@& Nat` is `mdata` around `Nat`; the export drops it)
and without the `have`/`let` flag (Lean core marks a `have` as non-dependent, the pinned exporter writes `false`; the kernel treats both alike). Only comparisons use this; replayed terms are as exported. -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun s => match s with
    | .mdata _ b => some (stripMData b)
    | .letE n t v b _ => some (.letE n (stripMData t) (stripMData v) (stripMData b) false)
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
  match env.toKernelEnv.find? n with
  | none => pure false
  | some ci => if stripMData ci.type == stripMData type then pure true else fail s!"{n} is in the environment with another type\n first difference: {firstDiff (stripMData ci.type) (stripMData type)}"

/-- a name that opens a namespace: `Fx.add_swap` makes `Fx` one (the kernel does not, `Lean.addDecl` does; without it `open Fx` is refused) -/
partial def isNamespaceName : Name → Bool
  | .str .anonymous _ => true
  | .str p _ => isNamespaceName p
  | _ => false

def registerPrefixes (env : Environment) (name : Name) : Environment :=
  match name with
  | .str _ s => if s.front == '_' then env else go env name
  | _ => env
where
  go (env : Environment) : Name → Environment
    | .str p _ => if isNamespaceName p then go (env.registerNamespace p) p else env
    | _ => env

def addDecl (env : Environment) (d : Declaration) : IO Environment :=
  -- no heartbeat limit (0), the default recursion depth: the kernel is the judge, not a timer
  match env.addDeclCore 0 512 d none with
  | .ok e => pure (d.getNames.foldl registerPrefixes e)
  | .error ex => do fail s!"the kernel refused a declaration: {← (ex.toMessageData {}).toString}"

def readInductive (t : Tables) (env : Environment) (v : Json) (st : Stats) : IO (Environment × Stats) := do
  let types ← jsonArr v "types"
  let ctors ← jsonArr v "ctors"
  let recs ← jsonArr v "recs"
  let mut ctorTable : Array (Name × Expr) := #[]
  for c in ctors do
    let cn ← getName t (← nat c "name")
    ctorTable := ctorTable.push (cn, fixedType t cn (← getExpr t (← nat c "type")))
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
    let tp := fixedType t n (← getExpr t (← nat ty "type"))
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
    match env.toKernelEnv.find? rn with
    | some ci => if stripMData ci.type != stripMData rt then fail s!"the recursor {rn} differs from the exported one"
    | none =>
      let added := env.constants.foldStage2 (fun acc n _ => if firstName.isPrefixOf n then acc.push n else acc) #[]
      fail s!"the recursor {rn} was not derived; added under {firstName}: {added}"
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

/-- the first name a declaration line declares: the name of an axiom, definition, theorem, opaque or quotient, or the first type of an inductive block. A block is one unit: its constructors and recursors are
derived with it, so a replay that keeps or leaves out a block decides on this name alone. -/
def firstName (t : Tables) (o : Json) : IO (Option Name) := do
  for k in ["axiom", "def", "thm", "opaque", "quot"] do
    if has o k then return some (← getName t (← nat (← obj o k) "name"))
  if has o "inductive" then
    let types ← jsonArr (← obj o "inductive") "types"
    if h : 0 < types.size then return some (← getName t (← nat types[0] "name"))
  return none

partial def loop (h : IO.FS.Handle) (t : Tables) (env : Environment) (st : Stats) (only : Option (Std.HashSet Name)) : IO (Environment × Stats) := do
  let line ← h.getLine
  if line.isEmpty then return (env, st)
  let line := line.trimAsciiEnd.copy
  if line.isEmpty then return (← loop h t env st only)
  let o ← match Json.parse line with
    | .ok j => pure j
    | .error e => fail s!"not JSON: {e}"
  if has o "meta" then
    let v ← obj (← obj (← obj o "meta") "format") "version"
    match v.getStr? with
    | .ok s => if !s.startsWith "3." then fail s!"export format {s}, this reads 3.x"
    | .error _ => fail "meta without a format version"
    loop h t env st only
  else if has o "in" then
    loop h (← readName t o) env st only
  else if has o "il" then
    loop h (← readLevel t o) env st only
  else if has o "ie" then
    loop h (← readExpr t o) env st only
  else
    let keep ← match only with
      | none => pure true
      | some names => pure ((← firstName t o).all names.contains)
    if !keep then
      loop h t env { st with filtered := st.filtered + 1 } only
    else
      let (env, st) ← readDecl t env o st
      loop h t env st only

/-- The pass of `loop` without the replay: the declaration lines are kept (each with the first name it declares) and everything else is read as `loop` reads it. A promotion in layers reads the export
once with this and replays each layer from what it kept (`replayDecls`), where one `tengai-replay` per layer reads and parses the whole export again for every layer. -/
partial def loadExport (h : IO.FS.Handle) (t : Tables) (decls : Array (Option Name × Json)) : IO (Tables × Array (Option Name × Json)) := do
  let line ← h.getLine
  if line.isEmpty then return (t, decls)
  let line := line.trimAsciiEnd.copy
  if line.isEmpty then return (← loadExport h t decls)
  let o ← match Json.parse line with
    | .ok j => pure j
    | .error e => fail s!"not JSON: {e}"
  if has o "meta" then
    let v ← obj (← obj (← obj o "meta") "format") "version"
    match v.getStr? with
    | .ok s => if !s.startsWith "3." then fail s!"export format {s}, this reads 3.x"
    | .error _ => fail "meta without a format version"
    loadExport h t decls
  else if has o "in" then
    loadExport h (← readName t o) decls
  else if has o "il" then
    loadExport h (← readLevel t o) decls
  else if has o "ie" then
    loadExport h (← readExpr t o) decls
  else
    loadExport h t (decls.push (← firstName t o, o))

/-- The declarations `loop` would replay, from what `loadExport` kept: the ones `only` names (all of them without `only`) go through the kernel, the others are counted as filtered. -/
def replayDecls (t : Tables) (env : Environment) (decls : Array (Option Name × Json)) (only : Option (Std.HashSet Name)) : IO (Environment × Stats) := do
  let mut env := env
  let mut st : Stats := {}
  for (first, o) in decls do
    let keep := match only with
      | none => true
      | some names => first.all names.contains
    if keep then
      let (e, s) ← readDecl t env o st
      env := e
      st := s
    else
      st := { st with filtered := st.filtered + 1 }
  pure (env, st)

/-- The parsed export as a file: what `loadExport` returns, written with `saveModuleData` (the image of an `.olean`) and read back mapped by `loadTables`, so that a layer's process does not parse a line of JSON.
Nothing in the file is a module; it borrows the format, which keeps the sharing of the expression DAG that a copy line by line would lose. The names go where a module keeps extra constant names, the rest are
entries under names of their own. -/
unsafe def saveTables (path : System.FilePath) (t : Tables) (decls : Array (Option Name × Json)) : IO Unit := do
  let data : ModuleData := {
    isModule := false, imports := #[], constNames := #[], constants := #[], extraConstNames := t.names,
    entries := #[(`levels, unsafeCast t.levels), (`exprs, unsafeCast t.exprs), (`decls, unsafeCast decls)] }
  saveModuleData path `TengaiTables data

/-- Read a table file back (`saveTables`): the arrays point into the mapped file, which is kept for the life of the process. A file that is not one is refused. -/
unsafe def loadTables (path : System.FilePath) : IO (Tables × Array (Option Name × Json)) := do
  let (data, _region) ← readModuleData path
  let entry (n : Name) : IO (Array EnvExtensionEntry) :=
    match data.entries.find? (·.1 == n) with
    | some (_, es) => pure es
    | none => fail s!"{path} is not a table file of tengai-replay (it has no {n})"
  if data.extraConstNames.isEmpty || data.extraConstNames[0]! != Name.anonymous then fail s!"{path} is not a table file of tengai-replay (its names do not start with the anonymous name)"
  pure ({ names := data.extraConstNames, levels := unsafeCast (← entry `levels), exprs := unsafeCast (← entry `exprs) }, unsafeCast (← entry `decls))

/-- The names a replay into `env` (Lean core alone) would add, found without replaying: a declaration whose name `env` already holds is left out, as `alreadyThere` leaves it out; an inductive block adds its
types, constructors and recursors; the quotient declaration adds its four constants. The kernel is not asked: this decides which names `tengai-extinfo` is asked about, and the replay still checks every declaration. -/
def addedNames (t : Tables) (env : Environment) (decls : Array (Option Name × Json)) : IO (Array Name) := do
  let mut out : Array Name := #[]
  for (first, o) in decls do
    let some n := first | continue
    if (env.toKernelEnv.find? n).isSome then continue
    if has o "inductive" then
      let v ← obj o "inductive"
      for k in ["types", "ctors", "recs"] do
        for x in ← jsonArr v k do
          out := out.push (← getName t (← nat x "name"))
    else if has o "quot" then
      out := out ++ #[``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
    else
      out := out.push n
  pure out

/-! ## Extension entries: what the kernel does not hold but elaboration needs

A replayed module holds kernel constants and nothing else. `tengai-extinfo` reads, in the environment the constants came from, what Lean keeps about them outside the kernel (reducibility, class and instance
registration, projection functions) as one JSON line per constant, and `--ext` puts that back. Instances are global by default (without them `#synth Field ℝ` finds nothing and a lemma cannot be applied to a
concrete goal); `--scoped-instances` registers them as scoped to the namespace of the module, for a library that wants them inactive until opened. Simp lemmas, notation and every other attribute are not carried. -/

def nameOfJson (j : Json) : IO Name := do
  let arr ← match j.getArr? with
    | .ok a => pure a
    | .error e => fail s!"a name is an array of components: {e}"
  let mut n := Name.anonymous
  for c in arr do
    match c with
    | Json.str s => n := Name.str n s
    | Json.num k => n := Name.num n k.mantissa.toNat
    | _ => fail "a name component is a string or a number"
  pure n

def nameToJson (n : Name) : Json :=
  Json.arr (n.components.toArray.map fun c => match c with
    | .str _ s => Json.str s
    | .num _ k => Json.num (JsonNumber.fromNat k)
    | _ => Json.null)

def reducibilityOfString (s : String) : IO ReducibilityStatus :=
  match s with
  | "reducible" => pure ReducibilityStatus.reducible
  | "semireducible" => pure ReducibilityStatus.semireducible
  | "irreducible" => pure ReducibilityStatus.irreducible
  | "implicitReducible" => pure ReducibilityStatus.implicitReducible
  | "instanceReducible" => pure ReducibilityStatus.instanceReducible
  | _ => fail s!"reducibility {s}"

structure ExtCounts where
  reducibility : Nat := 0
  projections : Nat := 0
  /-- structures and classes whose field information was registered (what `{ x := 1 }` and `{ p with x := 2 }` read) -/
  structures : Nat := 0
  classes : Nat := 0
  instances : Nat := 0
  /-- entries that could not be applied (the reason of the first ones goes to stderr): an entry that Lean refuses is counted, it does not stop a replay of a hundred thousand constants -/
  failed : Nat := 0
  deriving ToJson

open Meta in
/-- put the extension entries back: reducibility first (instance registration reads it), then projection info, classes, then instances. A refused entry is counted and its reason kept (the first 25). -/
def applyExt (rows : Array Json) (scopedInst : Bool) : MetaM (ExtCounts × Array String) := do
  let mut c : ExtCounts := {}
  let mut errors : Array String := #[]
  for r in rows do
    if let .ok st := r.getObjValAs? String "red" then
      let n ← nameOfJson (← obj r "n")
      try
        setReducibilityStatus n (← reducibilityOfString st)
        c := { c with reducibility := c.reducibility + 1 }
      catch ex =>
        c := { c with failed := c.failed + 1 }
        if errors.size < 25 then errors := errors.push s!"reducibility {n}: {← ex.toMessageData.toString}"
  for r in rows do
    if has r "proj" then
      let n ← nameOfJson (← obj r "n")
      let p ← obj r "proj"
      let ctor ← nameOfJson (← obj p "ctor")
      let np ← nat p "np"
      let i ← nat p "i"
      let fromClass ← bool p "cls"
      modifyEnv fun env => addProjectionFnInfo env n ctor np i fromClass
      c := { c with projections := c.projections + 1 }
  for r in rows do
    if has r "st" then
      let n ← nameOfJson (← obj r "n")
      let s ← obj r "st"
      try
        let mut fs : Array StructureFieldInfo := #[]
        for f in ← jsonArr s "fields" do
          let sub ← obj f "sub"
          -- a nested `←` is run before the whole statement, so the choice between a name and nothing is made here, as an action
          let subobject : Option Name ← if sub.isNull then pure none else some <$> nameOfJson sub
          fs := fs.push {
            fieldName := ← nameOfJson (← obj f "f")
            projFn := ← nameOfJson (← obj f "proj")
            subobject? := subobject
            binderInfo := ← binderInfo (← str f "bi") }
        let mut ps : Array StructureParentInfo := #[]
        for p in ← jsonArr s "parents" do
          ps := ps.push { structName := ← nameOfJson (← obj p "s"), subobject := ← bool p "sub", projFn := ← nameOfJson (← obj p "proj") }
        modifyEnv fun env => registerStructure env { structName := n, fields := fs }
        setStructureParents n ps
        c := { c with structures := c.structures + 1 }
      catch ex =>
        c := { c with failed := c.failed + 1 }
        if errors.size < 25 then errors := errors.push s!"structure {n}: {← ex.toMessageData.toString}"
  for r in rows do
    if has r "class" then
      let n ← nameOfJson (← obj r "n")
      match addClass (← getEnv) n with
      | .ok env =>
        setEnv env
        c := { c with classes := c.classes + 1 }
      | .error m =>
        c := { c with failed := c.failed + 1 }
        if errors.size < 25 then errors := errors.push s!"class {n}: {← m.toString}"
  for r in rows do
    if has r "inst" then
      let n ← nameOfJson (← obj r "n")
      let p ← obj r "inst"
      let prio ← nat p "prio"
      try
        addInstance n (if scopedInst then AttributeKind.scoped else AttributeKind.global) prio
        c := { c with instances := c.instances + 1 }
      catch ex =>
        c := { c with failed := c.failed + 1 }
        if errors.size < 25 then errors := errors.push s!"instance {n}: {← ex.toMessageData.toString}"
  pure (c, errors)

def usage : String := "usage: tengai-replay EXPORT.ndjson --module TengaiData.Foo --out DIR [--import MODULE]... [--only NAMES.jsonl] [--added ADDED.jsonl] [--ext EXT.jsonl [--scoped-instances]]\n       tengai-replay EXPORT.ndjson --save-tables TABLES\n       tengai-replay --tables TABLES --module TengaiData.Foo --out DIR [the options above]\n       tengai-replay (EXPORT.ndjson | --tables TABLES) --added-only ADDED.jsonl"

structure Opts where
  export_ : String := ""
  module : String := ""
  out : String := ""
  added : Option String := none
  ext : Option String := none
  scopedInst : Bool := false
  /-- modules the replay starts from besides Lean core: an earlier layer of the same promotion, found on LEAN_PATH -/
  imports : Array String := #[]
  /-- only the declarations whose first name is listed (one JSON array of name components a line) are added -/
  only : Option String := none
  /-- the parsed export as a file (`--save-tables` writes it, `--tables` replays from it instead of from the export): the parse of a large export is most of the time of a small layer -/
  saveTables : Option String := none
  tables : Option String := none
  /-- write the names a replay would add (`--added` writes the ones it did add) without replaying: from the export, or from `--tables` -/
  addedOnly : Option String := none

partial def parseArgs (o : Opts) : List String → Except String Opts
  | [] =>
    if o.addedOnly.isSome then
      if o.saveTables.isSome || !o.module.isEmpty || !o.out.isEmpty || !o.imports.isEmpty || o.only.isSome || o.added.isSome || o.ext.isSome || (o.export_.isEmpty && o.tables.isNone) || (!o.export_.isEmpty && o.tables.isSome) then
        .error "--added-only takes the export or --tables, and nothing else: it writes the names a replay would add"
      else .ok o
    else if o.saveTables.isSome then
      if o.export_.isEmpty || o.tables.isSome || !o.module.isEmpty || !o.out.isEmpty || !o.imports.isEmpty || o.only.isSome || o.added.isSome || o.ext.isSome then
        .error "--save-tables takes the export and nothing else: it parses the export and writes the table file"
      else .ok o
    else if o.tables.isSome then
      if !o.export_.isEmpty then .error "--tables replaces the export: give one of them"
      else if o.module.isEmpty || o.out.isEmpty then .error usage
      else .ok o
    else if o.export_.isEmpty || o.module.isEmpty || o.out.isEmpty then .error usage
    else .ok o
  | "--module" :: v :: r => parseArgs { o with module := v } r
  | "--out" :: v :: r => parseArgs { o with out := v } r
  | "--added" :: v :: r => parseArgs { o with added := some v } r
  | "--ext" :: v :: r => parseArgs { o with ext := some v } r
  | "--scoped-instances" :: r => parseArgs { o with scopedInst := true } r
  | "--import" :: v :: r => parseArgs { o with imports := o.imports.push v } r
  | "--only" :: v :: r => parseArgs { o with only := some v } r
  | "--save-tables" :: v :: r => parseArgs { o with saveTables := some v } r
  | "--tables" :: v :: r => parseArgs { o with tables := some v } r
  | "--added-only" :: v :: r => parseArgs { o with addedOnly := some v } r
  | x :: r => if o.export_.isEmpty && !x.startsWith "--" then parseArgs { o with export_ := x } r else .error s!"unexpected argument {x}"

/-- the lines of a JSON-lines file, parsed (blank lines skipped); `what` names the file in an error -/
def readJsonLines (f : String) (what : String) : IO (Array Json) := do
  let mut rows : Array Json := #[]
  for ln in (← IO.FS.lines f) do
    if ln.trimAscii.isEmpty then continue
    match Json.parse ln with
    | .ok j => rows := rows.push j
    | .error e => fail s!"{what} line is not JSON: {e}"
  pure rows

/-- the names of a `--only` file or of a layer of a plan: one JSON array of name components a line -/
def readNames (f : String) (what : String) : IO (Std.HashSet Name) := do
  let mut names : Std.HashSet Name := {}
  for j in (← readJsonLines f what) do
    names := names.insert (← nameOfJson j)
  pure names

/-- the binder names and annotations of `--ext` (its `bi` rows): they apply while the declarations are read, the kernel must see the types with the right annotations -/
def readFixes (rows : Array Json) : IO (Std.HashMap Name (Array (Name × BinderInfo))) := do
  let mut fixes : Std.HashMap Name (Array (Name × BinderInfo)) := {}
  for j in rows do
    if has j "bi" then
      let n ← nameOfJson (← obj j "n")
      let arr ← jsonArr j "bi"
      let mut fx : Array (Name × BinderInfo) := #[]
      for b in arr do
        let pair ← match b.getArr? with
          | .ok p => pure p
          | .error e => fail s!"bi: {e}"
        let bn ← nameOfJson pair[0]!
        let bi ← binderInfo (← match pair[1]!.getStr? with | .ok s => pure s | .error e => fail s!"bi: {e}")
        fx := fx.push (bn, bi)
      fixes := fixes.insert n fx
  pure fixes

/-- what a replay does once its declarations are in: the extension entries (the rows of `--ext`; for a layer, the rows of the constants it added: those of another layer are in that layer's module),
then the module is written and the statistics are printed as one JSON line. Shared by the one-module replay and each layer of `--layers`. -/
def finishModule (replayed : Environment) (st : Stats) (rows : Option (Array Json)) (ownOnly : Bool) (scopedInst : Bool) (module out : String) : IO Unit := do
  let mut counts : Option ExtCounts := none
  let mut cur := replayed
  if let some all := rows then
    let rows ← all.filterMapM fun j => do
      if ownOnly then
        match j.getObjVal? "n" with
        | .ok n => return if replayed.constants.map₂.contains (← nameOfJson n) then some j else none
        | .error _ => return some j
      else
        return some j
    let ((c, errs), cst) ← ((applyExt rows scopedInst).run' {}).toIO { fileName := "<replay>", fileMap := default } { env := cur }
    for e in errs do IO.eprintln s!"ext: {e}"
    counts := some c
    cur := cst.env
  let modName := module.toName
  let env := cur.setMainModule modName
  let rel := String.intercalate "/" (modName.components.map toString) ++ ".olean"
  let path : System.FilePath := (System.FilePath.mk out) / rel
  if let some p := path.parent then IO.FS.createDirAll p
  writeModule env path
  IO.println (Json.mkObj [("replay", toJson st), ("ext", match counts with | some c => toJson c | none => Json.null)]).compress

/-- the replay of one module (with `--import` and `--only` it is one layer of a promotion): `run` replays the declarations into the environment it is given, from the export as it is read or from a table file -/
def replayModule (opts : Opts) (rows : Option (Array Json)) (run : Environment → Option (Std.HashSet Name) → IO (Environment × Stats)) : IO UInt32 := do
  let env ← importModules (#[{ module := `Init }] ++ opts.imports.map fun m => { module := m.toName }) {} (loadExts := true)
  -- a layer of a promotion adds only the constants it was given; the others are in the layers it imports
  let only ← match opts.only with
    | none => pure none
    | some f => pure (some (← readNames f "--only"))
  let (replayed, st) ← run env only
  -- the names this replay added (not the ones Lean core already held): the input of `tengai-extinfo`
  if let some f := opts.added then
    let names := replayed.constants.foldStage2 (fun acc n _ => acc.push n) #[]
    IO.FS.writeFile f (String.join (names.toList.map fun n => (nameToJson n).compress ++ "\n"))
  finishModule replayed st rows only.isSome opts.scopedInst opts.module opts.out
  return 0

end TengaiReplay

open TengaiReplay in
unsafe def main (args : List String) : IO UInt32 := do
  match parseArgs {} args with
  | .error e =>
    IO.eprintln e
    return 2
  | .ok opts =>
    enableInitializersExecution
    initSearchPath (← findSysroot)
    -- the binder names and annotations of `--ext` apply while the declarations are read: the kernel must see the types with the right annotations
    let rows ← match opts.ext with
      | none => pure none
      | some f => pure (some (← readJsonLines f "ext"))
    let fixes ← match rows with
      | none => pure {}
      | some r => readFixes r
    if let some file := opts.addedOnly then
      let (t, decls) ← match opts.tables with
        | some f => loadTables f
        | none => loadExport (← IO.FS.Handle.mk opts.export_ IO.FS.Mode.read) {} #[]
      let env ← importModules #[{ module := `Init }] {} (loadExts := true)
      let names ← addedNames t env decls
      IO.FS.writeFile file (String.join (names.toList.map fun n => (nameToJson n).compress ++ "\n"))
      IO.println (Json.mkObj [("added_only", toJson names.size)]).compress
      return 0
    if let some file := opts.saveTables then
      -- parse the export once and keep the result: every layer's process then reads this file instead of the export
      let (t, decls) ← loadExport (← IO.FS.Handle.mk opts.export_ IO.FS.Mode.read) {} #[]
      saveTables file t decls
      IO.println (Json.mkObj [("tables", Json.mkObj [("names", toJson t.names.size), ("levels", toJson t.levels.size), ("exprs", toJson t.exprs.size), ("declarations", toJson decls.size)])]).compress
      return 0
    match opts.tables with
    | some file =>
      let (t, decls) ← loadTables file
      replayModule opts rows fun env only => replayDecls { t with fixes } env decls only
    | none =>
      let h ← IO.FS.Handle.mk opts.export_ IO.FS.Mode.read
      replayModule opts rows fun env only => loop h { fixes } env {} only
