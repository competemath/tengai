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

/-- The terms of a parsed export (`--save-tables`) as RECORDS, not as objects. A term as an object costs about 250 bytes in the table parse (the object, its slot, the entry the compactor of `saveModuleData` keeps for it
and its place in the output buffer): the 62 million terms of the whole tree peaked at 15.4 GB on a 16 GB runner. A record is 5 to about 20 bytes (`recs`, found by `offs`: 4 bytes a term), and a layer's process builds
into `Expr`s only the terms its own declarations reach (`matExpr`). Layout of a record, every number 4 bytes little endian (`u32`): 0 bvar (index) · 1 sort (level) · 2 const (name, k, k levels) ·
3 app (fn, arg) · 4 lam and 5 forallE (binder byte, name, type, body) · 6 letE (nondep byte, name, type, value, body) · 7 proj (type name, index, struct) · 8 and 9 the natural and the string literal (a place in `nats`
and in `strs`: a number or a string does not fit a record) · 10 the term of an expression metadata node (its subterm: the export's `mdata` is dropped). A subterm has a smaller id than its term. -/
structure CompactExprs where
  recs : ByteArray := .empty
  offs : ByteArray := .empty
  nats : Array Nat := #[]
  strs : Array String := #[]

def CompactExprs.size (c : CompactExprs) : Nat := c.offs.size / 4

structure Tables where
  names : Array Name := #[Name.anonymous]
  levels : Array Level := #[Level.zero]
  exprs : Array Expr := #[]
  /-- the terms as records, when the tables were parsed with `loadExport` (then `exprs` is empty): `memo` holds the terms built so far, by id, so that a term is one object however often it is reached (as `exprs` is) -/
  compact : Option CompactExprs := none
  memo : Option (IO.Ref (Std.HashMap Nat Expr)) := none
  /-- binder names and annotations to restore on the leading telescope of a constant's type (from `--ext`) -/
  fixes : Std.HashMap Name (Array (Name × BinderInfo)) := {}
  /-- `--stub-refused`: a definition, opaque constant or theorem the kernel refuses is added as an axiom of its type, and counted (`Stats.refused`), instead of stopping the replay -/
  stubRefused : Bool := false

structure Stats where
  added : Nat := 0
  skipped : Nat := 0
  inductives : Nat := 0
  /-- declarations left out because `--only` did not name them (they belong to another module of a layered promotion) -/
  filtered : Nat := 0
  /-- the declarations `--stub-refused` added as axioms because the kernel refused them (a definition whose value needs a proof that a statements export left out) -/
  refused : Array String := #[]
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

/-- `n` as 4 bytes, little endian, after `b` (the caller has checked that it fits) -/
def pushU32 (b : ByteArray) (n : Nat) : ByteArray :=
  let x := n.toUInt32
  (((b.push x.toUInt8).push (x >>> 8).toUInt8).push (x >>> 16).toUInt8).push (x >>> 24).toUInt8

def getU32 (b : ByteArray) (p : Nat) : Nat :=
  (b.get! p).toNat ||| ((b.get! (p + 1)).toNat <<< 8) ||| ((b.get! (p + 2)).toNat <<< 16) ||| ((b.get! (p + 3)).toNat <<< 24)

def binderByte : BinderInfo → UInt8
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

def binderOfByte : UInt8 → BinderInfo
  | 1 => .implicit
  | 2 => .strictImplicit
  | 3 => .instImplicit
  | _ => .default

/-- where the record of term `i` starts -/
def CompactExprs.start (c : CompactExprs) (i : Nat) : Nat := getU32 c.offs (4 * i)

/-- the subterms of term `i`: the ones that must be built before it -/
def CompactExprs.kids (c : CompactExprs) (i : Nat) : Array Nat :=
  let r := c.recs
  let p := c.start i
  match (r.get! p).toNat with
  | 3 => #[getU32 r (p + 1), getU32 r (p + 5)]
  | 4 | 5 => #[getU32 r (p + 6), getU32 r (p + 10)]
  | 6 => #[getU32 r (p + 6), getU32 r (p + 10), getU32 r (p + 14)]
  | 7 => #[getU32 r (p + 9)]
  | 10 => #[getU32 r (p + 1)]
  | _ => #[]

/-- term `i` from its record, its subterms taken from `memo` (they must be in it) -/
def CompactExprs.build (c : CompactExprs) (t : Tables) (memo : Std.HashMap Nat Expr) (i : Nat) : Except String Expr := do
  let r := c.recs
  let p := c.start i
  let u (o : Nat) : Nat := getU32 r (p + o)
  let nm (o : Nat) : Except String Name :=
    match t.names[u o]? with
    | some n => pure n
    | none => throw s!"name {u o} is not defined yet"
  let lv (l : Nat) : Except String Level :=
    match t.levels[l]? with
    | some v => pure v
    | none => throw s!"level {l} is not defined yet"
  let sub (o : Nat) : Except String Expr :=
    match memo[u o]? with
    | some e => pure e
    | none => throw s!"term {u o} was not built before term {i}"
  match (r.get! p).toNat with
  | 0 => pure (Expr.bvar (u 1))
  | 1 => pure (Expr.sort (← lv (u 1)))
  | 2 =>
    let mut ls : List Level := []
    for j in [0:u 5] do
      ls := (← lv (getU32 r (p + 9 + 4 * j))) :: ls
    pure (Expr.const (← nm 1) ls.reverse)
  | 3 => pure (Expr.app (← sub 1) (← sub 5))
  | 4 => pure (Expr.lam (← nm 2) (← sub 6) (← sub 10) (binderOfByte (r.get! (p + 1))))
  | 5 => pure (Expr.forallE (← nm 2) (← sub 6) (← sub 10) (binderOfByte (r.get! (p + 1))))
  | 6 => pure (Expr.letE (← nm 2) (← sub 6) (← sub 10) (← sub 14) (r.get! (p + 1) != 0))
  | 7 => pure (Expr.proj (← nm 1) (u 5) (← sub 9))
  | 8 =>
    match c.nats[u 1]? with
    | some n => pure (Expr.lit (Literal.natVal n))
    | none => throw s!"term {i}: natural literal {u 1} is not in the tables"
  | 9 =>
    match c.strs[u 1]? with
    | some s => pure (Expr.lit (Literal.strVal s))
    | none => throw s!"term {i}: string literal {u 1} is not in the tables"
  | 10 => sub 1
  | tag => throw s!"term {i}: unknown record {tag}"

/-- Term `root` of compact tables, and `memo` with every term built on the way. Iterative, with an explicit stack: a subterm has a smaller id than its term, so a term is built when its subterms are, and a deep
term is not a deep recursion. The term is the one `readExpr` builds from the same export, with the same sharing (one object per id): a module written from either is the same file. -/
def matExpr (c : CompactExprs) (t : Tables) (memo : Std.HashMap Nat Expr) (root : Nat) : Except String (Expr × Std.HashMap Nat Expr) := Id.run do
  if let some e := memo[root]? then return .ok (e, memo)
  if root >= c.size then return .error s!"term {root} is not defined yet"
  let mut memo := memo
  -- an entry of the stack is a term id times 2, plus 1 once its subterms have been put above it: it is built when it comes up again
  let mut stack : Array Nat := #[root * 2]
  while !stack.isEmpty do
    let entry := stack.back!
    stack := stack.pop
    let i := entry / 2
    if memo.contains i then continue
    if entry % 2 == 0 then
      stack := stack.push (i * 2 + 1)
      for k in c.kids i do
        if !memo.contains k then stack := stack.push (k * 2)
    else
      match c.build t memo i with
      | .ok e => memo := memo.insert i e
      | .error msg => return .error msg
  match memo[root]? with
  | some e => return .ok (e, memo)
  | none => return .error s!"term {root} was not built"

def getExpr (t : Tables) (i : Nat) : IO Expr := do
  match t.compact, t.memo with
  | some c, some ref =>
    -- the map leaves the reference while it is extended: a map that something else holds is copied at its first insertion
    let memo ← ref.swap {}
    match matExpr c t memo i with
    | .ok (e, memo) => ref.set memo; pure e
    | .error msg => fail msg
  | _, _ =>
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

/-- `readExpr` for compact tables: the line becomes a record and nothing is built. What `readExpr` asks of a line it asks here (the subterms, the names and the levels it names are defined already), and a number that does
not fit 4 bytes is refused. `c` is taken apart and put together again so that its arrays are updated in place. -/
def readExprCompact (t : Tables) (c : CompactExprs) (o : Json) : IO CompactExprs := do
  let idx ← nat o "ie"
  if idx != c.size then fail s!"term {idx} out of order"
  let big : Nat := 4294967296
  let num (n : Nat) (what : String) : IO Nat := if n < big then pure n else fail s!"term {idx}: {what} {n} does not fit 4 bytes"
  let sub (v : Json) (k : String) : IO Nat := do
    let i ← nat v k
    if i < idx then pure i else fail s!"term {i} is not defined yet"
  let nm (v : Json) (k : String) : IO Nat := do
    let i ← nat v k
    if i < t.names.size then pure i else fail s!"name {i} is not defined yet"
  let lv (i : Nat) : IO Nat := if i < t.levels.size then pure i else fail s!"level {i} is not defined yet"
  match c with
  | ⟨recs, offs, nats, strs⟩ =>
    if recs.size + 64 >= big then fail "the records of the terms of this export are over 4 GiB"
    let offs := pushU32 offs recs.size
    if has o "bvar" then
      pure ⟨pushU32 (recs.push 0) (← num (← nat o "bvar") "bound variable"), offs, nats, strs⟩
    else if has o "sort" then
      pure ⟨pushU32 (recs.push 1) (← lv (← nat o "sort")), offs, nats, strs⟩
    else if has o "const" then
      let v ← obj o "const"
      let us ← natArr v "us"
      let mut r := pushU32 (pushU32 (recs.push 2) (← nm v "name")) us.size
      for u in us do r := pushU32 r (← lv u)
      pure ⟨r, offs, nats, strs⟩
    else if has o "app" then
      let v ← obj o "app"
      pure ⟨pushU32 (pushU32 (recs.push 3) (← sub v "fn")) (← sub v "arg"), offs, nats, strs⟩
    else if has o "lam" || has o "forallE" then
      let lam := has o "lam"
      let v ← obj o (if lam then "lam" else "forallE")
      let bi ← binderInfo (← str v "binderInfo")
      let r := (recs.push (if lam then 4 else 5)).push (binderByte bi)
      pure ⟨pushU32 (pushU32 (pushU32 r (← nm v "name")) (← sub v "type")) (← sub v "body"), offs, nats, strs⟩
    else if has o "letE" then
      let v ← obj o "letE"
      let nd ← bool v "nondep"
      let r := (recs.push 6).push (if nd then 1 else 0)
      pure ⟨pushU32 (pushU32 (pushU32 (pushU32 r (← nm v "name")) (← sub v "type")) (← sub v "value")) (← sub v "body"), offs, nats, strs⟩
    else if has o "proj" then
      let v ← obj o "proj"
      pure ⟨pushU32 (pushU32 (pushU32 (recs.push 7) (← nm v "typeName")) (← num (← nat v "idx") "projection index")) (← sub v "struct"), offs, nats, strs⟩
    else if has o "natVal" then
      pure ⟨pushU32 (recs.push 8) nats.size, offs, nats.push (← str o "natVal").toNat!, strs⟩
    else if has o "strVal" then
      pure ⟨pushU32 (recs.push 9) strs.size, offs, nats, strs.push (← str o "strVal")⟩
    else if has o "mdata" then
      let v ← obj o "mdata"
      pure ⟨pushU32 (recs.push 10) (← sub v "expr"), offs, nats, strs⟩
    else
      fail s!"term {idx}: unknown kind"

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

/-- `addDecl`; with `--stub-refused` a declaration the kernel refuses is added as an axiom of its type instead (and counted). The type is what a search needs of a definition; what is lost is its computation. -/
def addOrStub (t : Tables) (env : Environment) (st : Stats) (cv : ConstantVal) (isUnsafe : Bool) (d : Declaration) : IO (Environment × Stats) := do
  try
    pure (← addDecl env d, st)
  catch e =>
    if !t.stubRefused then throw e
    let env ← addDecl env (Declaration.axiomDecl { toConstantVal := cv, isUnsafe := isUnsafe })
    pure (env, { st with refused := st.refused.push cv.name.toString })

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
    let (env, st) ← addOrStub t env st cv (safety == DefinitionSafety.unsafe) (Declaration.defnDecl { toConstantVal := cv, value := value, hints := hints, safety := safety, all := all })
    pure (env, { st with added := st.added + 1 })
  else if has o "thm" then
    let v ← obj o "thm"
    let cv ← constantVal t v
    if (← alreadyThere env cv.name cv.type) then return (env, { st with skipped := st.skipped + 1 })
    let value ← getExpr t (← nat v "value")
    let all ← allNames t v
    let (env, st) ← addOrStub t env st cv false (Declaration.thmDecl { toConstantVal := cv, value := value, all := all })
    pure (env, { st with added := st.added + 1 })
  else if has o "opaque" then
    let v ← obj o "opaque"
    let cv ← constantVal t v
    if (← alreadyThere env cv.name cv.type) then return (env, { st with skipped := st.skipped + 1 })
    let value ← getExpr t (← nat v "value")
    let u ← bool v "isUnsafe"
    let all ← allNames t v
    let (env, st) ← addOrStub t env st cv u (Declaration.opaqueDecl { toConstantVal := cv, value := value, isUnsafe := u, all := all })
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

/-- a declaration line kept as text (`loadExport`), parsed when a layer replays it -/
def parseLine (line : String) : IO Json :=
  match Json.parse line with
  | .ok j => pure j
  | .error e => fail s!"not JSON: {e}"

/-- The pass of `loop` without the replay: the declaration lines are kept as TEXT (each with the first name it declares: a parsed line is some forty objects, the line is one) and everything else is read as `loop`
reads it, except the terms: those are kept as records (`readExprCompact`), in `c`, and `t.exprs` stays empty. A promotion in layers reads the export once with this and replays each layer from what it kept (`replayDecls`), where one `tengai-replay` per layer
reads and parses the whole export again for every layer. -/
partial def loadExport (h : IO.FS.Handle) (t : Tables) (c : CompactExprs) (decls : Array (Option Name × String)) : IO (Tables × CompactExprs × Array (Option Name × String)) := do
  let line ← h.getLine
  if line.isEmpty then return (t, c, decls)
  let line := line.trimAsciiEnd.copy
  if line.isEmpty then return (← loadExport h t c decls)
  let o ← match Json.parse line with
    | .ok j => pure j
    | .error e => fail s!"not JSON: {e}"
  if has o "meta" then
    let v ← obj (← obj (← obj o "meta") "format") "version"
    match v.getStr? with
    | .ok s => if !s.startsWith "3." then fail s!"export format {s}, this reads 3.x"
    | .error _ => fail "meta without a format version"
    loadExport h t c decls
  else if has o "in" then
    loadExport h (← readName t o) c decls
  else if has o "il" then
    loadExport h (← readLevel t o) c decls
  else if has o "ie" then
    loadExport h t (← readExprCompact t c o) decls
  else
    loadExport h t c (decls.push (← firstName t o, line))

/-- The declarations `loop` would replay, from what `loadExport` kept: the ones `only` names (all of them without `only`) go through the kernel, the others are counted as filtered. -/
def replayDecls (t : Tables) (env : Environment) (decls : Array (Option Name × String)) (only : Option (Std.HashSet Name)) : IO (Environment × Stats) := do
  let mut env := env
  let mut st : Stats := {}
  for (first, line) in decls do
    let keep := match only with
      | none => true
      | some names => first.all names.contains
    if keep then
      let (e, s) ← readDecl t env (← parseLine line) st
      env := e
      st := s
    else
      st := { st with filtered := st.filtered + 1 }
  pure (env, st)

/-- The parsed export as a file: what `loadExport` returns, written with `saveModuleData` (the image of an `.olean`) and read back mapped by `loadTables`, so that a layer's process does not parse a line of JSON.
Nothing in the file is a module; it borrows the format. The names go where a module keeps extra constant names, the rest are entries under names of their own: the levels, the declarations, and the terms
as records (`CompactExprs`: two byte arrays and the literals), which the layer's process builds only as far as its declarations reach. The declarations are their text lines: a layer parses the ones it replays. -/
unsafe def saveTables (path : System.FilePath) (t : Tables) (c : CompactExprs) (decls : Array (Option Name × String)) : IO Unit := do
  let data : ModuleData := {
    isModule := false, imports := #[], constNames := #[], constants := #[], extraConstNames := t.names,
    entries := #[(`levels, unsafeCast t.levels), (`recs, unsafeCast c.recs), (`offs, unsafeCast c.offs), (`nats, unsafeCast c.nats), (`strs, unsafeCast c.strs),
      (`decls, unsafeCast decls)] }
  saveModuleData path `TengaiTables data

/-- Read a table file back (`saveTables`): the arrays point into the mapped file, which is kept for the life of the process. A file that is not one is refused. -/
unsafe def loadTables (path : System.FilePath) : IO (Tables × Array (Option Name × String)) := do
  let (data, _region) ← readModuleData path
  let entry (n : Name) : IO (Array EnvExtensionEntry) :=
    match data.entries.find? (·.1 == n) with
    | some (_, es) => pure es
    | none => fail s!"{path} is not a table file of tengai-replay (it has no {n})"
  if data.extraConstNames.isEmpty || data.extraConstNames[0]! != Name.anonymous then fail s!"{path} is not a table file of tengai-replay (its names do not start with the anonymous name)"
  let memo ← IO.mkRef ({} : Std.HashMap Nat Expr)
  let c : CompactExprs := { recs := unsafeCast (← entry `recs), offs := unsafeCast (← entry `offs), nats := unsafeCast (← entry `nats), strs := unsafeCast (← entry `strs) }
  if c.offs.size % 4 != 0 then fail s!"{path} is not a table file of tengai-replay (its term offsets are not a whole number of 4 bytes)"
  pure ({ names := data.extraConstNames, levels := unsafeCast (← entry `levels), compact := some c, memo := some memo }, unsafeCast (← entry `decls))

/-- The names a replay into `env` (Lean core alone) would add, found without replaying: a declaration whose name `env` already holds is left out, as `alreadyThere` leaves it out; an inductive block adds its
types, constructors and recursors; the quotient declaration adds its four constants. The kernel is not asked: this decides which names `tengai-extinfo` is asked about, and the replay still checks every declaration. -/
def addedNames (t : Tables) (env : Environment) (decls : Array (Option Name × String)) : IO (Array Name) := do
  let mut out : Array Name := #[]
  for (first, line) in decls do
    let some n := first | continue
    if (env.toKernelEnv.find? n).isSome then continue
    let o ← parseLine line
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
concrete goal); `--scoped-instances` registers them as scoped to the namespace of the module, for a library that wants them inactive until opened. The instances that are SCOPED in the source (`sinst` rows) are
registered scoped in the namespaces the source says, whatever that option is: they stay inactive until the namespace is opened, as they are in Tengoku. Simp lemmas, notation and every other attribute are not carried. -/

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

/-- a key of the discrimination-tree path of an instance, from the JSON `tengai-extinfo` wrote (the tags are in its header) -/
def keyOfJson (j : Json) : IO Meta.DiscrTree.Key := do
  let a ← match j.getArr? with
    | .ok a => pure a
    | .error e => fail s!"a key is an array: {e}"
  let tag ← match a[0]? with
    | some (Json.str s) => pure s
    | _ => fail "a key starts with its tag"
  let natAt (i : Nat) : IO Nat :=
    match a[i]? with
    | some v => match v.getNat? with
      | .ok n => pure n
      | .error e => fail s!"key {tag}: {e}"
    | none => fail s!"key {tag}: a number is missing"
  let nameAt (i : Nat) : IO Name :=
    match a[i]? with
    | some v => nameOfJson v
    | none => fail s!"key {tag}: a name is missing"
  let strAt (i : Nat) : IO String :=
    match a[i]? with
    | some (Json.str s) => pure s
    | _ => fail s!"key {tag}: a string is missing"
  match tag with
  | "c" => pure (.const (← nameAt 1) (← natAt 2))
  | "n" => pure (.lit (.natVal (← strAt 1).toNat!))
  | "s" => pure (.lit (.strVal (← strAt 1)))
  | "*" => pure .star
  | "o" => pure .other
  | "a" => pure .arrow
  | "p" => pure (.proj (← nameAt 1) (← natAt 2) (← natAt 3))
  | _ => fail s!"a key of kind {tag}"

structure ExtCounts where
  reducibility : Nat := 0
  projections : Nat := 0
  /-- structures and classes whose field information was registered (what `{ x := 1 }` and `{ p with x := 2 }` read) -/
  structures : Nat := 0
  classes : Nat := 0
  instances : Nat := 0
  /-- scoped registrations of instances (one for each namespace an instance is scoped in) -/
  scopedInstances : Nat := 0
  /-- instance entries added as the source holds them (its keys and synthesis order from the row), the others were computed by `addInstance` from the type -/
  carriedInstances : Nat := 0
  /-- entries that could not be applied (the reason of the first ones goes to stderr): an entry that Lean refuses is counted, it does not stop a replay of a hundred thousand constants -/
  failed : Nat := 0
  deriving ToJson

open Meta in
/-- The entry of instance `n` as its row holds it, or `none` for a row without keys (an older file). The value is the constant with its own level parameters, read from the KERNEL: Lean's lookups cannot see a
private constant whose user-facing name another private constant of the environment has (`Environment.addDeclCore` keeps the new constants in a registry by that name, and the second one is not found), and an entry
that is added as it is needs no lookup of its own. -/
def instanceEntryOf (n : Name) (p : Json) (prio : Nat) (kind : AttributeKind) : MetaM (Option InstanceEntry) := do
  if !has p "keys" then return none
  let mut keys : Array InstanceKey := #[]
  for j in ← jsonArr p "keys" do keys := keys.push (← keyOfJson j)
  let synth ← natArr p "synth"
  let some ci := (← getEnv).toKernelEnv.find? n | throwError "Unknown constant `{n}`"
  return some { keys, val := mkConst n (ci.levelParams.map mkLevelParam), priority := prio, globalName? := some n, synthOrder := synth, attrKind := kind }

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
        let kind := if scopedInst then AttributeKind.scoped else AttributeKind.global
        match ← instanceEntryOf n p prio kind with
        | some e =>
          modifyEnv fun env => instanceExtension.addCore env e kind Name.anonymous
          c := { c with instances := c.instances + 1, carriedInstances := c.carriedInstances + 1 }
        | none =>
          addInstance n kind prio
          c := { c with instances := c.instances + 1 }
      catch ex =>
        c := { c with failed := c.failed + 1 }
        if errors.size < 25 then errors := errors.push s!"instance {n}: {← ex.toMessageData.toString}"
  -- the scoped instances, each in the namespace it is scoped in (`addInstance` registers a scoped entry in the current namespace)
  for r in rows do
    if has r "sinst" then
      let n ← nameOfJson (← obj r "n")
      for e in ← jsonArr r "sinst" do
        let ns ← nameOfJson (← obj e "ns")
        let prio ← nat e "prio"
        try
          match ← instanceEntryOf n e prio AttributeKind.scoped with
          | some en =>
            modifyEnv fun env => instanceExtension.addCore env en AttributeKind.scoped ns
            c := { c with scopedInstances := c.scopedInstances + 1, carriedInstances := c.carriedInstances + 1 }
          | none =>
            withTheReader Core.Context (fun ctx => { ctx with currNamespace := ns }) (addInstance n AttributeKind.scoped prio)
            c := { c with scopedInstances := c.scopedInstances + 1 }
        catch ex =>
          c := { c with failed := c.failed + 1 }
          if errors.size < 25 then errors := errors.push s!"scoped instance {n} in {ns}: {← ex.toMessageData.toString}"
  pure (c, errors)

def usage : String := "usage: tengai-replay EXPORT.ndjson --module TengaiData.Foo --out DIR [--import MODULE]... [--only NAMES.jsonl] [--added ADDED.jsonl] [--ext EXT.jsonl [--scoped-instances]] [--stub-refused]\n       tengai-replay EXPORT.ndjson --save-tables TABLES\n       tengai-replay --tables TABLES --module TengaiData.Foo --out DIR [the options above]\n       tengai-replay (EXPORT.ndjson | --tables TABLES) --added-only ADDED.jsonl"

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
  /-- a declaration the kernel refuses is added as an axiom of its type and counted, instead of stopping the replay: for the replay of a statements export (`lean4export --statements`), where a definition can need a proof that was left out -/
  stubRefused : Bool := false

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
  | "--stub-refused" :: r => parseArgs { o with stubRefused := true } r
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

/-- The recursors the kernel generated carry the binder names it chose, and it chooses the index binders of a family by unfolding the declared type of the family: `inductive Foo : ObjectProperty C` has the binder of the
arrow of `C → Prop` in the definition `ObjectProperty`, as the export has it, and lean4export shares terms that differ only in binder names and keeps the first it saw. The recursor is not a declaration the replay reads
(the kernel makes it), so the names of the rows (`bi`, the leading binders of the recursor, which `tengai-extinfo` reads in the source) cannot be put back before the kernel sees it. They are put back in the
constants that are written: binder names and annotations belong to no judgement of the kernel and to no hash (a type is hashed up to them), so the recursor is the same constant with the source's names. -/
def fixRecursors (fixes : Std.HashMap Name (Array (Name × BinderInfo))) (cs : Array ConstantInfo) : Array ConstantInfo :=
  if fixes.isEmpty then cs else
  cs.map fun
    | .recInfo v =>
      match fixes[v.name]? with
      | some fx => .recInfo { v with type := fixTelescope v.type fx }
      | none => .recInfo v
    | c => c

/-- what a replay does once its declarations are in: the extension entries (the rows of `--ext`; for a layer, the rows of the constants it added: those of another layer are in that layer's module),
then the module is written and the statistics are printed as one JSON line. Shared by the one-module replay and each layer of `--layers`. -/
def finishModule (replayed : Environment) (st : Stats) (rows : Option (Array Json)) (ownOnly : Bool) (scopedInst : Bool) (module out : String) : IO Unit := do
  let mut counts : Option ExtCounts := none
  let mut cur := replayed
  let mut fixes : Std.HashMap Name (Array (Name × BinderInfo)) := {}
  if let some all := rows then
    let rows ← all.filterMapM fun j => do
      if ownOnly then
        match j.getObjVal? "n" with
        | .ok n => return if replayed.constants.map₂.contains (← nameOfJson n) then some j else none
        | .error _ => return some j
      else
        return some j
    fixes ← readFixes rows
    let ((c, errs), cst) ← ((applyExt rows scopedInst).run' {}).toIO { fileName := "<replay>", fileMap := default } { env := cur }
    for e in errs do IO.eprintln s!"ext: {e}"
    counts := some c
    cur := cst.env
  let modName := module.toName
  let env := cur.setMainModule modName
  let rel := String.intercalate "/" (modName.components.map toString) ++ ".olean"
  let path : System.FilePath := (System.FilePath.mk out) / rel
  if let some p := path.parent then IO.FS.createDirAll p
  if fixes.isEmpty || env.header.isModule then
    writeModule env path
  else  -- what `writeModule` does for a module that is not of the module system, with the binders of the recursors put back
    let data ← mkModuleData env
    saveModuleData path env.mainModule { data with constants := fixRecursors fixes data.constants }
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
        | none => do
          let (t, _, decls) ← loadExport (← IO.FS.Handle.mk opts.export_ IO.FS.Mode.read) {} {} #[]
          pure (t, decls)
      let env ← importModules #[{ module := `Init }] {} (loadExts := true)
      let names ← addedNames t env decls
      IO.FS.writeFile file (String.join (names.toList.map fun n => (nameToJson n).compress ++ "\n"))
      IO.println (Json.mkObj [("added_only", toJson names.size)]).compress
      return 0
    if let some file := opts.saveTables then
      -- parse the export once and keep the result: every layer's process then reads this file instead of the export
      let (t, c, decls) ← loadExport (← IO.FS.Handle.mk opts.export_ IO.FS.Mode.read) {} {} #[]
      saveTables file t c decls
      IO.println (Json.mkObj [("tables", Json.mkObj [("names", toJson t.names.size), ("levels", toJson t.levels.size), ("exprs", toJson c.size), ("record_bytes", toJson c.recs.size),
        ("declarations", toJson decls.size)])]).compress
      return 0
    match opts.tables with
    | some file =>
      let (t, decls) ← loadTables file
      replayModule opts rows fun env only => replayDecls { t with fixes, stubRefused := opts.stubRefused } env decls only
    | none =>
      let h ← IO.FS.Handle.mk opts.export_ IO.FS.Mode.read
      replayModule opts rows fun env only => loop h { fixes, stubRefused := opts.stubRefused } env {} only
