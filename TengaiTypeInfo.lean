import Lean
open Lean

/-!
# tengai-typeinfo: the shape of the type of a declaration, in whatever environment imports it

`lake env tengai-typeinfo NAMES.jsonl Module...` prints one JSON line a name (names are arrays of components, as in `tengai-extinfo`): the size of the type (nodes without sharing), how many of them
are expression metadata, and the leading binders (name, annotation, head constant of the binder type). It answers one question: when the same statement has another hypothesis count or size class in two
environments (isnad reads both off the expression), WHICH part of the expression differs. It imports Lean; no library imports it.

`lake env tengai-typeinfo --hashes NAMES.jsonl Module...` prints, instead, a compact record a name: `kind` (what the declaration is: axiom, def, thm, opaque, quot, induct, ctor, rec), `thash`, a hash of the
whole type, `tsize`, the nodes of the type without its `mdata` (as a tree, no sharing), `vhash`, a hash of the value when the declaration has one (an opaque constant's included), and `lparams`, the
universe parameters. A hash is Lean's `Expr.hash` (32 bits) of the expression without its `mdata` nodes (`lean4export` leaves them out: they mean nothing to the kernel); it does not read binder names and
annotations either. Two environments that hold the same declaration give the same record, whatever produced them; a theorem that stands as an axiom of its type (a statements snapshot, docs/statements.md in
Tenro) differs in `kind` and has no `vhash`, and its `thash` is the theorem's. A record that differs is a difference, found without printing a type; a record that agrees makes a difference very unlikely
(two other types agree on a 32-bit hash and on the node count by chance with a probability of about 2^-32 and less), it does not prove there is none: the default mode prints the type for the names
where the claim matters.
-/

def nameOfJson (j : Json) : Except String Name := do
  let arr ← j.getArr?
  let mut n := Name.anonymous
  for c in arr do
    match c with
    | Json.str s => n := Name.str n s
    | Json.num k => n := Name.num n k.mantissa.toNat
    | _ => throw "a name component is a string or a number"
  pure n

/-- nodes of the term read as a tree (no sharing) and how many of them are `mdata` -/
partial def census (e : Expr) : Nat × Nat :=
  match e with
  | .app f a => let (x, m) := census f; let (y, n) := census a; (x + y + 1, m + n)
  | .lam _ t b _ => let (x, m) := census t; let (y, n) := census b; (x + y + 1, m + n)
  | .forallE _ t b _ => let (x, m) := census t; let (y, n) := census b; (x + y + 1, m + n)
  | .letE _ t v b _ => let (x, m) := census t; let (y, n) := census v; let (z, o) := census b; (x + y + z + 1, m + n + o)
  | .mdata _ b => let (x, m) := census b; (x + 1, m + 1)
  | .proj _ _ b => let (x, m) := census b; (x + 1, m)
  | _ => (1, 0)

def infoString : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

partial def binders (e : Expr) (acc : Array Json := #[]) : Array Json :=
  match e with
  | .forallE n t b i =>
    let head := match t.getAppFn.consumeMData with
      | .const c _ => c.toString
      | .bvar k => s!"#{k}"
      | .sort _ => "Sort"
      | .forallE .. => "Pi"
      | _ => "?"
    binders b (acc.push (Json.mkObj [("name", Json.str n.toString), ("info", Json.str (infoString i)), ("head", Json.str head)]))
  | .mdata _ b => binders b acc
  | _ => acc

/-- the expression without its `mdata` nodes -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun
    | .mdata _ b => some (stripMData b)
    | _ => none

/-- what a declaration is -/
def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- the record of `--hashes` -/
def hashRecord (j : Json) (ci : ConstantInfo) : Json :=
  let base : List (String × Json) :=
    [("n", j), ("kind", Json.str (kindOf ci)), ("thash", toJson (stripMData ci.type).hash.toNat), ("tsize", toJson (let (s, m) := census ci.type; s - m)),
     ("lparams", Json.arr (ci.levelParams.toArray.map fun p => Json.str p.toString))]
  match ci.value? (allowOpaque := true) with
  | some v => Json.mkObj (base ++ [("vhash", toJson (stripMData v).hash.toNat)])
  | none => Json.mkObj base

unsafe def run (hashes : Bool) (file : String) (mods : List String) : IO UInt32 := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules (mods.toArray.map fun m => { module := m.toName }) {} (loadExts := true)
  let h ← IO.FS.Handle.mk file IO.FS.Mode.read
  repeat
    let line ← h.getLine
    if line.isEmpty then break
    if line.trimAscii.isEmpty then continue
    let j ← match Json.parse line with
      | .ok j => pure j
      | .error e => throw (IO.userError s!"not JSON: {e}")
    let n ← match nameOfJson j with
      | .ok n => pure n
      | .error e => throw (IO.userError e)
    match env.find? n with
    | none => IO.println (Json.mkObj [("n", j), ("missing", Json.bool true)]).compress
    | some ci =>
      if hashes then
        IO.println (hashRecord j ci).compress
      else
        let (size, mdata) := census ci.type
        IO.println (Json.mkObj [("n", j), ("size", toJson size), ("mdata", toJson mdata), ("binders", Json.arr (binders ci.type)), ("type", Json.str ((toString ci.type).take 1500).copy)]).compress
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | "--hashes" :: file :: mods@(_ :: _) => run true file mods
  | file :: mods@(_ :: _) => if file == "--hashes" then usage else run false file mods
  | _ => usage
where
  usage : IO UInt32 := do
    IO.eprintln "usage: lake env tengai-typeinfo [--hashes] NAMES.jsonl Module..."
    return 2
