import Lean
open Lean

/-!
# tengai-typeinfo: the shape of the type of a declaration, in whatever environment imports it

`lake env tengai-typeinfo NAMES.jsonl Module...` prints one JSON line a name (names are arrays of components, as in `tengai-extinfo`): the size of the type (nodes without sharing), how many of them
are expression metadata, and the leading binders (name, annotation, head constant of the binder type). It answers one question: when the same statement has another hypothesis count or size class in two
environments (isnad reads both off the expression), WHICH part of the expression differs. It imports Lean; no library imports it.
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

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | file :: mods@(_ :: _) =>
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
        let (size, mdata) := census ci.type
        IO.println (Json.mkObj [("n", j), ("size", toJson size), ("mdata", toJson mdata), ("binders", Json.arr (binders ci.type)), ("type", Json.str ((toString ci.type).take 1500))]).compress
    return 0
  | _ =>
    IO.eprintln "usage: lake env tengai-typeinfo NAMES.jsonl Module..."
    return 2
