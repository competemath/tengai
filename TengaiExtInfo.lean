import Lean
open Lean

/-!
# tengai-extinfo: what Lean keeps about a constant outside the kernel

`lake env tengai-extinfo ADDED.jsonl Module...` (run where the modules are built, e.g. in Tengoku's Lake project) reads the names a replay added (`tengai-replay --added`, one JSON array of name components a line)
and prints one JSON line for every one of them that has something to carry:

  {"n": [...], "red": "reducible"}                      reducibility other than semireducible
  {"n": [...], "proj": {"ctor": [...], "np": 2, "i": 0, "cls": true}}      a projection function
  {"n": [...], "class": true}                           a class
  {"n": [...], "st": {"fields": [{"f": [...], "proj": [...], "sub": [...]|null, "bi": "default"}, ...], "parents": [{"s": [...], "sub": true, "proj": [...]}, ...]}}
                                                        a structure (or class): its fields in constructor order and the parents of its `extends` clause, which structure instance notation (`{ x := 1 }`, `{ p with x := 2 }`) and field access through a parent read
  {"n": [...], "inst": {"prio": 1000, "kind": "global"}}   an instance (local ones are not carried)
  {"n": [...], "sinst": [{"ns": [...], "prio": 1000}, ...]}   the namespaces it is a SCOPED instance in (active only where one of them is open), sorted: a constant can be a global instance and a scoped one
                                                        in several namespaces. `instanceExtension.getState` shows the global entries and those of the namespaces that are open, and none is open when a module
                                                        is imported, so the scoped ones are read from the entries the extension keeps per namespace (without this a scoped instance of Tengoku, Mathlib's
                                                        `Classical.propDecidable` and the pointwise instances among them, was not carried at all: 0 of 42,314 rows of the whole tree said `scoped`)
  {"n": [...], "bi": [[[...], "instImplicit"], ...]}     the names and annotations of the leading binders of its type (what lean4export may have replaced by those of an equal term)

`tengai-replay --ext` puts them back. Names travel as arrays of components, never as strings: a numbered or private name does not survive `String.toName`. It imports Lean; no library imports it.
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

def nameToJson (n : Name) : Json :=
  Json.arr (n.components.toArray.map fun c => match c with
    | .str _ s => Json.str s
    | .num _ k => Json.num (JsonNumber.fromNat k)
    | _ => Json.null)

def infoString : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

/-- the names and annotations of the leading binders of a type (at most 64): lean4export shares terms that are equal up to binder names and annotations, so a replayed constant can carry another term's -/
partial def leadingBinders (e : Expr) (acc : Array Json := #[]) : Array Json :=
  if acc.size ≥ 64 then acc else
  match e with
  | .forallE n _ b i => leadingBinders b (acc.push (Json.arr #[nameToJson n, Json.str (infoString i)]))
  | _ => acc

def statusString : ReducibilityStatus → String
  | .reducible => "reducible"
  | .semireducible => "semireducible"
  | .irreducible => "irreducible"
  | .implicitReducible => "implicitReducible"
  | .instanceReducible => "instanceReducible"

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | file :: mods@(_ :: _) =>
    enableInitializersExecution
    initSearchPath (← findSysroot)
    let env ← importModules (mods.toArray.map fun m => { module := m.toName }) {} (loadExts := true)
    -- the scoped instances, by constant: (namespace, priority) of every scoped registration
    let mut scopedRegs : Std.HashMap Name (Array (Name × Nat)) := {}
    for (ns, es) in (Meta.instanceExtension.ext.getState env).scopedEntries.map.toList do
      for e in es do
        if let some n := e.globalName? then
          scopedRegs := scopedRegs.insert n ((scopedRegs.getD n #[]).push (ns, e.priority))
    let mut seen := 0
    let mut emitted := 0
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
      seen := seen + 1
      let mut fields : List (String × Json) := [("n", nameToJson n)]
      let st := getReducibilityStatusCore env n
      if st != .semireducible then fields := fields ++ [("red", Json.str (statusString st))]
      if let some p := env.getProjectionFnInfo? n then
        fields := fields ++ [("proj", Json.mkObj [("ctor", nameToJson p.ctorName), ("np", toJson p.numParams), ("i", toJson p.i), ("cls", toJson p.fromClass)])]
      if isClass env n then fields := fields ++ [("class", Json.bool true)]
      if let some si := getStructureInfo? env n then
        -- the fields in the order of the constructor, each with its projection, whether it embeds a parent, and its annotation; then the parents of the `extends` clause
        let mut fs : Array Json := #[]
        for f in si.fieldNames do
          let some fi := getFieldInfo? env n f | throw (IO.userError s!"structure {n}: no field information for {f}")
          fs := fs.push (Json.mkObj [("f", nameToJson fi.fieldName), ("proj", nameToJson fi.projFn),
            ("sub", match fi.subobject? with | some s => nameToJson s | none => Json.null), ("bi", Json.str (infoString fi.binderInfo))])
        let ps := si.parentInfo.map fun p => Json.mkObj [("s", nameToJson p.structName), ("sub", Json.bool p.subobject), ("proj", nameToJson p.projFn)]
        fields := fields ++ [("st", Json.mkObj [("fields", Json.arr fs), ("parents", Json.arr ps)])]
      if let some e := (Meta.instanceExtension.getState env).instanceNames.find? n then
        match e.attrKind with
        | .local => pure ()
        | k => fields := fields ++ [("inst", Json.mkObj [("prio", toJson e.priority), ("kind", Json.str (if k matches .scoped then "scoped" else "global"))])]
      if let some ss := scopedRegs[n]? then
        let sorted := ss.qsort fun a b => a.1.toString < b.1.toString || (a.1.toString == b.1.toString && a.2 < b.2)
        fields := fields ++ [("sinst", Json.arr (sorted.map fun (ns, p) => Json.mkObj [("ns", nameToJson ns), ("prio", toJson p)]))]
      if let some ci := env.find? n then
        let bs := leadingBinders ci.type
        if bs.size > 0 then fields := fields ++ [("bi", Json.arr bs)]
      if fields.length > 1 then
        IO.println (Json.mkObj fields).compress
        emitted := emitted + 1
    IO.eprintln s!"extinfo: {emitted} of {seen} names carry something"
    return 0
  | _ =>
    IO.eprintln "usage: lake env tengai-extinfo ADDED.jsonl Module..."
    return 2
