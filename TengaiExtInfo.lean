import Lean
open Lean

/-!
# tengai-extinfo: what Lean keeps about a constant outside the kernel

`lake env tengai-extinfo ADDED.jsonl Module...` (run where the modules are built, e.g. in Tengoku's Lake project) reads the names a replay added (`tengai-replay --added`, one JSON array of name components a line)
and prints one JSON line for every one of them that has something to carry:

  {"n": [...], "red": "reducible"}                      reducibility other than semireducible
  {"n": [...], "proj": {"ctor": [...], "np": 2, "i": 0, "cls": true}}      a projection function
  {"n": [...], "class": true}                           a class
  {"n": [...], "inst": {"prio": 1000, "kind": "global"}}   an instance (local ones are not carried)

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
      if let some e := (Meta.instanceExtension.getState env).instanceNames.find? n then
        match e.attrKind with
        | .local => pure ()
        | k => fields := fields ++ [("inst", Json.mkObj [("prio", toJson e.priority), ("kind", Json.str (if k matches .scoped then "scoped" else "global"))])]
      if fields.length > 1 then
        IO.println (Json.mkObj fields).compress
        emitted := emitted + 1
    IO.eprintln s!"extinfo: {emitted} of {seen} names carry something"
    return 0
  | _ =>
    IO.eprintln "usage: lake env tengai-extinfo ADDED.jsonl Module..."
    return 2
