import Lean
open Lean Elab

/-!
# tengai-normalise: the canonical form, produced

`lake exe tengai-normalise FILE` prints FILE with the three SYNTACTIC rules of `conventions.toml` applied to every declaration signature (`declSig`):

* `gt-ge`:   `a > b` becomes `b < a`, `a ≥ b` becomes `b ≤ a`.
* `not-eq`:  `¬ a = b` (also `¬ (a = b)`) becomes `a ≠ b`.
* `nat-succ`: `Nat.succ n` becomes `n + 1`.

It edits the SOURCE TEXT at the positions of syntax nodes (parsed with the file's own imports, so a notation the file defines is known), so every comment, space and line break
outside a rewritten node is kept byte for byte. A rewritten node is rendered from the rewritten text of its children, so a nested violation is fixed in the same pass.
It is a fixed-point iteration: it applies the rules until nothing changes, and exits 3 if that does not happen within 8 passes (the rules are then not idempotent: a bug).
`tests/test_normalise.py` checks `normalise (normalise x) = normalise x` on a corpus and that `tengai-canon` finds none of the three rules in the result.

What it does NOT do (the checker `tengai-canon` still reports these, so nothing is missed silently): `n.succ` and `succ n` under `open Nat` (the syntax does not say the type), a
violation in a proof body (only signatures are canonical), a node with a comment inside it (a rewrite would drop the comment), and a `¬ a = b` or `Nat.succ n` whose parent
could change meaning if the replacement were not parenthesised (`¬` and `+` bind differently from the notation they replace): those are listed on stderr as `skipped`.

`--write` rewrites the file in place; `--check` prints nothing and exits 1 if the file is not canonical (the CI form).
-/

namespace TengaiNormalise

/-- the slice of `s` between two byte offsets -/
def slice (s : String) (a b : Nat) : String := String.fromUTF8! (s.toUTF8.extract a b)

structure Edit where
  lo : Nat
  hi : Nat
  text : String

/-- `text` over `[lo, hi)` with the edits (each inside the range, none overlapping) applied -/
def applyEdits (text : String) (lo hi : Nat) (es : Array Edit) : String := Id.run do
  let es := es.qsort fun a b => a.lo < b.lo
  let mut out := ""
  let mut cur := lo
  for e in es do
    out := out ++ slice text cur e.lo ++ e.text
    cur := e.hi
  return out ++ slice text cur hi

def range? (s : Syntax) : Option (Nat × Nat) := do
  let a ← s.getPos?
  let b ← s.getTailPos?
  return (a.byteIdx, b.byteIdx)

/-- a source slice that holds a comment: a node with one inside is not rewritten, the comment would be lost -/
def hasComment (s : String) : Bool :=
  (s.splitOn "--").length > 1 || (s.splitOn "/-").length > 1

/-- the parent kinds where a notation of precedence 50 or lower may stand without parentheses (an operand of `∧`, `∨`, `→`, `↔`, `¬`, a parenthesis, a type ascription) -/
def looseParent (parent grand : SyntaxNodeKind) : Bool :=
  parent == ``Lean.Parser.Term.paren || parent == ``Lean.Parser.Term.typeSpec
    || parent == `«term_∧_» || parent == `«term_∨_» || parent == `«term_→_» || parent == `«term_↔_» || parent == `«term¬_»
    || (parent == `null && (grand == ``Lean.Parser.Term.explicitBinder || grand == ``Lean.Parser.Term.implicitBinder
          || grand == ``Lean.Parser.Term.strictImplicitBinder || grand == ``Lean.Parser.Term.instBinder))

/-- the parent kinds where `n + 1` (precedence 65) may stand without parentheses: everywhere `looseParent` holds, and an operand of a relation -/
def tightParent (parent grand : SyntaxNodeKind) : Bool :=
  looseParent parent grand
    || parent == `«term_=_» || parent == `«term_≠_» || parent == `«term_<_» || parent == `«term_≤_»
    || parent == `«term_>_» || parent == `«term_≥_» || parent == `leftOfAdd

/-- an argument of `Nat.succ` that can be the left operand of `+` as written -/
def inlineKind (k : SyntaxNodeKind) : Bool :=
  k == `ident || k == `num || k == ``Lean.Parser.Term.proj || k == ``Lean.Parser.Term.app || k == ``Lean.Parser.Term.paren
    || k == `«term_+_» || k == `«term_-_» || k == `«term_*_» || k == `«term_/_» || k == `«term_%_» || k == `«term_^_»
    || k == ``Lean.Parser.Term.anonymousCtor || k == ``Lean.Parser.Term.typeAscription

def isParen (s : Syntax) : Bool := s.isOfKind ``Lean.Parser.Term.paren && s.getNumArgs == 3

/-- the edits of one syntax tree. `inSig`: below a `declSig`. `parent`, `grand`: the kinds of the two nodes above. `skipped` collects the lines for stderr. -/
partial def collect (text : String) (inSig : Bool) (parent grand : SyntaxNodeKind) (s : Syntax) :
    StateM (Array String) (Array Edit) := do
  let k := s.getKind
  let inSig := inSig || k == ``Lean.Parser.Command.declSig || k == ``Lean.Parser.Command.optDeclSig
  let render (c : Syntax) : StateM (Array String) String := do
    match range? c with
    | none => return ""
    | some (lo, hi) =>
      let es ← collect text inSig k parent c
      return applyEdits text lo hi es
  let descend : StateM (Array String) (Array Edit) := do
    let mut out : Array Edit := #[]
    for c in s.getArgs do
      out := out ++ (← collect text inSig k parent c)
    return out
  if !inSig then return (← descend)
  let some (lo, hi) := range? s | return (← descend)
  -- `a > b` and `a ≥ b`: same precedence as `<`, `≤`, so the swap is safe in every position
  if (k == `«term_>_» || k == `«term_≥_») && s.getNumArgs == 3 then
    let l := s[0]
    let r := s[2]
    let some (_, lt) := range? l | return (← descend)
    let some (rl, _) := range? r | return (← descend)
    if hasComment (slice text lt rl) then
      modify (·.push s!"skipped\tcomment-inside\t{lo}")
      return (← descend)
    let op := if k == `«term_>_» then "<" else "≤"
    return #[{ lo, hi, text := (← render r) ++ " " ++ op ++ " " ++ (← render l) }]
  -- `¬ a = b`
  if k == `«term¬_» && s.getNumArgs == 2 then
    let inner := if isParen s[1] then s[1][1] else s[1]
    if inner.isOfKind `«term_=_» && inner.getNumArgs == 3 then
      if !looseParent parent grand then
        modify (·.push s!"skipped\tnot-eq-context\t{lo}")
        return (← descend)
      let some (_, llt) := range? inner[0] | return (← descend)
      let some (rl, _) := range? inner[2] | return (← descend)
      if hasComment (slice text llt rl) then
        modify (·.push s!"skipped\tcomment-inside\t{lo}")
        return (← descend)
      return #[{ lo, hi, text := (← render inner[0]) ++ " ≠ " ++ (← render inner[2]) }]
  -- `Nat.succ n`
  if k == ``Lean.Parser.Term.app && s.getNumArgs == 2 && s[0].isIdent && s[0].getId == `Nat.succ
      && s[1].getNumArgs == 1 then
    let arg := s[1][0]
    let argNode := if isParen arg && inlineKind arg[1].getKind then arg[1] else arg
    -- the argument becomes the left operand of `+`: a `Nat.succ m` inside it is `m + 1 + 1`, not `(m + 1) + 1`
    let argRendered ← match range? argNode with
      | none => pure ""
      | some (alo, ahi) => do
        let es ← collect text inSig `leftOfAdd k argNode
        pure (applyEdits text alo ahi es)
    let argText := if inlineKind argNode.getKind then argRendered else s!"({argRendered})"
    let body := argText ++ " + 1"
    -- where `n + 1` would bind differently from `Nat.succ n` (an operand of `*`, `+`, an argument), it keeps parentheses
    return #[{ lo, hi, text := if tightParent parent grand then body else s!"({body})" }]
  return (← descend)

/-- one pass over a file's text: the new text and the lines `skipped` -/
unsafe def pass (text : String) : IO (String × Array String) := do
  enableInitializersExecution  -- here and not only in `main`: the compiled program failed `importModules (loadExts := true)` with it only in `main`
  let ictx := Parser.mkInputContext text "<tengai-normalise>"
  let (header, ps, msgs) ← Parser.parseHeader ictx
  let env ← importModules (Elab.headerToImports header) {} (trustLevel := 0) (loadExts := true)
  let cs := Command.mkState env msgs {}
  let st ← Elab.IO.processCommands ictx ps cs
  let mut edits : Array Edit := #[]
  let mut skipped : Array String := #[]
  for c in st.commands do
    let (es, sk) := (collect text false `null `null c).run #[]
    edits := edits ++ es
    skipped := skipped ++ sk
  return (applyEdits text 0 text.utf8ByteSize edits, skipped)

/-- apply the rules until nothing changes: the text, the `skipped` lines of the last pass, and whether it converged -/
unsafe def normalise (text : String) : IO (String × Array String × Bool) := do
  let mut cur := text
  let mut skipped : Array String := #[]
  for _ in [0:8] do
    let (next, sk) ← pass cur
    skipped := sk
    if next == cur then return (cur, skipped, true)
    cur := next
  return (cur, skipped, false)

end TengaiNormalise

unsafe def main (argv : List String) : IO UInt32 := do
  enableInitializersExecution
  let files := argv.filter fun a => !a.startsWith "--"
  let some file := files.head? | do
    IO.eprintln "usage: tengai-normalise FILE [--write | --check]"
    return 2
  initSearchPath (← findSysroot)
  let text ← IO.FS.readFile file
  let (out, skipped, ok) ← TengaiNormalise.normalise text
  for l in skipped.toList.eraseDups do IO.eprintln l
  if !ok then
    IO.eprintln "not a fixed point after 8 passes: the rules are not idempotent here (a bug)"
    return 3
  if argv.contains "--check" then
    return (if out == text then 0 else 1)
  if argv.contains "--write" then
    if out != text then IO.FS.writeFile file out
  else
    IO.print out
  return 0
