import Lean
open Lean Elab Command

/-! A type with expression metadata between two binders, which Lean's own elaborator leaves in auxiliary lemmas (`_proof_N`) and which the export drops: `tengai-extinfo` must read the telescope through it
(tests/test_replay.py). Not exported: it imports Lean, whose constants an export would carry along. -/
run_cmd liftCoreM do
  let nat := mkConst ``Nat
  -- ∀ {a : Nat}, [mdata] ∀ (b : Nat), a = a
  let eq := mkApp3 (mkConst ``Eq [Level.one]) nat (.bvar 1) (.bvar 1)
  let ty := Expr.forallE `a nat (.mdata {} (.forallE `b nat eq .default)) .implicit
  addDecl (.axiomDecl { name := `FxMd.throughMData, levelParams := [], type := ty, isUnsafe := false })
