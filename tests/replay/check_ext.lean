import TengaiData.Fx
open Fx

-- needs the instance `Sz Nat` found by synthesis
example : Nonempty (Sz Nat) := ⟨inferInstance⟩  -- a proposition: replayed constants have no compiled code, so no data is built here
#synth Sz Nat
-- needs `MyNat` to unfold at reducible transparency (instance search for `+` on a `MyNat`)
example (y : MyNat) : y + 0 = y := Nat.add_zero y
-- needs the annotations of the source: the class parameter of a projection that the result does not mention is explicit
example : Sz.n Nat = 1 := sz_nat
