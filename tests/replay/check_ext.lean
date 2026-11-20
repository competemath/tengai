import TengaiData.Fx
open Fx

-- needs the instance `Sz Nat` found by synthesis
example : Sz Nat := inferInstance
#synth Sz Nat
-- needs `MyNat` to unfold at reducible transparency (instance search for `+` on a `MyNat`)
example (y : MyNat) : y + 0 = y := Nat.add_zero y
