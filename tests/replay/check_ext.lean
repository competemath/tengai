import TengaiData.Fx
open Fx

-- needs the instance `Sz Nat` found by synthesis
example : Sz.n Nat = 1 := sz_nat
#synth Sz Nat
-- needs `MyNat` to unfold at reducible transparency (instance search for `+` on a `MyNat`)
example (y : MyNat) : y + 0 = y := Nat.add_zero y
#check @Sz.n
