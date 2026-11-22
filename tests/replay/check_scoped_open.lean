import TengaiData.Fx

-- the namespace of the scoped instance is open: it is found
open Fx.Scp
example : Nonempty (Fx.Tg Bool) := ⟨inferInstance⟩
#synth Fx.Tg Bool
