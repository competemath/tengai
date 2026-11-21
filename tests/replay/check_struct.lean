import TengaiData.Fx
open Fx

-- field access through a parent needs the structure's field information: `p.x` is `p.toPt.x` (propositions only: replayed constants have no compiled code, so no data is built here)
theorem struct_parent_field (p : Pt3) : p.x = p.toPt.x := rfl
