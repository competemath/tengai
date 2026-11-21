import TengaiData.Fx
open Fx

-- structure instance notation needs the structure's field information (propositions only: replayed constants have no compiled code, so no data is built here)
theorem struct_inst : ({ x := 1, y := 2 } : Pt).x = 1 := rfl
-- `with` copies the fields it does not set
theorem struct_with (p : Pt) : ({ p with x := 3 } : Pt).y = p.y := rfl
-- fields of the parent are written flat in the structure that extends it
theorem struct_extends : ({ x := 1, y := 2, z := 3 } : Pt3).z = 3 := rfl
-- and read through the subobject: `p.x` is `p.toPt.x`
theorem struct_parent_field (p : Pt3) : p.x = p.toPt.x := rfl
