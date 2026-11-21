import TengaiData.Fx
open Fx

-- structure instance notation needs the field information AND the structure's flat constructor `S.mk._flat_ctor`, an abbreviation Lean adds with every structure (and the projections)
theorem struct_inst : ({ x := 1, y := 2 } : Pt).x = 1 := rfl
-- `with` copies the fields it does not set
theorem struct_with (p : Pt) : ({ p with x := 3 } : Pt).y = p.y := rfl
-- the fields of the parent are written flat in the structure that extends it
theorem struct_extends : ({ x := 1, y := 2, z := 3 } : Pt3).z = 3 := rfl
