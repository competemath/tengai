import TengaiData.Fx
open Fx

-- the replayed constants are usable by name: a theorem, a structure and its projections, a recursive definition, a nested inductive
example (p : Pt) : swap (swap p) = p := swap_swap p
example (a b : Nat) : a + b = b + a := add_swap a b
example : fib 2 = 1 := fib_two
example : Tree.node [Tree.leaf 1] = Tree.node [Tree.leaf 1] := rfl  -- a statement, not data: replayed constants have no compiled code
#check @Tree.rec
#print axioms fun_ext_ex
#print axioms em_ex
#print axioms add_swap
