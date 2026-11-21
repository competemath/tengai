import TengaiData.Fx

-- after a replay with --stub-refused of an export whose Fx.add_swap proof was corrupted: the statement is still there, as an axiom
#check @Fx.add_swap
#print axioms Fx.add_swap
