namespace FxIdx

-- A type former behind a definition: the kernel finds the index of the family below by unfolding `Pred Nat`, and names the index binder of the recursor after the binder of the arrow it finds in the unfolding.
abbrev Pred (α : Type) : Type := α → Prop

inductive Cl (f : Nat → Nat) : Pred Nat
  | base (x : Nat) : Cl f (f x)
  | step (x : Nat) : Cl f x → Cl f (f x)

theorem cl_base (f : Nat → Nat) (x : Nat) : Cl f (f x) := Cl.base x

end FxIdx
