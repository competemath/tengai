namespace Fx

inductive Color where
  | red
  | green
  | blue

structure Pt where
  x : Nat
  y : Nat

def swap (p : Pt) : Pt := ⟨p.y, p.x⟩

theorem swap_swap (p : Pt) : swap (swap p) = p := by
  cases p
  rfl

theorem add_swap (a b : Nat) : a + b = b + a := Nat.add_comm a b

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

theorem fib_two : fib 2 = 1 := by decide

-- a nested inductive: the kernel builds auxiliary types for it
inductive Tree where
  | leaf : Nat → Tree
  | node : List Tree → Tree

theorem fun_ext_ex (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := funext h

theorem em_ex (p : Prop) : p ∨ ¬p := Classical.em p

-- what elaboration needs beyond the kernel: a class, an instance, a reducible definition
class Sz (α : Type) where
  n : Nat

instance : Sz Nat := ⟨1⟩

@[reducible] def MyNat : Type := Nat

theorem sz_nat : Sz.n Nat = 1 := rfl

end Fx
