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

-- structure information: a structure that extends another one (structure instance notation and `p.x` through the parent read it)
structure Pt3 extends Pt where
  z : Nat

-- layers: two theorems that share a definition of the fixture's own, the way two topics of a promotion share a foundation
def shared (n : Nat) : Nat := n + n

theorem left_use (n : Nat) : shared n = n + n := rfl

theorem right_use (n : Nat) : shared (shared n) = shared n + shared n := rfl

-- the kinds of term that the parsed tables keep as a record and a layer builds only when it reaches it: a string literal (with a quote, a newline and a non-ASCII character), a natural literal that
-- does not fit a machine word, a small one, and a `let`; the replay from the tables must write the module that the replay from the export writes, byte for byte
def greeting : String := "héllo \"quoted\"\n"

theorem big_literal : (2 : Nat) ^ 70 = 1180591620717411303424 := rfl

def small_literal : Nat := 42

def with_let (n : Nat) : Nat :=
  let m := n + 5
  m + m

-- a scoped instance: carried with the namespace it was declared scoped in, and found only where that namespace is open (`tengai-extinfo` did not see scoped instances at all before: the instance state of an
-- imported module holds the global entries and those of the namespaces that are open, and none is)
class Tg (α : Type) where
  tg : Nat

namespace Scp
scoped instance instTgBool : Tg Bool := ⟨2⟩
end Scp

end Fx
