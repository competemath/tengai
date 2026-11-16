/-! Fixtures of tengai-canon (tests/test_canon.py): each `bad_*` declaration breaks exactly the rule its name says and nothing else; each `good_*` breaks none. Not part of the
library: it is built on purpose, by the test. -/

namespace Fixtures

theorem bad_gt (a b : Nat) (h : a > b) : b < a := h

theorem bad_ge (a b : Nat) (h : a ≥ b) : b ≤ a := h

theorem bad_not_eq (a b : Nat) (h : ¬ a = b) : a ≠ b := h

theorem bad_succ (n : Nat) : Nat.succ n = n + 1 := rfl

theorem BadName (n : Nat) : n = n := rfl

inductive bad_type where
  | mk : bad_type

@[simp] theorem bad_global_simp (n : Nat) : n + 0 = n := rfl

instance bad_global_instance : Inhabited Bool := ⟨true⟩

theorem good_lt (a b : Nat) (h : a < b) : a < b := h

theorem good_ne (a b : Nat) (h : a ≠ b) : a ≠ b := h

theorem good_add (n : Nat) : n + 1 = n + 1 := rfl

theorem good_name' (n : Nat) : n = n := rfl

inductive GoodType where
  | mk : GoodType

-- registered, but only where the namespace is open or the scope is local: searchable, not active
@[scoped simp] theorem good_scoped_simp (n : Nat) : 0 + n = n := Nat.zero_add n

scoped instance good_scoped_instance : Inhabited GoodType := ⟨GoodType.mk⟩

section
local instance good_local_instance : Inhabited Nat := ⟨1⟩
end

end Fixtures
