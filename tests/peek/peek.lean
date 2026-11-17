/-! Fixture of `tengai-canon --source` (the rule `no-peek`): each `bad_*` looks inside a definition Tengai does not own; each `good_*` does not. Never built as a module. -/

def own_def (n : Nat) : Nat := n + 1

namespace Peek

theorem bad_unfold (n : Nat) : n + 0 = n := by unfold Nat.add; rfl

theorem bad_delta (n : Nat) : n + 0 = n := by delta Nat.add; rfl

theorem bad_simp (n : Nat) : n + 0 = n := by simp [Nat.add]

theorem bad_dsimp (n : Nat) : n + 0 = n := by dsimp only [Nat.add]

theorem bad_rw (n : Nat) : n + 0 = n := by rw [Nat.add]

unseal Nat.add in
theorem bad_unseal (n : Nat) : n + 0 = n := rfl

open Nat in
theorem bad_open (n : Nat) : n + 0 = n := by unfold add; rfl

theorem good_own (n : Nat) : own_def n = n + 1 := by unfold own_def; rfl

theorem good_theorem_rule (a b : Nat) : a + b = b + a := by simp [Nat.add_comm]

theorem good_rw_theorem (a b : Nat) : a + b = b + a := by rw [Nat.add_comm]

end Peek
