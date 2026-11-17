/-! A corpus for `tengai-normalise` (tests/test_normalise.py): every violation of the three syntactic rules in a position the normaliser handles, and the positions it must leave alone. -/

namespace Corpus

theorem gt (a b : Nat) (h : b < a) : b < a := h

theorem ge_nested (a b c : Nat) (h : b ≤ a ∧ c < b) : c < b := h.2

theorem gt_both_sides (a b : Nat) (h : b * 2 < a + 1) : b * 2 < a + 1 := h

theorem not_eq (a b : Nat) (h : a ≠ b) : a ≠ b := h

theorem not_eq_paren (a b : Nat) (h : a ≠ b) : a ≠ b := h

theorem not_eq_inside_and (a b : Nat) (h : a ≠ b ∧ 0 < a) : a ≠ b := h.1

theorem succ (n : Nat) : n + 1 = n + 1 := rfl

theorem succ_nested (n : Nat) : n + 1 + 1 = n + 2 := rfl

theorem succ_operand (n : Nat) : 2 * (n + 1) = 2 * n + 2 := by omega

theorem succ_compound (a b : Nat) : a + b + 1 = a + b + 1 := rfl

theorem succ_gt (n m : Nat) (h : m < n + 1) : m ≤ n := Nat.le_of_lt_succ h

theorem succ_paren (n : Nat) : n + 1 = n + 1 := rfl

-- already canonical: untouched
theorem canon_lt (a b : Nat) (h : a < b) : a ≠ b := Nat.ne_of_lt h

-- a proof body is not canonical form: untouched
theorem body_untouched (a b : Nat) (h : b < a) : b < a := by
  have : a > b := h
  exact this

theorem comment_inside (a b : Nat) (h : a > -- the larger one
    b) : b < a := h

end Corpus
