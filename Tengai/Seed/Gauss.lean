import Tengoku.All

/-!
# Gauss' sum in any commutative ring

Tengoku has the sum of the first `n` naturals as a statement about natural numbers, where the subtraction in
`n * (n - 1)` truncates. The same identity holds in every commutative ring, with the subtraction of the ring, and
the proof by induction does not need the truncation case at all. This is the first of Tengai's abstraction seeds:
discrete (`ℕ`) to algebraic (`CommRing`).
-/

namespace Tengai

/-- Twice the sum of `0, 1, …, n - 1` is `n * (n - 1)`, in any commutative ring. -/
theorem sum_range_mul_two (R : Type*) [CommRing R] (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : R)) * 2 = (n : R) * ((n : R) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    linear_combination ih

end Tengai
