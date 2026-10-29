import Tengoku.All

/-!
# The sum of the first `n` odd numbers is `n ^ 2`, in any commutative ring

The second abstraction seed. The statement is about a commutative ring `R`; the odd numbers are `2 * i + 1`.
-/

namespace Tengai

/-- `1 + 3 + … + (2 * n - 1) = n ^ 2`, in any commutative ring. -/
theorem sum_range_odd (R : Type*) [CommRing R] (n : ℕ) :
    (∑ i ∈ Finset.range n, (2 * (i : R) + 1)) = (n : R) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

end Tengai
