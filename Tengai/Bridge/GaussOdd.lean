import Tengoku.All
import Tengai.Seed.Gauss
import Tengai.Seed.OddSum

/-!
# A bridge: the odd sum is Gauss' sum, twice, plus `n`

`Tengai.Seed.Gauss` and `Tengai.Seed.OddSum` were proved separately and by the same induction. The bridge shows they are
one fact: the odd sum is `2 * (0 + 1 + … + (n - 1)) + n`, and Gauss' sum turns that into `n ^ 2`. It is a second proof of
`Tengai.sum_range_odd` that goes through `Tengai.sum_range_mul_two` instead of repeating the induction.
-/

namespace Tengai

/-- The odd sum split into twice the Gauss sum and `n` ones. -/
theorem sum_range_odd_split (R : Type*) [CommRing R] (n : ℕ) :
    (∑ i ∈ Finset.range n, (2 * (i : R) + 1)) = 2 * (∑ i ∈ Finset.range n, (i : R)) + n := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

/-- `sum_range_odd`, proved from Gauss' sum instead of by induction. -/
theorem sum_range_odd_of_gauss (R : Type*) [CommRing R] (n : ℕ) :
    (∑ i ∈ Finset.range n, (2 * (i : R) + 1)) = (n : R) ^ 2 := by
  rw [sum_range_odd_split]
  linear_combination sum_range_mul_two R n

end Tengai
