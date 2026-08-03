import MathlibAux.SlidingExponentialGapDecomposition

open Complex
open scoped BigOperators

namespace MathlibAux

/-!
# Contract for sliding exponential gap decomposition
-/

#check slidingExponentialGapSum
#check slidingExponentialGapSum_le_diagonal_add_frequencyGap

example {ι : Type*} (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    {A B H : ℝ} (hAB : A ≤ B) :
    slidingExponentialGapSum s coeff freq A B H ≤
      (B - A) *
          ∑ n ∈ s,
            Complex.normSq (slidingExponentialCoefficient H coeff freq n) +
        H ^ 2 *
          ∑ m ∈ s, ∑ n ∈ s,
            2 * ‖coeff m‖ * ‖coeff n‖ / |freq m - freq n| :=
  slidingExponentialGapSum_le_diagonal_add_frequencyGap s coeff freq hAB

end MathlibAux
