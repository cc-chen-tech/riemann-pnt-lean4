import MathlibAux.SeparatedFrequencySquareEnvelope

open scoped BigOperators

namespace MathlibAux

#check (stationaryMinReciprocalEnvelope : ℝ → ℝ → ℝ → ℝ)

#check (sum_sq_stationaryMinReciprocalEnvelope_le :
  ∀ (S : Finset ℝ) (Delta H xi : ℝ),
    0 < Delta → 0 ≤ H →
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → Delta ≤ |x - y|) →
    (∑ x ∈ S, (stationaryMinReciprocalEnvelope H xi x) ^ 2) ≤
      H ^ 2 + 12 * H / Delta)

end MathlibAux
