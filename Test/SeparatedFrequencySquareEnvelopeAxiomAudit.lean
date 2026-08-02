import MathlibAux.SeparatedFrequencySquareEnvelope

open scoped BigOperators

#check MathlibAux.stationaryMinReciprocalEnvelope
#check MathlibAux.sum_sq_stationaryMinReciprocalEnvelope_le

example (H xi x : ℝ) :
    MathlibAux.stationaryMinReciprocalEnvelope H xi x =
      if x = xi then H else min H (2 / |x - xi|) := by
  rfl

example (S : Finset ℝ) (Delta H xi : ℝ)
    (hDelta : 0 < Delta) (hH : 0 ≤ H)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Delta ≤ |x - y|) :
    (∑ x ∈ S,
      (MathlibAux.stationaryMinReciprocalEnvelope H xi x) ^ 2) ≤
        H ^ 2 + 12 * H / Delta := by
  exact MathlibAux.sum_sq_stationaryMinReciprocalEnvelope_le
    S Delta H xi hDelta hH hsep

#print axioms MathlibAux.sum_sq_stationaryMinReciprocalEnvelope_le
