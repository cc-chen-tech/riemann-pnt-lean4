import MathlibAux.StrictCancellationMeasure

open MeasureTheory Set
open scoped Interval

namespace MathlibAux

example
    {f : ℝ → ℝ} (hf : Continuous f) {T H L MS MA : ℝ}
    (hT : 0 ≤ T) (hH : 0 ≤ H) (hMS : 0 ≤ MS)
    (hfirst : L ≤ ∫ t in 0..T, slidingAbsoluteMass f H t)
    (hsignedSecond :
      (∫ t in 0..T, (slidingSignedAbsMass f H t) ^ 2) ≤ MS)
    (habsSecondInt : Integrable (fun t => (slidingAbsoluteMass f H t) ^ 2))
    (habsSecond : (∫ t : ℝ, (slidingAbsoluteMass f H t) ^ 2) ≤ MA)
    (hgap : 0 ≤ L - Real.sqrt (T * MS)) :
    (L - Real.sqrt (T * MS)) ^ 2 ≤
      volume.real (Icc 0 T ∩ strictCancellationStarts f H) * MA :=
  firstMomentGap_sq_le_strictCancellation_measure_mul_absSecondMoment
    hf hT hH hMS hfirst hsignedSecond habsSecondInt habsSecond hgap

#print axioms
  firstMomentGap_sq_le_strictCancellation_measure_mul_absSecondMoment

end MathlibAux
