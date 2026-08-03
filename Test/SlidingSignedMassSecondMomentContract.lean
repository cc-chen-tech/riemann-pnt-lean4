import MathlibAux.SlidingSignedMassSecondMoment

set_option autoImplicit false

open MeasureTheory Set

namespace MathlibAux

example {F : ℝ → ℝ} (hF : Continuous F) (H : ℝ) :
    Continuous (slidingWindowMass F H) :=
  continuous_slidingWindowMass_of_continuous hF H

example {F : ℝ → ℝ} (hF : Continuous F)
    {A B H : ℝ} (hAB : A ≤ B) (hH : 0 ≤ H) :
    (∫ t in A..B, (slidingWindowMass F H t) ^ 2) =
      ∫ v in 0..H, ∫ w in 0..H, ∫ x in A + v..B + v,
        F x * F (x + (w - v)) :=
  integral_sq_slidingWindowMass_eq_correlation hF hAB hH

example {F : ℝ → ℝ} (hF : Continuous F)
    {A B H eta : ℝ} (hAB : A ≤ B) (heta : 0 < eta) :
    volume.real ({t | eta ≤ |slidingWindowMass F H t|} ∩ Icc A B) ≤
      (∫ t in A..B, (slidingWindowMass F H t) ^ 2) / eta ^ 2 :=
  volume_abs_slidingWindowMass_ge_inter_Icc_le_secondMoment hF hAB heta

end MathlibAux
