import HardyTheorem.SelbergSignedMassSecondMoment

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-!
# Contract for the signed short-mass second-moment chain

The examples expose the exact shapes of the sharp Chebyshev step and the
conditional `T / 24` endpoint bound driven by the translated autocorrelation
double integral.
-/

example (X : ℕ) {A B H : ℝ} (hAB : A ≤ B) (hH : 0 ≤ H) :
    (∫ t in A..B, (selbergMoebiusSignedShortIntegral X H t) ^ 2) =
      ∫ v in 0..H, ∫ w in 0..H, ∫ x in A + v..B + v,
        selbergMoebiusMollifiedHardyZ X x *
          selbergMoebiusMollifiedHardyZ X (x + (w - v)) :=
  integral_sq_signedShortIntegral_eq_correlation X hAB hH

example (X : ℕ) {A B H eta : ℝ} (hAB : A ≤ B) (heta : 0 < eta) :
    volume.real (selbergExcessiveSignedMassStarts X H eta ∩ Icc A B) ≤
      (∫ t in A..B, (selbergMoebiusSignedShortIntegral X H t) ^ 2) / eta ^ 2 :=
  volume_selbergExcessiveSignedMassStarts_inter_Icc_le_signedSecondMoment
    X hAB heta

example (X : ℕ) (A T eta : ℝ) (hA0 : 0 < A) (hT1 : 1 < T)
    (hHT : A / Real.log T ≤ T) (heta : 0 < eta)
    (hcorr :
      (∫ v in 0..A / Real.log T, ∫ w in 0..A / Real.log T,
        ∫ x in T + v..(2 * T - A / Real.log T) + v,
          selbergMoebiusMollifiedHardyZ X x *
            selbergMoebiusMollifiedHardyZ X (x + (w - v))) ≤
        T * eta ^ 2 / 24) :
    volume.real (Set.Icc T (2 * T - A / Real.log T) ∩
      selbergExcessiveSignedMassStarts X (A / Real.log T) eta) ≤ T / 24 :=
  volume_selbergExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_correlation_le
    X A T eta hA0 hT1 hHT heta hcorr

#print axioms integral_sq_signedShortIntegral_eq_correlation
#print axioms volume_selbergExcessiveSignedMassStarts_inter_Icc_le_signedSecondMoment
#print axioms
  volume_selbergExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_correlation_le

end HardyTheorem
