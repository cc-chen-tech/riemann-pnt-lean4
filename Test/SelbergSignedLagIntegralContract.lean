import HardyTheorem.SelbergSignedLagIntegral

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-!
# Contract for the lag form of the signed second moment
-/

example (X : ℕ) {A B H : ℝ} (hAB : A ≤ B) (hH : 0 ≤ H) :
    (∫ t in A..B, (selbergMoebiusSignedShortIntegral X H t) ^ 2) =
      ∫ τ in (-H)..H, ∫ v in max 0 (-τ)..min H (H - τ),
        ∫ x in A + v..B + v,
          selbergMoebiusMollifiedHardyZ X x *
            selbergMoebiusMollifiedHardyZ X (x + τ) :=
  integral_sq_signedShortIntegral_eq_lagIntegral X hAB hH

example (X : ℕ) (A T eta : ℝ) (hA0 : 0 < A) (hT1 : 1 < T)
    (hHT : A / Real.log T ≤ T) (heta : 0 < eta)
    (hlag :
      (∫ τ in (-(A / Real.log T))..(A / Real.log T),
        ∫ v in max 0 (-τ)..min (A / Real.log T) ((A / Real.log T) - τ),
          ∫ x in T + v..(2 * T - A / Real.log T) + v,
            selbergMoebiusMollifiedHardyZ X x *
              selbergMoebiusMollifiedHardyZ X (x + τ)) ≤
        T * eta ^ 2 / 24) :
    volume.real (Set.Icc T (2 * T - A / Real.log T) ∩
      selbergExcessiveSignedMassStarts X (A / Real.log T) eta) ≤ T / 24 :=
  volume_selbergExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_lagIntegral_le
    X A T eta hA0 hT1 hHT heta hlag

#print axioms integral_sq_signedShortIntegral_eq_lagIntegral
#print axioms
  volume_selbergExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_lagIntegral_le

end HardyTheorem
