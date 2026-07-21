import HardyTheorem.SelbergSignedFinalBound

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-!
# Contract for the conditional `T / 24` excessive-signed-mass bound
-/

example (X : ℕ) (A T eta M : ℝ) (hA0 : 0 < A) (hT1 : 1 < T)
    (hHT : A / Real.log T ≤ T) (heta : 0 < eta)
    (hglobal :
      (∫ u in T..(2 * T - A / Real.log T) + A / Real.log T,
        selbergMoebiusMollifiedHardyZ X u ^ 2) ≤ M)
    (hbudget : (A / Real.log T) ^ 2 * M ≤ T * eta ^ 2 / 24) :
    volume.real (Set.Icc T (2 * T - A / Real.log T) ∩
      selbergExcessiveSignedMassStarts X (A / Real.log T) eta) ≤ T / 24 :=
  volume_selbergExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_secondMoment_le
    X A T eta M hA0 hT1 hHT heta hglobal hbudget

#print axioms
  volume_selbergExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_secondMoment_le

end HardyTheorem
