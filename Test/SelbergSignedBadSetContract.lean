import HardyTheorem.SelbergSignedBadSet

open MeasureTheory Set

namespace HardyTheorem

#check abs_intervalIntegral_sq_le_length_mul_intervalIntegral_sq
#check selbergExcessiveSignedMassStarts_subset_squareWindowMass
#check integral_slidingWindowMass_le_length_mul_globalMass
#check volume_selbergExcessiveSignedMassStarts_inter_Icc_le

example {X : ℕ} {A B H eta M : ℝ}
    (hAB : A ≤ B) (hH : 0 < H) (heta : 0 < eta)
    (hglobal :
      (∫ u in A..B + H, selbergMoebiusMollifiedHardyZ X u ^ 2) ≤ M) :
    volume.real (selbergExcessiveSignedMassStarts X H eta ∩ Icc A B) ≤
      H ^ 2 * M / eta ^ 2 :=
  volume_selbergExcessiveSignedMassStarts_inter_Icc_le hAB hH heta hglobal

#print axioms abs_intervalIntegral_sq_le_length_mul_intervalIntegral_sq
#print axioms selbergExcessiveSignedMassStarts_subset_squareWindowMass
#print axioms integral_slidingWindowMass_le_length_mul_globalMass
#print axioms volume_selbergExcessiveSignedMassStarts_inter_Icc_le

end HardyTheorem
