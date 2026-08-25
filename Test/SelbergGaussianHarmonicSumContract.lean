import HardyTheorem.SelbergGaussianHarmonicSum

namespace HardyTheorem

#check selbergGaussianHarmonic
#check selbergGaussianMass
#check selbergGaussianLogHarmonic
#check selbergOffDiagonalDampedBracket
#check selbergCappedGaussianParameter
#check summable_selbergGaussianHarmonic
#check summable_selbergGaussianMass
#check mul_tsum_selbergGaussianMass_le_two
#check tsum_selbergGaussianHarmonic_le_log
#check summable_selbergGaussianLogHarmonic
#check tsum_selbergGaussianLogHarmonic_le
#check summable_selbergOffDiagonalDampedBracket
#check tsum_selbergOffDiagonalDampedBracket_le
#check tsum_selbergGaussianHarmonic_le_log_capped
#check tsum_selbergGaussianLogHarmonic_le_capped
#check summable_selbergGaussianLogHarmonic_of_pos
#check summable_selbergOffDiagonalDampedBracket_of_pos

example {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (∑' n : ℕ, selbergGaussianHarmonic a n) ≤ Real.log (2 / a) :=
  tsum_selbergGaussianHarmonic_le_log ha0 ha1

example {a X : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hX : 1 ≤ X) :
    (∑' n : ℕ, selbergGaussianLogHarmonic a X n) ≤
      (Real.log X + Real.log (1 / a)) * Real.log (2 / a) + 2 :=
  tsum_selbergGaussianLogHarmonic_le ha0 ha1 hX

end HardyTheorem
