import PrimeNumberTheorem.MWKFCubicActualMoment

open Complex MeasureTheory Set

namespace PrimeNumberTheorem.MWKFCubic

#check CubicTestWeight
#check CubicTestWeight.hasCompactSupport_dilate
#check cubicMollifierLength
#check cubicMomentIntegrand
#check cubicMollifiedSecondMoment

#check (@cubicMollifierLength_cast_le :
  ∀ {T : ℝ}, 0 ≤ T → (cubicMollifierLength T : ℝ) ≤ T ^ 3)

#check (@cubicMomentIntegrand_eq_hardy :
  ∀ (W : CubicTestWeight) (T t : ℝ),
    cubicMomentIntegrand W T t =
      HardyTheorem.hardyZ t ^ 2 *
        Complex.normSq (HardyTheorem.selbergMoebiusMollifier
          (cubicMollifierLength T) ((1 / 2 : ℂ) + I * t)) * W (t / T))

#check (@integrable_cubicMomentIntegrand :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 →
    Integrable (cubicMomentIntegrand W T))

#check (@CubicTestWeight.hasCompactSupport_dilate :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 →
    HasCompactSupport (fun t : ℝ ↦ W (t / T)))

end PrimeNumberTheorem.MWKFCubic
