import PrimeNumberTheorem.MWKFCubicFiniteExpansion

open Complex MeasureTheory
open scoped BigOperators

namespace PrimeNumberTheorem.MWKFCubic

#check cubicMollifierSupport
#check cubicMollifierCoefficient
#check cubicTwistedIntegrand
#check cubicTwistedMoment
#check cubicComplexMollifiedSecondMoment

#check (@cubicMollifier_eq_sum :
  ∀ (T : ℝ) (s : ℂ),
    HardyTheorem.selbergMoebiusMollifier (cubicMollifierLength T) s =
      ∑ n ∈ cubicMollifierSupport T,
        (cubicMollifierCoefficient T n : ℂ) * (1 / (n : ℂ) ^ s))

#check (@cubicMollifierNormSq_eq_doubleSum :
  ∀ (T t : ℝ),
    (Complex.normSq (HardyTheorem.selbergMoebiusMollifier
      (cubicMollifierLength T) ((1 / 2 : ℂ) + I * t)) : ℂ) =
      ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
        (cubicMollifierCoefficient T d : ℂ) *
          (cubicMollifierCoefficient T e : ℂ) *
          ((1 / (d : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
            (starRingEnd ℂ)
              (1 / (e : ℂ) ^ ((1 / 2 : ℂ) + I * t))))

#check (@integrable_cubicTwistedIntegrand :
  ∀ (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0)
    {d e : ℕ} (hd : d ∈ cubicMollifierSupport T)
    (he : e ∈ cubicMollifierSupport T),
    Integrable (cubicTwistedIntegrand W T d e))

#check (@cubicComplexMollifiedSecondMoment_eq_ofReal :
  ∀ (W : CubicTestWeight) {T : ℝ} (_hT : T ≠ 0),
    cubicComplexMollifiedSecondMoment W T =
      (cubicMollifiedSecondMoment W T : ℂ))

#check (@cubicComplexMollifiedSecondMoment_eq_twisted_sum :
  ∀ (W : CubicTestWeight) {T : ℝ} (_hT : T ≠ 0),
    cubicComplexMollifiedSecondMoment W T =
      ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
        (cubicMollifierCoefficient T d : ℂ) *
          (cubicMollifierCoefficient T e : ℂ) *
          cubicTwistedMoment W T d e)

end PrimeNumberTheorem.MWKFCubic
