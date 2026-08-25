import HardyTheorem.SelbergFourierThetaKernel

open Complex
open scoped BigOperators

namespace HardyTheorem

example (X : ℕ) (s : ℂ) :
    selbergSqrtZetaPsi X s =
      selbergMollifier X
        (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ)) s := rfl

example (delta : ℝ) (X : ℕ) (y : ℝ) :
    selbergNonconstantThetaKernel delta X y =
      ∑ μ ∈ Finset.Icc 1 X, ∑ ν ∈ Finset.Icc 1 X,
        ((selbergSqrtZetaTaperedCoeff X μ : ℂ) *
          (selbergSqrtZetaTaperedCoeff X ν : ℂ) / (ν : ℂ)) *
          selbergGaussianThetaSum delta y μ ν := rfl

example (delta : ℝ) (X : ℕ) (y : ℝ) :
    selbergExplicitInverseFourierKernel delta X y =
      (1 / 2 : ℂ) * selbergFourierZ delta y ^ (1 / 2 : ℂ) *
          selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0 -
        selbergFourierZ delta y ^ (-1 / 2 : ℂ) *
          selbergNonconstantThetaKernel delta X y := rfl

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) (y : ℝ) :
    Summable (selbergNonconstantThetaLevel delta X y) :=
  summable_selbergNonconstantThetaLevel hdelta0 hdeltaPi X y

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) (y : ℝ) :
    HasSum (selbergNonconstantThetaLevel delta X y)
      (selbergNonconstantThetaKernel delta X y) :=
  hasSum_selbergNonconstantThetaLevel hdelta0 hdeltaPi X y

#print axioms summable_selbergNonconstantThetaLevel
#print axioms hasSum_selbergNonconstantThetaLevel

end HardyTheorem
