import PrimeNumberTheorem.MWKFCubicAFEKernel

open Complex

namespace PrimeNumberTheorem.MWKFCubic

#check cubicCriticalPoint
#check cubicAFEPoleCanceller
#check cubicAFEKernelG
#check cubicAFECompletedExtension
#check cubicAFECompletedIntegrand
#check cubicAFEHolomorphicRemainder

#check (@cubicCriticalPoint_ne_zero :
  ∀ t : ℝ, cubicCriticalPoint t ≠ 0)

#check (@one_sub_cubicCriticalPoint_ne_zero :
  ∀ t : ℝ, 1 - cubicCriticalPoint t ≠ 0)

#check (@cubicAFEKernelG_zero :
  ∀ t : ℝ, cubicAFEKernelG t 0 = 1)

#check (@cubicAFEKernelG_neg :
  ∀ (t : ℝ) (z : ℂ), cubicAFEKernelG t (-z) = cubicAFEKernelG t z)

#check (@cubicAFEKernelG_at_criticalPoint :
  ∀ t : ℝ, cubicAFEKernelG t (cubicCriticalPoint t) = 0)

#check (@cubicAFEKernelG_at_neg_criticalPoint :
  ∀ t : ℝ, cubicAFEKernelG t (-cubicCriticalPoint t) = 0)

#check (@cubicAFEKernelG_at_one_sub_criticalPoint :
  ∀ t : ℝ, cubicAFEKernelG t (1 - cubicCriticalPoint t) = 0)

#check (@cubicAFEKernelG_at_criticalPoint_sub_one :
  ∀ t : ℝ, cubicAFEKernelG t (cubicCriticalPoint t - 1) = 0)

#check (@cubicAFEKernelG_at_half :
  ∀ t : ℝ, cubicAFEKernelG t (1 / 2 : ℂ) = 0)

#check (@cubicAFEKernelG_at_neg_half :
  ∀ t : ℝ, cubicAFEKernelG t (-1 / 2 : ℂ) = 0)

#check (@differentiable_cubicAFECompletedExtension :
  ∀ t : ℝ, Differentiable ℂ (cubicAFECompletedExtension t))

#check (@cubicAFECompletedExtension_neg :
  ∀ (t : ℝ) (z : ℂ),
    cubicAFECompletedExtension t (-z) = cubicAFECompletedExtension t z)

#check (@cubicAFECompletedExtension_eq :
  ∀ (t : ℝ) (z : ℂ),
    cubicCriticalPoint t + z ≠ 0 →
    1 - cubicCriticalPoint t - z ≠ 0 →
    1 - cubicCriticalPoint t + z ≠ 0 →
    cubicCriticalPoint t - z ≠ 0 →
      cubicAFECompletedExtension t z =
        cubicAFEKernelG t z *
          completedRiemannZeta (cubicCriticalPoint t + z) *
          completedRiemannZeta (1 - cubicCriticalPoint t + z))

#check (@cubicAFECompletedExtension_zero :
  ∀ t : ℝ,
    cubicAFECompletedExtension t 0 =
      completedRiemannZeta (cubicCriticalPoint t) *
        completedRiemannZeta (1 - cubicCriticalPoint t))

#check (@cubicAFECompletedIntegrand_residue_zero :
  ∀ t : ℝ,
    Filter.Tendsto
      (fun z : ℂ ↦ z * cubicAFECompletedIntegrand t z)
      (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds (completedRiemannZeta (cubicCriticalPoint t) *
        completedRiemannZeta (1 - cubicCriticalPoint t))))

#check (@differentiable_cubicAFEHolomorphicRemainder :
  ∀ t : ℝ, Differentiable ℂ (cubicAFEHolomorphicRemainder t))

#check (@cubicAFECompletedIntegrand_eq_remainder_add :
  ∀ (t : ℝ) {z : ℂ}, z ≠ 0 →
    cubicAFECompletedIntegrand t z =
      cubicAFEHolomorphicRemainder t z +
        z⁻¹ * cubicAFECompletedExtension t 0)

#check (@rectangleBoundaryIntegral_cubicAFECompletedIntegrand :
  ∀ (t : ℝ) {R : ℝ}, 0 < R →
    MathlibAux.rectangleBoundaryIntegral
        (cubicAFECompletedIntegrand t) 0 R =
      (2 * Real.pi * I) *
        (completedRiemannZeta (cubicCriticalPoint t) *
          completedRiemannZeta (1 - cubicCriticalPoint t)))

end PrimeNumberTheorem.MWKFCubic
