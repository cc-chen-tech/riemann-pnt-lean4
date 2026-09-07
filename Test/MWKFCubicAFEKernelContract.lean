import PrimeNumberTheorem.MWKFCubicAFEKernel

open Complex
open scoped Interval

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

#check (@boundaryRectIntegral_cubicAFECompletedIntegrand :
  ∀ (t : ℝ) {x0 x1 y0 y1 : ℝ},
    x0 < 0 → 0 < x1 → y0 < 0 → 0 < y1 →
      MathlibAux.boundaryRectIntegral
          (cubicAFECompletedIntegrand t) x0 x1 y0 y1 =
        (2 * Real.pi * I) *
          (completedRiemannZeta (cubicCriticalPoint t) *
            completedRiemannZeta (1 - cubicCriticalPoint t)))

#check (@boundaryRectIntegral_cubicAFECompletedIntegrand_symmetric :
  ∀ (t : ℝ) {X V : ℝ}, 0 < X → 0 < V →
    MathlibAux.boundaryRectIntegral
        (cubicAFECompletedIntegrand t) (-X) X (-V) V =
      (2 * Real.pi * I) *
        (completedRiemannZeta (cubicCriticalPoint t) *
          completedRiemannZeta (1 - cubicCriticalPoint t)))

#check (@cubicAFECompletedIntegrand_neg :
  ∀ (t : ℝ) (z : ℂ),
    cubicAFECompletedIntegrand t (-z) =
      -cubicAFECompletedIntegrand t z)

#check (@cubicAFECompletedIntegrand_horizontal_symmetry :
  ∀ (t X V : ℝ),
    (∫ x : ℝ in -X..X,
        cubicAFECompletedIntegrand t ((x : ℂ) + (-V : ℂ) * I)) =
      -(∫ x : ℝ in -X..X,
        cubicAFECompletedIntegrand t ((x : ℂ) + (V : ℂ) * I)))

#check (@cubicAFECompletedIntegrand_vertical_symmetry :
  ∀ (t X V : ℝ),
    (∫ y : ℝ in -V..V,
        cubicAFECompletedIntegrand t ((-X : ℂ) + (y : ℂ) * I)) =
      -(∫ y : ℝ in -V..V,
        cubicAFECompletedIntegrand t ((X : ℂ) + (y : ℂ) * I)))

#check (@cubicAFEFiniteVerticalIdentity :
  ∀ (t : ℝ) {X V : ℝ}, 0 < X → 0 < V →
    (∫ y : ℝ in -V..V,
        cubicAFECompletedIntegrand t ((X : ℂ) + (y : ℂ) * I)) +
      I * (∫ x : ℝ in -X..X,
        cubicAFECompletedIntegrand t ((x : ℂ) + (V : ℂ) * I)) =
      Real.pi *
        (completedRiemannZeta (cubicCriticalPoint t) *
          completedRiemannZeta (1 - cubicCriticalPoint t)))

end PrimeNumberTheorem.MWKFCubic
