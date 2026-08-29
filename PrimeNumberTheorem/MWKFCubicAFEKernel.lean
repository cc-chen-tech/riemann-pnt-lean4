import Mathlib.NumberTheory.LSeries.RiemannZeta
import MathlibAux.RectangleResidue

open Complex Filter Set

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# Pole-cancelled kernel for the cubic MWKF approximate functional equation

This file fixes the exact algebraic kernel from the paper proof.  It proves
all six prescribed zeros, its evenness, and its normalization at the origin.
No contour shift or asymptotic estimate is asserted here.
-/

/-- The point `1/2+it` on the critical line. -/
noncomputable def cubicCriticalPoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + I * t

/-- The polynomial part that cancels the four moving completed-zeta poles and
the two fixed half-boundary poles. -/
noncomputable def cubicAFEPoleCanceller (t : ℝ) (z : ℂ) : ℂ :=
  (1 - 4 * z ^ 2) *
    (1 - z ^ 2 / cubicCriticalPoint t ^ 2) *
    (1 - z ^ 2 / (1 - cubicCriticalPoint t) ^ 2)

/-- The complete even Gaussian AFE kernel `G_t(z)`. -/
noncomputable def cubicAFEKernelG (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z ^ 2) * cubicAFEPoleCanceller t z

/-- The explicit entire extension of
`G_t(z) Lambda(s_t+z) Lambda(1-s_t+z)`.  Each bracket is the numerator
obtained after inserting Mathlib's entire `completedRiemannZeta₀` and
clearing the two simple-pole denominators. -/
noncomputable def cubicAFECompletedExtension (t : ℝ) (z : ℂ) : ℂ :=
  let s := cubicCriticalPoint t
  let u := 1 - s
  Complex.exp (z ^ 2) * (1 - 4 * z ^ 2) / (s ^ 2 * u ^ 2) *
    (completedRiemannZeta₀ (s + z) * (s + z) * (u - z) -
      (u - z) - (s + z)) *
    (completedRiemannZeta₀ (u + z) * (u + z) * (s - z) -
      (s - z) - (u + z))

/-- The completed AFE integrand after the four moving poles have been removed;
its only remaining singular factor is `1/z`. -/
noncomputable def cubicAFECompletedIntegrand (t : ℝ) (z : ℂ) : ℂ :=
  cubicAFECompletedExtension t z / z

/-- The holomorphic remainder after subtracting the unique principal part at
the origin. -/
noncomputable def cubicAFEHolomorphicRemainder (t : ℝ) (z : ℂ) : ℂ :=
  dslope (cubicAFECompletedExtension t) 0 z

theorem cubicCriticalPoint_ne_zero (t : ℝ) :
    cubicCriticalPoint t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [cubicCriticalPoint] at hre

theorem one_sub_cubicCriticalPoint_ne_zero (t : ℝ) :
    1 - cubicCriticalPoint t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [cubicCriticalPoint] at hre

/-- The pole-cleared completed product is an entire function of the shift. -/
theorem differentiable_cubicAFECompletedExtension (t : ℝ) :
    Differentiable ℂ (cubicAFECompletedExtension t) := by
  have hcompleted : Differentiable ℂ completedRiemannZeta₀ :=
    differentiable_completedZeta₀
  unfold cubicAFECompletedExtension
  fun_prop

set_option maxRecDepth 10000 in
/-- The entire completed numerator retains the `z ↦ -z` symmetry supplied by
the completed-zeta functional equation. -/
theorem cubicAFECompletedExtension_neg (t : ℝ) (z : ℂ) :
    cubicAFECompletedExtension t (-z) =
      cubicAFECompletedExtension t z := by
  have hleft :
      completedRiemannZeta₀ (cubicCriticalPoint t + -z) =
        completedRiemannZeta₀ (1 - cubicCriticalPoint t + z) := by
    calc
      completedRiemannZeta₀ (cubicCriticalPoint t + -z) =
          completedRiemannZeta₀
            (1 - (cubicCriticalPoint t + -z)) :=
        (completedRiemannZeta₀_one_sub _).symm
      _ = completedRiemannZeta₀ (1 - cubicCriticalPoint t + z) := by
        congr 1
        ring
  have hright :
      completedRiemannZeta₀ (1 - cubicCriticalPoint t + -z) =
        completedRiemannZeta₀ (cubicCriticalPoint t + z) := by
    calc
      completedRiemannZeta₀ (1 - cubicCriticalPoint t + -z) =
          completedRiemannZeta₀
            (1 - (1 - cubicCriticalPoint t + -z)) :=
        (completedRiemannZeta₀_one_sub _).symm
      _ = completedRiemannZeta₀ (cubicCriticalPoint t + z) := by
        congr 1
        ring
  unfold cubicAFECompletedExtension
  dsimp only
  rw [hleft, hright]
  simp only [neg_sq]
  ring

set_option maxRecDepth 10000 in
/-- Away from the original four poles, the explicit entire extension agrees
with the literal product of the kernel and the two completed zeta factors. -/
theorem cubicAFECompletedExtension_eq
    (t : ℝ) (z : ℂ)
    (hsplus : cubicCriticalPoint t + z ≠ 0)
    (husub : 1 - cubicCriticalPoint t - z ≠ 0)
    (huplus : 1 - cubicCriticalPoint t + z ≠ 0)
    (hssub : cubicCriticalPoint t - z ≠ 0) :
    cubicAFECompletedExtension t z =
      cubicAFEKernelG t z *
        completedRiemannZeta (cubicCriticalPoint t + z) *
        completedRiemannZeta (1 - cubicCriticalPoint t + z) := by
  have hs : cubicCriticalPoint t ≠ 0 := cubicCriticalPoint_ne_zero t
  have hu : 1 - cubicCriticalPoint t ≠ 0 :=
    one_sub_cubicCriticalPoint_ne_zero t
  have hLambdaLeft :
      completedRiemannZeta (cubicCriticalPoint t + z) =
        (completedRiemannZeta₀ (cubicCriticalPoint t + z) *
              (cubicCriticalPoint t + z) *
              (1 - cubicCriticalPoint t - z) -
            (1 - cubicCriticalPoint t - z) -
            (cubicCriticalPoint t + z)) /
          ((cubicCriticalPoint t + z) *
            (1 - cubicCriticalPoint t - z)) := by
    rw [completedRiemannZeta_eq]
    rw [show 1 - (cubicCriticalPoint t + z) =
      1 - cubicCriticalPoint t - z by ring]
    field_simp [hsplus, husub]
  have hLambdaRight :
      completedRiemannZeta (1 - cubicCriticalPoint t + z) =
        (completedRiemannZeta₀ (1 - cubicCriticalPoint t + z) *
              (1 - cubicCriticalPoint t + z) *
              (cubicCriticalPoint t - z) -
            (cubicCriticalPoint t - z) -
            (1 - cubicCriticalPoint t + z)) /
          ((1 - cubicCriticalPoint t + z) *
            (cubicCriticalPoint t - z)) := by
    rw [completedRiemannZeta_eq]
    rw [show 1 - (1 - cubicCriticalPoint t + z) =
      cubicCriticalPoint t - z by ring]
    field_simp [huplus, hssub]
  rw [hLambdaLeft, hLambdaRight]
  unfold cubicAFECompletedExtension cubicAFEKernelG cubicAFEPoleCanceller
  dsimp only
  field_simp [hs, hu, hsplus, husub, huplus, hssub]
  ring

theorem cubicAFEKernelG_zero (t : ℝ) :
    cubicAFEKernelG t 0 = 1 := by
  simp [cubicAFEKernelG, cubicAFEPoleCanceller]

theorem cubicAFEKernelG_neg (t : ℝ) (z : ℂ) :
    cubicAFEKernelG t (-z) = cubicAFEKernelG t z := by
  simp [cubicAFEKernelG, cubicAFEPoleCanceller]

theorem cubicAFEKernelG_at_criticalPoint (t : ℝ) :
    cubicAFEKernelG t (cubicCriticalPoint t) = 0 := by
  simp [cubicAFEKernelG, cubicAFEPoleCanceller,
    cubicCriticalPoint_ne_zero t]

theorem cubicAFEKernelG_at_neg_criticalPoint (t : ℝ) :
    cubicAFEKernelG t (-cubicCriticalPoint t) = 0 := by
  rw [cubicAFEKernelG_neg]
  exact cubicAFEKernelG_at_criticalPoint t

theorem cubicAFEKernelG_at_one_sub_criticalPoint (t : ℝ) :
    cubicAFEKernelG t (1 - cubicCriticalPoint t) = 0 := by
  simp [cubicAFEKernelG, cubicAFEPoleCanceller,
    one_sub_cubicCriticalPoint_ne_zero t]

theorem cubicAFEKernelG_at_criticalPoint_sub_one (t : ℝ) :
    cubicAFEKernelG t (cubicCriticalPoint t - 1) = 0 := by
  rw [show cubicCriticalPoint t - 1 = -(1 - cubicCriticalPoint t) by ring,
    cubicAFEKernelG_neg]
  exact cubicAFEKernelG_at_one_sub_criticalPoint t

theorem cubicAFEKernelG_at_half (t : ℝ) :
    cubicAFEKernelG t (1 / 2 : ℂ) = 0 := by
  have hhalf : (1 - 4 * (1 / 2 : ℂ) ^ 2) = 0 := by norm_num
  unfold cubicAFEKernelG cubicAFEPoleCanceller
  rw [hhalf]
  simp

theorem cubicAFEKernelG_at_neg_half (t : ℝ) :
    cubicAFEKernelG t (-1 / 2 : ℂ) = 0 := by
  calc
    cubicAFEKernelG t (-1 / 2 : ℂ) =
        cubicAFEKernelG t (-(1 / 2 : ℂ)) := by congr 1; ring
    _ = cubicAFEKernelG t (1 / 2 : ℂ) := cubicAFEKernelG_neg t _
    _ = 0 := cubicAFEKernelG_at_half t

/-- The entire numerator has the expected value at the sole remaining pole. -/
theorem cubicAFECompletedExtension_zero (t : ℝ) :
    cubicAFECompletedExtension t 0 =
      completedRiemannZeta (cubicCriticalPoint t) *
        completedRiemannZeta (1 - cubicCriticalPoint t) := by
  have hs : cubicCriticalPoint t ≠ 0 := cubicCriticalPoint_ne_zero t
  have hu : 1 - cubicCriticalPoint t ≠ 0 :=
    one_sub_cubicCriticalPoint_ne_zero t
  have hsplus : cubicCriticalPoint t + 0 ≠ 0 := by simpa using hs
  have husub : 1 - cubicCriticalPoint t - 0 ≠ 0 := by simpa using hu
  have huplus : 1 - cubicCriticalPoint t + 0 ≠ 0 := by simpa using hu
  have hssub : cubicCriticalPoint t - 0 ≠ 0 := by simpa using hs
  simpa [cubicAFEKernelG_zero] using
    cubicAFECompletedExtension_eq t 0 hsplus husub huplus hssub

/-- In limit form, the residue of the pole-cleared completed integrand at
`z=0` is exactly `Lambda(s_t)Lambda(1-s_t)`. -/
theorem cubicAFECompletedIntegrand_residue_zero (t : ℝ) :
    Tendsto
      (fun z : ℂ ↦ z * cubicAFECompletedIntegrand t z)
      (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds (completedRiemannZeta (cubicCriticalPoint t) *
        completedRiemannZeta (1 - cubicCriticalPoint t))) := by
  have hcontinuous : ContinuousAt (cubicAFECompletedExtension t) 0 :=
    (differentiable_cubicAFECompletedExtension t).continuous.continuousAt
  have ht : Tendsto (cubicAFECompletedExtension t)
      (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds (cubicAFECompletedExtension t 0)) :=
    hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  rw [cubicAFECompletedExtension_zero t] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  unfold cubicAFECompletedIntegrand
  field_simp [hz0]

/-- The divided difference supplying the regular part is entire. -/
theorem differentiable_cubicAFEHolomorphicRemainder (t : ℝ) :
    Differentiable ℂ (cubicAFEHolomorphicRemainder t) := by
  unfold cubicAFEHolomorphicRemainder
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope
    (isOpen_univ.mem_nhds (Set.mem_univ (0 : ℂ)))).2
      (differentiable_cubicAFECompletedExtension t).differentiableOn

/-- Off the origin, the completed integrand is its entire remainder plus the
single explicit principal part. -/
theorem cubicAFECompletedIntegrand_eq_remainder_add
    (t : ℝ) {z : ℂ} (hz : z ≠ 0) :
    cubicAFECompletedIntegrand t z =
      cubicAFEHolomorphicRemainder t z +
        z⁻¹ * cubicAFECompletedExtension t 0 := by
  unfold cubicAFECompletedIntegrand cubicAFEHolomorphicRemainder
  rw [dslope_of_ne _ hz]
  simp only [slope_def_module, sub_zero, smul_eq_mul]
  field_simp [hz]
  ring

/-- Every positively sized square centered at the origin encloses exactly the
one remaining AFE pole, so its boundary integral is `2 pi i` times the exact
completed-zeta residue. -/
theorem rectangleBoundaryIntegral_cubicAFECompletedIntegrand
    (t : ℝ) {R : ℝ} (hR : 0 < R) :
    MathlibAux.rectangleBoundaryIntegral
        (cubicAFECompletedIntegrand t) 0 R =
      (2 * Real.pi * I) *
        (completedRiemannZeta (cubicCriticalPoint t) *
          completedRiemannZeta (1 - cubicCriticalPoint t)) := by
  classical
  let residue : ℂ → ℂ := fun _ ↦ cubicAFECompletedExtension t 0
  let model : ℂ → ℂ := fun z ↦
    cubicAFEHolomorphicRemainder t z +
      ∑ p ∈ ({0} : Finset ℂ), (z - p)⁻¹ * residue p
  have hpole : (0 : ℂ) ∈ MathlibAux.openRectangle 0 R := by
    simp [MathlibAux.openRectangle, mem_reProdIm, hR]
  have hmodel :=
    MathlibAux.rectangleBoundaryIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
      (g := cubicAFEHolomorphicRemainder t) (c := (0 : ℂ))
      hR ({0} : Finset ℂ) residue
      (differentiable_cubicAFEHolomorphicRemainder t).differentiableOn
      (by
        intro p hp
        simp only [Finset.mem_singleton] at hp
        subst p
        exact hpole)
  have hboundary :
      MathlibAux.rectangleBoundaryIntegral
          (cubicAFECompletedIntegrand t) 0 R =
        MathlibAux.rectangleBoundaryIntegral model 0 R := by
    apply MathlibAux.rectangleBoundaryIntegral_congr_of_eqOn_boundary hR
    intro z hzclosed hznotopen
    have hz0 : z ≠ 0 := by
      intro hz
      subst z
      exact hznotopen hpole
    rw [cubicAFECompletedIntegrand_eq_remainder_add t hz0]
    simp [model, residue]
  rw [hboundary]
  simpa [model, residue, cubicAFECompletedExtension_zero t] using hmodel

end MWKFCubic
end PrimeNumberTheorem
