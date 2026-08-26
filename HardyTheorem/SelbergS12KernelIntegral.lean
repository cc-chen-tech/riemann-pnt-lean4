import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open Real MeasureTheory Module

namespace HardyTheorem

/-!
# Selberg S12: the square-root Perron kernel

After choosing the Perron line `sigma = theta + epsilon`, the analytic input
leaves the real kernel

`sqrt (epsilon + |t|) / (sigma^2 + t^2)`.

Its integral is `O(sigma⁻¹/²)` whenever `0 ≤ epsilon ≤ sigma`.  The proof below
normalizes by `t = sigma * u`; the only fixed kernel that remains is bounded by
`2 * (1 + |u|)⁻³/²`.
-/

noncomputable def selbergS12BaseKernel (u : ℝ) : ℝ :=
  Real.sqrt (1 + |u|) / (1 + u ^ 2)

noncomputable def selbergS12Kernel (epsilon sigma t : ℝ) : ℝ :=
  Real.sqrt (epsilon + |t|) / (sigma ^ 2 + t ^ 2)

theorem continuous_selbergS12BaseKernel :
    Continuous selbergS12BaseKernel := by
  unfold selbergS12BaseKernel
  exact (Real.continuous_sqrt.comp (continuous_const.add continuous_abs)).div
    (continuous_const.add (continuous_id.pow 2)) (fun u => by positivity)

/-- The normalized kernel is integrable.  The exponent `3/2` is the exact
amount of decay produced by a square-root numerator over a quadratic
denominator. -/
theorem integrable_selbergS12BaseKernel :
    Integrable selbergS12BaseKernel := by
  have hg :
      Integrable (fun u : ℝ => 2 * (1 + ‖u‖) ^ (-(3 / 2 : ℝ))) := by
    exact (integrable_one_add_norm (E := ℝ) (r := (3 / 2 : ℝ))
      (by norm_num)).const_mul 2
  refine hg.mono' continuous_selbergS12BaseKernel.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by unfold selbergS12BaseKernel; positivity :
      0 ≤ selbergS12BaseKernel u)]
  let a : ℝ := 1 + |u|
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hden : a ^ 2 / 2 ≤ 1 + u ^ 2 := by
    dsimp [a]
    nlinarith [sq_nonneg (|u| - 1), sq_abs u]
  have hquot :
      Real.sqrt a / (1 + u ^ 2) ≤ Real.sqrt a / (a ^ 2 / 2) :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) hden
  have hrpow :
      a ^ (1 / 2 : ℝ) / a ^ (2 : ℕ) = a ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub ha]
    congr 1
    norm_num
  calc
    selbergS12BaseKernel u = Real.sqrt a / (1 + u ^ 2) := by rfl
    _ ≤ Real.sqrt a / (a ^ 2 / 2) := hquot
    _ = 2 * (a ^ (1 / 2 : ℝ) / a ^ (2 : ℕ)) := by
      rw [Real.sqrt_eq_rpow]
      ring
    _ = 2 * a ^ (-(3 / 2 : ℝ)) := by rw [hrpow]
    _ = 2 * (1 + ‖u‖) ^ (-(3 / 2 : ℝ)) := by
      simp [a, Real.norm_eq_abs]

/-- Exact scaling identity for the majorant with `epsilon = sigma`. -/
theorem selbergS12ScaledKernel_eq {sigma t : ℝ} (hsigma : 0 < sigma) :
    selbergS12Kernel sigma sigma t =
      (1 / (sigma * Real.sqrt sigma)) * selbergS12BaseKernel (t / sigma) := by
  have hs0 : sigma ≠ 0 := hsigma.ne'
  have hsqrt0 : Real.sqrt sigma ≠ 0 := (Real.sqrt_pos.2 hsigma).ne'
  have hsqrtsq : Real.sqrt sigma ^ 2 = sigma := Real.sq_sqrt hsigma.le
  have habs : |t / sigma| = |t| / sigma := by
    rw [abs_div, abs_of_pos hsigma]
  have hone : 1 + |t| / sigma = (sigma + |t|) / sigma := by
    field_simp
  have htwo :
      1 + (t / sigma) ^ 2 = (sigma ^ 2 + t ^ 2) / sigma ^ 2 := by
    field_simp
  rw [selbergS12Kernel, selbergS12BaseKernel, habs, hone, htwo,
    Real.sqrt_div (by positivity : 0 ≤ sigma + |t|) sigma]
  field_simp
  nlinarith

theorem integrable_selbergS12ScaledKernel {sigma : ℝ} (hsigma : 0 < sigma) :
    Integrable (selbergS12Kernel sigma sigma) := by
  have hscaled := (integrable_selbergS12BaseKernel.comp_div hsigma.ne').const_mul
    (1 / (sigma * Real.sqrt sigma))
  exact hscaled.congr (Filter.Eventually.of_forall fun t =>
    (selbergS12ScaledKernel_eq hsigma).symm)

/-- Exact normalized integral.  Its right side is a fixed positive constant
times `sigma⁻¹/²`. -/
theorem integral_selbergS12ScaledKernel_eq {sigma : ℝ} (hsigma : 0 < sigma) :
    (∫ t : ℝ, selbergS12Kernel sigma sigma t) =
      (∫ u : ℝ, selbergS12BaseKernel u) / Real.sqrt sigma := by
  have hs0 : sigma ≠ 0 := hsigma.ne'
  have hsqrt0 : Real.sqrt sigma ≠ 0 := (Real.sqrt_pos.2 hsigma).ne'
  rw [integral_congr_ae (Filter.Eventually.of_forall fun t =>
      selbergS12ScaledKernel_eq hsigma),
    integral_const_mul, Measure.integral_comp_div, abs_of_pos hsigma]
  simp only [smul_eq_mul]
  field_simp

/-- Uniform integrability and integral estimate for the actual S12 kernel. -/
theorem exists_integrable_integral_selbergS12Kernel_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ epsilon sigma : ℝ, 0 ≤ epsilon → epsilon ≤ sigma → 0 < sigma →
        Integrable (selbergS12Kernel epsilon sigma) ∧
          (∫ t : ℝ, selbergS12Kernel epsilon sigma t) ≤
            C / Real.sqrt sigma := by
  let C : ℝ := ∫ u : ℝ, selbergS12BaseKernel u
  have hC : 0 ≤ C := by
    dsimp [C]
    exact integral_nonneg (fun u => by unfold selbergS12BaseKernel; positivity)
  refine ⟨C, hC, ?_⟩
  intro epsilon sigma hepsilon hepsilonSigma hsigma
  have hscaled := integrable_selbergS12ScaledKernel hsigma
  have hpoint : ∀ t : ℝ,
      selbergS12Kernel epsilon sigma t ≤
        selbergS12Kernel sigma sigma t := by
    intro t
    unfold selbergS12Kernel
    exact div_le_div_of_nonneg_right
      (Real.sqrt_le_sqrt (by
        simpa [add_comm] using add_le_add_right hepsilonSigma |t|))
      (by positivity)
  have hkernel : Integrable (selbergS12Kernel epsilon sigma) := by
    refine hscaled.mono'
      (by
        apply Continuous.aestronglyMeasurable
        unfold selbergS12Kernel
        exact (Real.continuous_sqrt.comp
            (continuous_const.add continuous_abs)).div
          ((continuous_const.pow 2).add (continuous_id.pow 2))
          (fun t => by positivity))
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by unfold selbergS12Kernel; positivity :
        0 ≤ selbergS12Kernel epsilon sigma t)]
    exact hpoint t
  refine ⟨hkernel, ?_⟩
  calc
    (∫ t : ℝ, selbergS12Kernel epsilon sigma t) ≤
        ∫ t : ℝ, selbergS12Kernel sigma sigma t :=
      integral_mono hkernel hscaled hpoint
    _ = C / Real.sqrt sigma := by
      exact integral_selbergS12ScaledKernel_eq hsigma

end HardyTheorem
