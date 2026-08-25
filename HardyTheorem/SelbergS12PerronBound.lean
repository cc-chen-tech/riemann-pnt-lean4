import HardyTheorem.SelbergS12PerronIdentity
import HardyTheorem.SelbergS12CoprimeStripBound
import HardyTheorem.SelbergS12KernelIntegral

open Complex MeasureTheory Filter
open scoped BigOperators

namespace HardyTheorem

/-!
# Selberg S12: combining Perron inversion with the strip estimate

This file is the analytic synthesis step.  We stay on the absolutely convergent
line `sigma = theta + epsilon`; no contour shift or boundary value of the
Dirichlet series is used.
-/

theorem norm_selbergS12PerronKernel_eq {sigma t : ℝ} :
    ‖(1 / (selbergPerronLine sigma t) ^ 2 : ℂ)‖ =
      1 / (sigma ^ 2 + t ^ 2) := by
  rw [one_div, norm_inv, norm_pow, Complex.sq_norm, Complex.normSq_apply]
  simp [selbergPerronLine]
  ring_nf

theorem selbergS12PerronSeriesArgument_eq_stripPoint
    (theta epsilon t : ℝ) :
    (((1 - theta : ℝ) : ℂ) + selbergPerronLine (theta + epsilon) t) =
      selbergS12StripPoint epsilon t := by
  simp [selbergPerronLine, selbergS12StripPoint]
  ring

theorem norm_selbergS12PerronIntegrand_eq
    {r : ℕ} {theta epsilon Y t : ℝ} (hY : 0 < Y) :
    ‖selbergS12PerronIntegrand r theta Y (theta + epsilon) t‖ =
      Y ^ (theta + epsilon) *
        ‖selbergS12CoprimeDirichletSeries r
          (selbergS12StripPoint epsilon t)‖ *
        (1 / ((theta + epsilon) ^ 2 + t ^ 2)) := by
  unfold selbergS12PerronIntegrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY,
    selbergS12PerronSeriesArgument_eq_stripPoint]
  have hlineRe :
      (selbergPerronLine (theta + epsilon) t).re = theta + epsilon := by
    simp [selbergPerronLine]
  rw [hlineRe, norm_selbergS12PerronKernel_eq]

/-- General S12 estimate on the line `sigma = theta + epsilon`.  The important
feature is that the constant is uniform in `r`, `theta`, `epsilon`, and `Y`;
all `r`-dependence is the displayed finite Euler product. -/
theorem exists_norm_selbergS12WeightedCoprimeSum_le :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (r : ℕ) [NeZero r] (theta epsilon : ℝ) (Y : ℕ),
        0 ≤ theta → 0 < epsilon → epsilon ≤ 1 → 0 < Y →
        ‖selbergS12WeightedCoprimeSum r theta Y‖ ≤
          D * ((Y : ℝ) ^ (theta + epsilon)) /
              Real.sqrt (theta + epsilon) *
            Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
  rcases exists_norm_selbergS12CoprimeDirichletSeries_strip_le with
    ⟨B, hB, hseries⟩
  rcases exists_integrable_integral_selbergS12Kernel_le with
    ⟨C, hC, hkernel⟩
  let k : ℝ := ‖(1 / (2 * Real.pi) : ℂ)‖
  let D : ℝ := k * B * C
  have hk : 0 ≤ k := norm_nonneg _
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro r _ theta epsilon Y htheta hepsilon hepsilon1 hY
  let sigma : ℝ := theta + epsilon
  let P : ℝ := ∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    linarith
  have hepsilonSigma : epsilon ≤ sigma := by
    dsimp [sigma]
    linarith
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hseriesPoint (t : ℝ) :
      ‖selbergS12CoprimeDirichletSeries r
          (selbergS12StripPoint epsilon t)‖ ≤
        B * Real.sqrt (epsilon + |t|) * Real.sqrt P := by
    simpa only [P] using hseries r epsilon t hepsilon hepsilon1
  rcases hkernel epsilon sigma hepsilon.le hepsilonSigma hsigma with
    ⟨hkernelInt, hkernelBound⟩
  let M : ℝ := ((Y : ℝ) ^ sigma) * B * Real.sqrt P
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hmajorInt : Integrable (fun t : ℝ => M * selbergS12Kernel epsilon sigma t) :=
    hkernelInt.const_mul M
  have hpoint (t : ℝ) :
      ‖selbergS12PerronIntegrand r theta (Y : ℝ) sigma t‖ ≤
        M * selbergS12Kernel epsilon sigma t := by
    change
      ‖selbergS12PerronIntegrand r theta (Y : ℝ) (theta + epsilon) t‖ ≤
        M * selbergS12Kernel epsilon (theta + epsilon) t
    have hnorm := norm_selbergS12PerronIntegrand_eq
      (r := r) (theta := theta) (epsilon := epsilon) (Y := (Y : ℝ))
      (t := t) hYR
    rw [hnorm]
    calc
      (Y : ℝ) ^ sigma *
          ‖selbergS12CoprimeDirichletSeries r
            (selbergS12StripPoint epsilon t)‖ *
          (1 / (sigma ^ 2 + t ^ 2)) ≤
        (Y : ℝ) ^ sigma *
          (B * Real.sqrt (epsilon + |t|) * Real.sqrt P) *
          (1 / (sigma ^ 2 + t ^ 2)) := by
            gcongr
            exact hseriesPoint t
      _ = M * selbergS12Kernel epsilon sigma t := by
        unfold M selbergS12Kernel
        ring
  have hintegral :
      ‖∫ t : ℝ, selbergS12PerronIntegrand r theta (Y : ℝ) sigma t‖ ≤
        M * (C / Real.sqrt sigma) := by
    calc
      ‖∫ t : ℝ, selbergS12PerronIntegrand r theta (Y : ℝ) sigma t‖ ≤
          ∫ t : ℝ, ‖selbergS12PerronIntegrand r theta (Y : ℝ) sigma t‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, M * selbergS12Kernel epsilon sigma t :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          hmajorInt (Filter.Eventually.of_forall hpoint)
      _ = M * ∫ t : ℝ, selbergS12Kernel epsilon sigma t := by
        rw [integral_const_mul]
      _ ≤ M * (C / Real.sqrt sigma) :=
        mul_le_mul_of_nonneg_left hkernelBound hM
  have hPerron := normalized_integral_selbergS12PerronIntegrand_eq_weightedSum
    r theta (Y := Y) (sigma := sigma) htheta hY (by
      dsimp [sigma]
      linarith)
  rw [← hPerron, norm_mul]
  calc
    ‖(1 / (2 * Real.pi) : ℂ)‖ *
        ‖∫ t : ℝ, selbergS12PerronIntegrand r theta (Y : ℝ) sigma t‖ ≤
      k * (M * (C / Real.sqrt sigma)) :=
        mul_le_mul_of_nonneg_left hintegral hk
    _ = D * ((Y : ℝ) ^ (theta + epsilon)) /
          Real.sqrt (theta + epsilon) * Real.sqrt P := by
      dsimp [D, k, M, sigma]
      ring

end HardyTheorem
