import HardyTheorem.SelbergS12OptimizedBound

open Complex MeasureTheory Filter
open scoped BigOperators LSeries.notation

namespace HardyTheorem

/-!
# Selberg S12 with a positive real cutoff

The arithmetic decomposition requires the exact cutoff `Y = X / d`, which
is generally not an integer.  The Perron kernel and all analytic estimates
already use a positive real parameter, so the natural statement is the
following `tsum` weighted by `perronLogCutoff (n / Y)`.
-/

noncomputable def selbergS12WeightedCoprimeSumReal
    (r : ℕ) (theta Y : ℝ) : ℂ :=
  ∑' n : ℕ, selbergS12ShiftedCoprimeCoeff r theta n *
    perronLogCutoff ((n : ℝ) / Y)

private theorem selbergS12PerronIntegrand_eq_generic_real
    (r : ℕ) (theta Y sigma t : ℝ) :
    selbergS12PerronIntegrand r theta Y sigma t =
      selbergPerronLSeriesIntegrand
        (selbergS12ShiftedCoprimeCoeff r theta) Y sigma t := by
  unfold selbergS12PerronIntegrand selbergPerronLSeriesIntegrand
  rw [LSeries_selbergS12ShiftedCoprimeCoeff_eq]

theorem normalized_integral_selbergS12PerronIntegrand_eq_weightedSumReal
    (r : ℕ) (theta : ℝ) {Y sigma : ℝ}
    (htheta : 0 ≤ theta) (hY : 0 < Y) (hsigma : theta < sigma) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, selbergS12PerronIntegrand r theta Y sigma t) =
      selbergS12WeightedCoprimeSumReal r theta Y := by
  have hsigma0 : 0 < sigma := htheta.trans_lt hsigma
  have hsum : LSeriesSummable
      (selbergS12ShiftedCoprimeCoeff r theta) (sigma : ℂ) :=
    LSeriesSummable_selbergS12ShiftedCoprimeCoeff hsigma
  rw [integral_congr_ae (Eventually.of_forall
    (selbergS12PerronIntegrand_eq_generic_real r theta Y sigma))]
  exact normalized_integral_selbergPerronLSeries_eq
    (selbergS12ShiftedCoprimeCoeff r theta) hY hsigma0 hsum

/-- General real-cutoff S12 estimate on `sigma = theta + epsilon`. -/
theorem exists_norm_selbergS12WeightedCoprimeSumReal_le :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (r : ℕ) [NeZero r] (theta epsilon Y : ℝ),
        0 ≤ theta → 0 < epsilon → epsilon ≤ 1 → 0 < Y →
        ‖selbergS12WeightedCoprimeSumReal r theta Y‖ ≤
          D * (Y ^ (theta + epsilon)) /
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
  let M : ℝ := (Y ^ sigma) * B * Real.sqrt P
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hmajorInt : Integrable
      (fun t : ℝ => M * selbergS12Kernel epsilon sigma t) :=
    hkernelInt.const_mul M
  have hpoint (t : ℝ) :
      ‖selbergS12PerronIntegrand r theta Y sigma t‖ ≤
        M * selbergS12Kernel epsilon sigma t := by
    change
      ‖selbergS12PerronIntegrand r theta Y (theta + epsilon) t‖ ≤
        M * selbergS12Kernel epsilon (theta + epsilon) t
    have hnorm := norm_selbergS12PerronIntegrand_eq
      (r := r) (theta := theta) (epsilon := epsilon) (Y := Y)
      (t := t) hY
    rw [hnorm]
    calc
      Y ^ sigma *
          ‖selbergS12CoprimeDirichletSeries r
            (selbergS12StripPoint epsilon t)‖ *
          (1 / (sigma ^ 2 + t ^ 2)) ≤
        Y ^ sigma *
          (B * Real.sqrt (epsilon + |t|) * Real.sqrt P) *
          (1 / (sigma ^ 2 + t ^ 2)) := by
            gcongr
            exact hseriesPoint t
      _ = M * selbergS12Kernel epsilon sigma t := by
        unfold M selbergS12Kernel
        ring
  have hintegral :
      ‖∫ t : ℝ, selbergS12PerronIntegrand r theta Y sigma t‖ ≤
        M * (C / Real.sqrt sigma) := by
    calc
      ‖∫ t : ℝ, selbergS12PerronIntegrand r theta Y sigma t‖ ≤
          ∫ t : ℝ, ‖selbergS12PerronIntegrand r theta Y sigma t‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, M * selbergS12Kernel epsilon sigma t :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          hmajorInt (Filter.Eventually.of_forall hpoint)
      _ = M * ∫ t : ℝ, selbergS12Kernel epsilon sigma t := by
        rw [integral_const_mul]
      _ ≤ M * (C / Real.sqrt sigma) :=
        mul_le_mul_of_nonneg_left hkernelBound hM
  have hPerron :=
    normalized_integral_selbergS12PerronIntegrand_eq_weightedSumReal
      r theta (Y := Y) (sigma := sigma) htheta hY (by
        dsimp [sigma]
        linarith)
  rw [← hPerron, norm_mul]
  calc
    ‖(1 / (2 * Real.pi) : ℂ)‖ *
        ‖∫ t : ℝ, selbergS12PerronIntegrand r theta Y sigma t‖ ≤
      k * (M * (C / Real.sqrt sigma)) :=
        mul_le_mul_of_nonneg_left hintegral hk
    _ = D * (Y ^ (theta + epsilon)) /
          Real.sqrt (theta + epsilon) * Real.sqrt P := by
      dsimp [D, k, M, sigma]
      ring

/-- Standard optimized S12 estimate with an exact positive real cutoff. -/
theorem exists_norm_selbergS12WeightedCoprimeSumReal_s12_le :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ (r : ℕ) [NeZero r] (theta Y : ℝ),
        0 ≤ theta → Real.exp 1 ≤ Y →
        ‖selbergS12WeightedCoprimeSumReal r theta Y‖ ≤
          E * (Y ^ theta) * Real.sqrt (Real.log Y) *
            Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
  rcases exists_norm_selbergS12WeightedCoprimeSumReal_le with
    ⟨D, hD, hgeneral⟩
  let E : ℝ := D * Real.exp 1
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  refine ⟨E, hE, ?_⟩
  intro r _ theta Y htheta hYexp
  have hYpos : 0 < Y := (Real.exp_pos 1).trans_le hYexp
  have hYone : Y ≠ 1 := by
    intro h
    rw [h] at hYexp
    have := Real.exp_one_gt_d9
    linarith
  have hlog : 1 ≤ Real.log Y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hYexp
  have hlogpos : 0 < Real.log Y := zero_lt_one.trans_le hlog
  have hepsilon : 0 < (Real.log Y)⁻¹ := inv_pos.mpr hlogpos
  have hepsilon1 : (Real.log Y)⁻¹ ≤ 1 :=
    (inv_le_one₀ hlogpos).2 hlog
  have h := hgeneral r theta (Real.log Y)⁻¹ Y
    htheta hepsilon hepsilon1 hYpos
  rw [Real.rpow_add hYpos, Real.rpow_inv_log hYpos hYone] at h
  have hsqrtLe :
      Real.sqrt (Real.log Y)⁻¹ ≤
        Real.sqrt (theta + (Real.log Y)⁻¹) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsqrtInvPos : 0 < Real.sqrt (Real.log Y)⁻¹ :=
    Real.sqrt_pos.2 hepsilon
  have hreciprocal :
      (Real.sqrt (theta + (Real.log Y)⁻¹))⁻¹ ≤
        Real.sqrt (Real.log Y) := by
    calc
      (Real.sqrt (theta + (Real.log Y)⁻¹))⁻¹ ≤
          (Real.sqrt (Real.log Y)⁻¹)⁻¹ := by
        simpa only [one_div] using
          one_div_le_one_div_of_le hsqrtInvPos hsqrtLe
      _ = Real.sqrt (Real.log Y) := by
        rw [Real.sqrt_inv]
        field_simp
  calc
    ‖selbergS12WeightedCoprimeSumReal r theta Y‖ ≤
        D * (Y ^ theta * Real.exp 1) /
            Real.sqrt (theta + (Real.log Y)⁻¹) *
          Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := h
    _ = (D * Real.exp 1 * (Y ^ theta)) *
          (Real.sqrt (theta + (Real.log Y)⁻¹))⁻¹ *
          Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ (D * Real.exp 1 * (Y ^ theta)) *
          Real.sqrt (Real.log Y) *
          Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
      gcongr
    _ = E * (Y ^ theta) * Real.sqrt (Real.log Y) *
          Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
      dsimp [E]

/-- Uniform form needed after the arithmetic split.  The local cutoff `Y`
may be smaller than `e`, but it is bounded by one global `X ≥ e`; in the
small range the unoptimized line `epsilon = 1` is absorbed by
`sqrt (log X) ≥ 1`. -/
theorem exists_norm_selbergS12WeightedCoprimeSumReal_context_le :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ (r : ℕ) [NeZero r] (theta X Y : ℝ),
        0 ≤ theta → Real.exp 1 ≤ X → 0 < Y → Y ≤ X →
        ‖selbergS12WeightedCoprimeSumReal r theta Y‖ ≤
          E * (Y ^ theta) * Real.sqrt (Real.log X) *
            Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
  rcases exists_norm_selbergS12WeightedCoprimeSumReal_le with
    ⟨D, hD, hgeneral⟩
  rcases exists_norm_selbergS12WeightedCoprimeSumReal_s12_le with
    ⟨E₀, hE₀, hlarge⟩
  let E : ℝ := E₀ + D * Real.exp 1
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  refine ⟨E, hE, ?_⟩
  intro r _ theta X Y htheta hX hY hYX
  have hlogX : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hX
  have hsqrtLogX : 1 ≤ Real.sqrt (Real.log X) := by
    simpa using Real.sqrt_le_sqrt hlogX
  have hP : 0 ≤ ∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹) := by
    positivity
  by_cases hYlarge : Real.exp 1 ≤ Y
  · have h := hlarge r theta Y htheta hYlarge
    have hlogYX : Real.log Y ≤ Real.log X :=
      Real.log_le_log hY hYX
    have hsqrtYX : Real.sqrt (Real.log Y) ≤ Real.sqrt (Real.log X) :=
      Real.sqrt_le_sqrt hlogYX
    calc
      ‖selbergS12WeightedCoprimeSumReal r theta Y‖ ≤
          E₀ * Y ^ theta * Real.sqrt (Real.log Y) * Real.sqrt
            (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := h
      _ ≤ E * Y ^ theta * Real.sqrt (Real.log X) * Real.sqrt
            (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
        have hE₀E : E₀ ≤ E := by
          dsimp [E]
          have hterm : 0 ≤ D * Real.exp 1 :=
            mul_nonneg hD (Real.exp_pos 1).le
          linarith
        gcongr
  · have hYupper : Y ≤ Real.exp 1 := le_of_not_ge hYlarge
    have h := hgeneral r theta 1 Y htheta zero_lt_one le_rfl hY
    have hsqrtOne : 1 ≤ Real.sqrt (theta + 1) := by
      have harg : (1 : ℝ) ≤ theta + 1 := by linarith
      simpa using Real.sqrt_le_sqrt harg
    have hsqrtPos : 0 < Real.sqrt (theta + 1) :=
      Real.sqrt_pos.2 (by linarith)
    have hinv : (Real.sqrt (theta + 1))⁻¹ ≤ 1 :=
      (inv_le_one₀ hsqrtPos).2 hsqrtOne
    have hDE : D * Real.exp 1 ≤ E := by
      dsimp [E]
      linarith
    rw [Real.rpow_add hY, Real.rpow_one] at h
    calc
      ‖selbergS12WeightedCoprimeSumReal r theta Y‖ ≤
          D * (Y ^ theta * Y) / Real.sqrt (theta + 1) *
            Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := h
      _ = D * Y ^ theta * Y * (Real.sqrt (theta + 1))⁻¹ *
            Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ D * Y ^ theta * Real.exp 1 * 1 *
            Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
        gcongr
      _ ≤ E * Y ^ theta * Real.sqrt (Real.log X) *
            Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
        have hYtheta : 0 ≤ Y ^ theta := Real.rpow_nonneg hY.le _
        calc
          D * Y ^ theta * Real.exp 1 * 1 * Real.sqrt
              (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) =
            (D * Real.exp 1) * Y ^ theta * 1 * Real.sqrt
              (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by ring
          _ ≤ E * Y ^ theta * Real.sqrt (Real.log X) * Real.sqrt
              (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
            gcongr

end HardyTheorem
