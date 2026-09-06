import HardyTheorem.SelbergCompletedMollifiedLp

open Complex Filter MeasureTheory Set Topology

namespace HardyTheorem

/-! # Direct L2 decay of Selberg's completed mollified function -/

private theorem eventually_shifted_pow_four_mul_exp_le_one_for_L2
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ T : ℝ in atTop,
      1 ≤ T ∧ (T + 3) ^ 4 * Real.exp (-a * T) ≤ 1 := by
  have hlt : ∀ᶠ T : ℝ in atTop,
      (T + 3) ^ 4 * Real.exp (-a * T) < 1 :=
    (tendsto_order.1 (tendsto_shifted_pow_four_mul_exp_neg ha)).2
      1 (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlt] with T hT hdecay
  exact ⟨hT, hdecay.le⟩

private theorem exists_tail_bound_selbergMellinRaw_criticalLine_zero
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) :
    ∃ R K : ℝ, 1 ≤ R ∧ 0 ≤ K ∧ ∀ t : ℝ, R ≤ |t| →
      ‖selbergMellinRawIntegrand (selbergFourierZ delta 0) X
        ((1 / 2 : ℂ) + I * t)‖ ≤ K := by
  let a : ℝ := delta / 8
  have ha : 0 < a := by dsimp [a]; positivity
  rcases exists_norm_selbergMellinRaw_horizontal_le
    hdelta0 hdeltaPi 0 X with ⟨K, hK, hbound⟩
  rcases (eventually_atTop.1
    (eventually_shifted_pow_four_mul_exp_le_one_for_L2 ha)) with ⟨R, hR⟩
  refine ⟨R, K, (hR R le_rfl).1, hK, ?_⟩
  intro t htR
  have htOne : 1 ≤ |t| := (hR R le_rfl).1.trans htR
  have hsmall := (hR |t| htR).2
  have hb := hbound (1 / 2) t ⟨le_rfl, by norm_num⟩ htOne
  have hsplit : Real.exp (-(delta / 4) * |t|) =
      Real.exp (-a * |t|) * Real.exp (-a * |t|) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [a]
    ring
  rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ) : ℂ)) by norm_num]
  calc
    _ ≤ K * (|t| + 3) ^ 4 * Real.exp (-(delta / 4) * |t|) := hb
    _ = K * ((|t| + 3) ^ 4 * Real.exp (-a * |t|)) *
        Real.exp (-a * |t|) := by rw [hsplit]; ring
    _ ≤ K * 1 * Real.exp (-a * |t|) := by gcongr
    _ ≤ K * 1 := by
      have hexp : Real.exp (-a * |t|) ≤ 1 :=
        Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (abs_nonneg t))
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hK zero_le_one)
    _ = K := mul_one K

private theorem exists_global_bound_of_continuous_of_tail_bound
    {f : ℝ → ℂ} (hf : Continuous f) {R K : ℝ}
    (hR : 0 ≤ R) (hK : 0 ≤ K)
    (htail : ∀ t : ℝ, R ≤ |t| → ‖f t‖ ≤ K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, ‖f t‖ ≤ M := by
  rcases isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn with
    ⟨C, hC⟩
  refine ⟨max C K, hK.trans (le_max_right _ _), ?_⟩
  intro t
  by_cases ht : |t| ≤ R
  · have htmem : t ∈ Icc (-R) R := by
      constructor <;> linarith [neg_le_abs t, le_abs_self t]
    exact (hC t htmem).trans (le_max_left _ _)
  · exact (htail t (le_of_not_ge ht)).trans (le_max_right _ _)

private theorem exists_global_bound_selbergMellinRaw_criticalLine_zero
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ,
      ‖selbergMellinRawIntegrand (selbergFourierZ delta 0) X
        ((1 / 2 : ℂ) + I * t)‖ ≤ M := by
  rcases exists_tail_bound_selbergMellinRaw_criticalLine_zero
    hdelta0 hdeltaPi X with ⟨R, K, hR, hK, htail⟩
  rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ) : ℂ)) by norm_num] at htail ⊢
  exact exists_global_bound_of_continuous_of_tail_bound
    (continuous_selbergMellinRaw_vertical (sigma := (1 / 2 : ℝ)) delta 0 X
      (by norm_num) (by norm_num))
    (zero_le_one.trans hR) hK htail

theorem integrable_normSq_selbergMellinRaw_criticalLine_zero
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) :
    Integrable (fun t : ℝ => Complex.normSq
      (selbergMellinRawIntegrand (selbergFourierZ delta 0) X
        ((1 / 2 : ℂ) + I * t))) := by
  let raw : ℝ → ℂ := fun t =>
    selbergMellinRawIntegrand (selbergFourierZ delta 0) X
      ((1 / 2 : ℂ) + I * t)
  have hraw := integrable_selbergMellinRaw_criticalLine_zero
    hdelta0 hdeltaPi X
  rcases exists_global_bound_selbergMellinRaw_criticalLine_zero
    hdelta0 hdeltaPi X with ⟨M, hM, hbound⟩
  have hmul := hraw.norm.mul_bdd hraw.norm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by
      simpa only [raw, Real.norm_eq_abs, abs_norm] using hbound t)
  simpa only [raw, Complex.normSq_eq_norm_sq, pow_two] using hmul

theorem memLp_two_selbergCompletedMollifiedF_complex
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) :
    MemLp (selbergCompletedMollifiedFComplex delta X) 2 := by
  let D : ℂ := (-2 * Real.sqrt (2 * Real.pi) : ℂ) *
    selbergFourierZ delta 0 ^ (1 / 2 : ℂ)
  let raw : ℝ → ℂ := fun t =>
    selbergMellinRawIntegrand (selbergFourierZ delta 0) X
      ((1 / 2 : ℂ) + I * t)
  have hrawSq := integrable_normSq_selbergMellinRaw_criticalLine_zero
    hdelta0 hdeltaPi X
  have hrawInt : Integrable raw :=
    integrable_selbergMellinRaw_criticalLine_zero hdelta0 hdeltaPi X
  have hrawMeas : AEStronglyMeasurable raw := hrawInt.aestronglyMeasurable
  have hraw2 : MemLp raw 2 := by
    rw [memLp_two_iff_integrable_sq_norm hrawMeas]
    simpa only [raw, Complex.normSq_eq_norm_sq] using hrawSq
  have hD : D ≠ 0 := selbergMellinRaw_zero_scalar_ne delta
  have hscaled := hraw2.const_mul D⁻¹
  apply hscaled.ae_eq
  filter_upwards with t
  have hrel := selbergMellinRaw_criticalLine_zero_eq_const_mul_F
    hdelta0 hdeltaPi X t
  have hrelD : raw t = D * selbergCompletedMollifiedFComplex delta X t := by
    simpa only [raw, D] using hrel
  change D⁻¹ * raw t = selbergCompletedMollifiedFComplex delta X t
  rw [hrelD]
  exact inv_mul_cancel_left₀ hD _

end HardyTheorem
