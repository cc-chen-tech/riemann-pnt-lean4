import PrimeNumberTheorem.CarlsonClosedCount

/-! Elementary geometric summation without any loss of logarithmic degree.
The finite initial height interval is absorbed using monotonicity. -/

open Filter

namespace PrimeNumberTheorem

private noncomputable def powerLogModel (q : ℝ) (B : ℕ) (T : ℝ) : ℝ :=
  T ^ q * (1 + Real.log T) ^ B

private lemma powerLogModel_nonneg {q T : ℝ} {B : ℕ} (hT : 1 ≤ T) :
    0 ≤ powerLogModel q B T := by
  have := Real.log_nonneg hT
  dsimp [powerLogModel]
  positivity

private lemma one_le_powerLogModel {q T : ℝ} {B : ℕ} (hq : 0 ≤ q) (hT : 1 ≤ T) :
    1 ≤ powerLogModel q B T := by
  have hlog : 1 ≤ 1 + Real.log T := by linarith only [Real.log_nonneg hT]
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hT hq) (one_le_pow₀ hlog)

private lemma powerLogModel_mono {q U T : ℝ} {B : ℕ}
    (hq : 0 ≤ q) (hU : 1 ≤ U) (hUT : U ≤ T) :
    powerLogModel q B U ≤ powerLogModel q B T := by
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hl := Real.log_le_log hUpos hUT
  have hlog : 0 ≤ 1 + Real.log U := by linarith only [Real.log_nonneg hU]
  exact mul_le_mul (Real.rpow_le_rpow hUpos.le hUT hq)
    (pow_le_pow_left₀ hlog (by linarith only [hl]) B) (by positivity)
    (Real.rpow_nonneg (hUpos.le.trans hUT) q)

private lemma powerLogModel_scale_lower {r q U : ℝ} {B : ℕ}
    (hr : 1 ≤ r) (hU : 1 ≤ U) :
    r ^ q * powerLogModel q B U ≤ powerLogModel q B (r * U) := by
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hUscale : U ≤ r * U := le_mul_of_one_le_left hUpos.le hr
  have hl := Real.log_le_log hUpos hUscale
  have hl0 : 0 ≤ 1 + Real.log U := by linarith only [Real.log_nonneg hU]
  dsimp [powerLogModel]
  rw [Real.mul_rpow hrpos.le hUpos.le, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 (by linarith only [hl]) B)
    (by positivity)

private lemma powerLogModel_scale_upper {r q T : ℝ} {B : ℕ}
    (hr : 1 ≤ r) (hT : 1 ≤ T) :
    powerLogModel q B (r * T) ≤
      (r ^ q * (1 + Real.log r) ^ B) * powerLogModel q B T := by
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hlr := Real.log_nonneg hr
  have hlt := Real.log_nonneg hT
  have hlog : 1 + Real.log (r * T) ≤ (1 + Real.log r) * (1 + Real.log T) := by
    rw [Real.log_mul hrpos.ne' hTpos.ne']
    nlinarith only [mul_nonneg hlr hlt]
  have hlog0 : 0 ≤ 1 + Real.log (r * T) := by
    rw [Real.log_mul hrpos.ne' hTpos.ne']
    linarith only [hlr, hlt]
  calc
    _ ≤ (r * T) ^ q * ((1 + Real.log r) * (1 + Real.log T)) ^ B :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog B) (by positivity)
    _ = _ := by rw [Real.mul_rpow hrpos.le hTpos.le, mul_pow]; dsimp [powerLogModel]; ring

/-- A monotone nonnegative count with a geometric shell recurrence and a
positive power exponent has the same global power and logarithmic degree.
This is an elementary summation theorem, not an analytic hypothesis. -/
theorem exists_eventually_powerLog_bound_of_geometric_step
    {F : ℝ → ℝ} {r q C : ℝ} {B : ℕ}
    (hF : Monotone F) (hF0 : ∀ T, 0 ≤ F T)
    (hr : 1 < r) (hq : 0 < q) (hC : 0 < C)
    (hstep : ∀ᶠ U : ℝ in atTop,
      F (r * U) ≤ F U + C * U ^ q * (1 + Real.log U) ^ B) :
    ∃ K > (0 : ℝ), ∀ᶠ T : ℝ in atTop,
      F T ≤ K * T ^ q * (1 + Real.log T) ^ B := by
  obtain ⟨a0, ha0⟩ := eventually_atTop.1 hstep
  let a := max a0 1
  have ha : 1 ≤ a := le_max_right _ _
  have hapos : 0 < a := zero_lt_one.trans_le ha
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hrq : 1 < r ^ q := Real.one_lt_rpow hr hq
  let D := F a + C / (r ^ q - 1) + 1
  have hden : 0 < r ^ q - 1 := sub_pos.mpr hrq
  have hD : 0 < D := by
    have := hF0 a
    dsimp [D]
    positivity
  have hDF : F a ≤ D := by
    have hcdiv : 0 ≤ C / (r ^ q - 1) := div_nonneg hC.le hden.le
    dsimp [D]
    linarith only [hcdiv]
  have hDstep : D + C ≤ D * r ^ q := by
    have hmul : C / (r ^ q - 1) * (r ^ q - 1) = C :=
      div_mul_cancel₀ _ hden.ne'
    have hf : 0 ≤ (F a + 1) * (r ^ q - 1) :=
      mul_nonneg (by linarith only [hF0 a]) hden.le
    dsimp [D]
    nlinarith only [hmul, hf]
  have hgrid : ∀ n : ℕ, F (a * r ^ n) ≤ D * powerLogModel q B (a * r ^ n) := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, mul_one]
      exact hDF.trans (le_mul_of_one_le_right hD.le (one_le_powerLogModel hq.le ha))
    | succ n ih =>
      have han : a ≤ a * r ^ n := le_mul_of_one_le_right hapos.le (one_le_pow₀ hr.le)
      have han1 : 1 ≤ a * r ^ n := ha.trans han
      have hrec := ha0 (a * r ^ n) ((le_max_left a0 1).trans han)
      have heq : a * r ^ (n + 1) = r * (a * r ^ n) := by rw [pow_succ]; ring
      rw [heq]
      calc
        _ ≤ F (a * r ^ n) + C * powerLogModel q B (a * r ^ n) := by
          simpa only [powerLogModel, mul_assoc] using hrec
        _ ≤ (D + C) * powerLogModel q B (a * r ^ n) := by
          nlinarith only [ih]
        _ ≤ (D * r ^ q) * powerLogModel q B (a * r ^ n) :=
          mul_le_mul_of_nonneg_right hDstep (powerLogModel_nonneg han1)
        _ ≤ D * powerLogModel q B (r * (a * r ^ n)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (powerLogModel_scale_lower hr.le han1) hD.le
  refine ⟨D * (r ^ q * (1 + Real.log r) ^ B), ?_, ?_⟩
  · have : 0 < 1 + Real.log r := by linarith only [Real.log_nonneg hr.le]
    positivity
  filter_upwards [eventually_ge_atTop a] with T hT
  have hT1 : 1 ≤ T := ha.trans hT
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near ((one_le_div hapos).mpr hT) hr
  have hlow : a * r ^ n ≤ T := by
    have := (le_div_iff₀ hapos).mp hn
    simpa only [mul_comm] using this
  have hhigh : T ≤ a * r ^ (n + 1) := by
    have := (div_lt_iff₀ hapos).mp hn'
    simpa only [mul_comm] using this.le
  have hnext : a * r ^ (n + 1) ≤ r * T := by
    calc
      _ = r * (a * r ^ n) := by rw [pow_succ]; ring
      _ ≤ r * T := mul_le_mul_of_nonneg_left hlow hrpos.le
  have han1 : 1 ≤ a * r ^ (n + 1) :=
    ha.trans (le_mul_of_one_le_right hapos.le (one_le_pow₀ hr.le))
  calc
    F T ≤ F (a * r ^ (n + 1)) := hF hhigh
    _ ≤ D * powerLogModel q B (a * r ^ (n + 1)) := hgrid _
    _ ≤ D * powerLogModel q B (r * T) :=
      mul_le_mul_of_nonneg_left (powerLogModel_mono hq.le han1 hnext) hD.le
    _ ≤ D * ((r ^ q * (1 + Real.log r) ^ B) * powerLogModel q B T) :=
      mul_le_mul_of_nonneg_left (powerLogModel_scale_upper hr.le hT1) hD.le
    _ = _ := by dsimp [powerLogModel]; ring

end PrimeNumberTheorem
