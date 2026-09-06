import HardyTheorem.SelbergFirstMomentParameter

open Filter

namespace HardyTheorem

/-!
# Final fixed parameters for the Selberg moment assembly

The S2--S4 specialization uses `delta=1/T`,
`X=floor(T^(1/32))`, and the logarithmic window
`H=2*pi/log(X^a)`.  This file collects the elementary eventual inequalities
needed to apply all three moment estimates with the same parameters.
-/

noncomputable def selbergMomentWindow (a T : ℝ) : ℝ :=
  2 * Real.pi /
    Real.log ((selbergFirstMomentCutoff T : ℝ) ^ a)

/-- The floor in `X=floor(T^(1/32))` loses at most a factor two, so its
logarithm retains at least `1/64` of `log T` eventually. -/
theorem eventually_log_div_sixtyFour_le_log_selbergFirstMomentCutoff :
    ∀ᶠ T : ℝ in atTop,
      0 < T ∧
      Real.log T / 64 ≤ Real.log (selbergFirstMomentCutoff T : ℝ) ∧
      (selbergFirstMomentCutoff T : ℝ) ≤ T ^ (1 / 32 : ℝ) := by
  have hpow : ∀ᶠ T : ℝ in atTop,
      (4 : ℝ) ≤ T ^ (1 / 32 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 32)).eventually_ge_atTop 4
  have hlog : ∀ᶠ T : ℝ in atTop,
      64 * Real.log 2 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually_ge_atTop (64 * Real.log 2)
  have hTone : ∀ᶠ T : ℝ in atTop, (1 : ℝ) ≤ T := eventually_ge_atTop 1
  filter_upwards [hpow, hlog, hTone] with T hpowT hlogT hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hypowpos : 0 < T ^ (1 / 32 : ℝ) :=
    Real.rpow_pos_of_pos hTpos _
  have hfloorLower : T ^ (1 / 32 : ℝ) / 2 ≤
      (selbergFirstMomentCutoff T : ℝ) := by
    unfold selbergFirstMomentCutoff
    have hlt := Nat.sub_one_lt_floor (T ^ (1 / 32 : ℝ))
    have hhalf : T ^ (1 / 32 : ℝ) / 2 ≤
        T ^ (1 / 32 : ℝ) - 1 := by linarith
    exact hhalf.trans hlt.le
  have hlogLower :
      Real.log (T ^ (1 / 32 : ℝ) / 2) ≤
        Real.log (selbergFirstMomentCutoff T : ℝ) :=
    Real.log_le_log (div_pos hypowpos (by norm_num)) hfloorLower
  have hlogPower : Real.log (T ^ (1 / 32 : ℝ)) =
      (1 / 32 : ℝ) * Real.log T := Real.log_rpow hTpos _
  have hlogFloor : Real.log T / 64 ≤
      Real.log (selbergFirstMomentCutoff T : ℝ) := by
    rw [Real.log_div hypowpos.ne' (by norm_num), hlogPower] at hlogLower
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have hupper : (selbergFirstMomentCutoff T : ℝ) ≤
      T ^ (1 / 32 : ℝ) := by
    unfold selbergFirstMomentCutoff
    exact Nat.floor_le (Real.rpow_nonneg hTpos.le _)
  exact ⟨hTpos, hlogFloor, hupper⟩

/-- For every fixed positive frequency parameter `a`, all elementary range
conditions of S2--S4 hold eventually for the final Selberg parameters. -/
theorem eventually_selbergMomentParameter_conditions
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ T : ℝ in atTop,
      0 < 1 / T ∧
      1 / T ≤ 1 ∧
      1 / T < Real.pi / 2 ∧
      2 ≤ selbergFirstMomentCutoff T ∧
      Real.exp 1 ≤ (selbergFirstMomentCutoff T : ℝ) ∧
      (selbergFirstMomentCutoff T : ℝ) ≤
        (1 / T) ^ (-(1 / 32 : ℝ)) ∧
      2 ≤ Real.log ((selbergFirstMomentCutoff T : ℝ) ^ a) ∧
      2 ≤ Real.log ((1 / T) ^ (-2 : ℝ)) ∧
      Real.log (1 / (1 / T)) /
          Real.log (selbergFirstMomentCutoff T : ℝ) ≤ 64 ∧
      0 < selbergMomentWindow a T ∧
      selbergMomentWindow a T ≤ T / 2 := by
  have hbase :=
    eventually_log_div_sixtyFour_le_log_selbergFirstMomentCutoff
  have hlogLarge : ∀ᶠ T : ℝ in atTop,
      128 / a ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually_ge_atTop (128 / a)
  have hpowExp : ∀ᶠ T : ℝ in atTop,
      Real.exp 1 + 1 ≤ T ^ (1 / 32 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 32)).eventually_ge_atTop
      (Real.exp 1 + 1)
  have hTlarge : ∀ᶠ T : ℝ in atTop,
      max (2 * Real.pi) (Real.exp 1) ≤ T :=
    eventually_ge_atTop (max (2 * Real.pi) (Real.exp 1))
  filter_upwards [hbase, hlogLarge, hpowExp, hTlarge]
    with T hbaseT hlogLargeT hpowExpT hTlargeT
  rcases hbaseT with ⟨hTpos, hlogFloor, hXupper⟩
  have hTexp : Real.exp 1 ≤ T :=
    (le_max_right _ _).trans hTlargeT
  have hTone : 1 ≤ T := by
    linarith [Real.exp_one_gt_d9]
  have hdeltaPos : 0 < 1 / T := one_div_pos.mpr hTpos
  have hdeltaOne : 1 / T ≤ 1 := by
    rw [div_le_iff₀ hTpos]
    simpa using hTone
  have hdeltaPi : 1 / T < Real.pi / 2 := by
    calc
      1 / T ≤ 1 := hdeltaOne
      _ < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hXexp : Real.exp 1 ≤ (selbergFirstMomentCutoff T : ℝ) := by
    unfold selbergFirstMomentCutoff
    exact (by
      have hlt := Nat.sub_one_lt_floor (T ^ (1 / 32 : ℝ))
      linarith)
  have hXtwo : 2 ≤ selbergFirstMomentCutoff T := by
    have heTwo : (2 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
    exact_mod_cast heTwo.trans hXexp
  have hXpow : (selbergFirstMomentCutoff T : ℝ) ≤
      (1 / T) ^ (-(1 / 32 : ℝ)) := by
    calc
      (selbergFirstMomentCutoff T : ℝ) ≤ T ^ (1 / 32 : ℝ) := hXupper
      _ = (1 / T) ^ (-(1 / 32 : ℝ)) := by
        rw [Real.rpow_neg_eq_inv_rpow]
        congr 1
        field_simp
  have hlogTpos : 0 < Real.log T :=
    Real.log_pos (by linarith [Real.exp_one_gt_d9])
  have hlogXpos : 0 < Real.log (selbergFirstMomentCutoff T : ℝ) := by
    exact Real.log_pos (lt_of_lt_of_le (by norm_num) hXexp)
  have hlogXa : 2 ≤
      Real.log ((selbergFirstMomentCutoff T : ℝ) ^ a) := by
    rw [Real.log_rpow (by positivity : (0 : ℝ) < selbergFirstMomentCutoff T) a]
    have hscaled := mul_le_mul_of_nonneg_left hlogFloor ha.le
    have haDiv : a * (Real.log T / 64) ≥ 2 := by
      have haPos : 0 < a := ha
      have := mul_le_mul_of_nonneg_left hlogLargeT ha.le
      field_simp [ha.ne'] at this ⊢
      nlinarith
    linarith
  have hdeltaPow : (1 / T) ^ (-2 : ℝ) = T ^ (2 : ℝ) := by
    rw [one_div, Real.rpow_neg_eq_inv_rpow, inv_inv]
  have hlogDelta : 2 ≤ Real.log ((1 / T) ^ (-2 : ℝ)) := by
    rw [hdeltaPow, Real.log_rpow hTpos]
    have honeLog : 1 ≤ Real.log T :=
      (Real.le_log_iff_exp_le hTpos).2 hTexp
    nlinarith
  have hlogRatio :
      Real.log (1 / (1 / T)) /
          Real.log (selbergFirstMomentCutoff T : ℝ) ≤ 64 := by
    have hinv : 1 / (1 / T) = T := by field_simp
    rw [hinv]
    exact (div_le_iff₀ hlogXpos).2 (by nlinarith [hlogFloor])
  have hwindowPos : 0 < selbergMomentWindow a T := by
    unfold selbergMomentWindow
    exact div_pos (mul_pos (by norm_num) Real.pi_pos) (by linarith)
  have hwindowLe : selbergMomentWindow a T ≤ T / 2 := by
    have hwindowPi : selbergMomentWindow a T ≤ Real.pi := by
      unfold selbergMomentWindow
      exact (div_le_iff₀ (by linarith :
        0 < Real.log ((selbergFirstMomentCutoff T : ℝ) ^ a))).2 (by
          nlinarith [Real.pi_pos])
    have hTwoPiT : 2 * Real.pi ≤ T :=
      (le_max_left _ _).trans hTlargeT
    linarith
  exact ⟨hdeltaPos, hdeltaOne, hdeltaPi, hXtwo, hXexp, hXpow,
    hlogXa, hlogDelta, hlogRatio, hwindowPos, hwindowLe⟩

end HardyTheorem
