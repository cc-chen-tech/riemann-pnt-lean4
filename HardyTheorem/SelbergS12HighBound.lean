import HardyTheorem.SelbergS12HighTransfer

open Complex

namespace HardyTheorem

/-!
# Selberg S12: linear high-height bound on the one-line

We choose the horizontal length constant with slack, `a = 1 / (4(C+1))`.
The Grönwall exponential then contributes at most `|t|^(1/4)`, while the
right-line logarithm contributes another `|t|^(1/4)`.
-/

theorem exists_norm_inv_riemannZeta_oneLine_le_mul_abs_high :
    ∃ A T : ℝ, 0 ≤ A ∧ 2 ≤ T ∧
      ∀ t : ℝ, T ≤ |t| →
        ‖(riemannZeta ((1 : ℂ) + I * t))⁻¹‖ ≤ A * |t| := by
  rcases exists_norm_inv_riemannZeta_oneLine_le_gronwall with
    ⟨C, T, hC, hT, htransfer⟩
  let a : ℝ := 1 / (4 * (C + 1))
  let A : ℝ := 1 + 4 / a
  let T' : ℝ := max T (Real.exp a)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hT' : 2 ≤ T' := hT.trans (le_max_left _ _)
  refine ⟨A, T', hA, hT', ?_⟩
  intro t ht
  let x : ℝ := |t|
  let L : ℝ := Real.log x
  let q : ℝ := x ^ (1 / 4 : ℝ)
  have hTx : T ≤ x := (le_max_left T (Real.exp a)).trans ht
  have hexpa : Real.exp a ≤ x := (le_max_right T (Real.exp a)).trans ht
  have hx2 : 2 ≤ x := hT.trans hTx
  have hx1 : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 2).trans hx2
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (lt_of_lt_of_le one_lt_two hx2)
  have haL : a ≤ L := by
    have h := Real.log_le_log (Real.exp_pos a) hexpa
    simpa [L] using h
  have hraw := htransfer a t ha (by simpa [L, x] using haL)
    (by simpa [x] using hTx)
  have hCa : C * a ≤ (1 / 4 : ℝ) := by
    dsimp [a]
    have hden : 0 < 4 * (C + 1) := by positivity
    rw [one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)).2
    nlinarith
  have hexponent :
      C * L ^ 2 * (a / L) = (C * a) * L := by
    field_simp [hLpos.ne']
  have hexp_le_q :
      Real.exp (C * L ^ 2 * (a / L)) ≤ q := by
    rw [hexponent]
    have hpow : (C * a) * L ≤ (1 / 4 : ℝ) * L :=
      mul_le_mul_of_nonneg_right hCa hLpos.le
    calc
      Real.exp ((C * a) * L) ≤ Real.exp ((1 / 4 : ℝ) * L) := by
        exact Real.exp_le_exp.mpr hpow
      _ = q := by
        dsimp [q]
        rw [Real.rpow_def_of_pos hxpos]
        congr 1
        dsimp [L]
        ring
  have hq_nonneg : 0 ≤ q := (Real.rpow_pos_of_pos hxpos _).le
  have hq_one : 1 ≤ q := Real.one_le_rpow hx1 (by norm_num)
  have hlog_q : L ≤ 4 * q := by
    have h := Real.log_le_rpow_div hxpos.le (by norm_num : 0 < (1 / 4 : ℝ))
    change L ≤ 4 * q
    simpa [L, q, mul_comm] using h
  have hbase : 1 + L / a ≤ A * q := by
    have hdiv : L / a ≤ (4 * q) / a :=
      div_le_div_of_nonneg_right hlog_q ha.le
    have hfoura : 0 ≤ 4 / a := by positivity
    dsimp [A]
    calc
      1 + L / a ≤ 1 + (4 * q) / a := add_le_add le_rfl hdiv
      _ = 1 + (4 / a) * q := by ring
      _ ≤ q + (4 / a) * q := add_le_add hq_one le_rfl
      _ = (1 + 4 / a) * q := by ring
  have hqq : q * q = x ^ (1 / 2 : ℝ) := by
    dsimp [q]
    rw [← Real.rpow_add hxpos]
    norm_num
  have hsqrt_le : x ^ (1 / 2 : ℝ) ≤ x :=
    Real.rpow_le_self_of_one_le hx1 (by norm_num)
  have hbase_nonneg : 0 ≤ 1 + L / a := by positivity
  calc
    ‖(riemannZeta ((1 : ℂ) + I * t))⁻¹‖ ≤
        (1 + L / a) * Real.exp (C * L ^ 2 * (a / L)) := by
      simpa [L, x] using hraw
    _ ≤ (A * q) * q :=
      mul_le_mul hbase hexp_le_q (Real.exp_pos _).le (mul_nonneg hA hq_nonneg)
    _ = A * (q * q) := by ring
    _ = A * x ^ (1 / 2 : ℝ) := by rw [hqq]
    _ ≤ A * x := mul_le_mul_of_nonneg_left hsqrt_le hA
    _ = A * |t| := by rfl

end HardyTheorem
