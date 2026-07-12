import PrimeNumberTheorem.LSeriesPerron

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction BigOperators LSeries.notation

namespace PrimeNumberTheorem

lemma perronTerm_eq_kernel
    {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) (c w : ℝ) :
    (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              (perronLine c w) ^ 2 =
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        (Complex.exp (perronLine c w * Real.log (x / n)) /
          (perronLine c w) ^ 2) := by
  rw [LSeries.term_of_ne_zero hn]
  have hpow :
      (x : ℂ) ^ perronLine c w / (n : ℂ) ^ perronLine c w =
        Complex.exp (perronLine c w * Real.log (x / n)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
    rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
    rw [div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add]
    rw [← Complex.ofReal_log hx.le, ← Complex.natCast_log]
    rw [Real.log_div hx.ne' (Nat.cast_ne_zero.mpr hn)]
    congr 1
    push_cast
    ring
  rw [show (x : ℂ) ^ perronLine c w *
        ((ArithmeticFunction.vonMangoldt n : ℂ) /
          (n : ℂ) ^ perronLine c w) /
          (perronLine c w) ^ 2 =
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        (((x : ℂ) ^ perronLine c w / (n : ℂ) ^ perronLine c w) /
          (perronLine c w) ^ 2) by ring]
  rw [hpow]

lemma norm_intervalIntegral_perronTerm_sub_max_le
    {x c W : ℝ} (hx : 0 < x) (hc : 0 < c) (hW : 0 < W) (n : ℕ) :
    ‖(∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              (perronLine c w) ^ 2) -
        (vonMangoldt n : ℂ) *
          ((max (Real.log (x / n)) 0 : ℝ) : ℂ)‖ ≤
      vonMangoldt n * (x / n) ^ c / (2 * Real.pi ^ 2 * W) := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term, vonMangoldt_eq_mathlib]
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hv_nonneg : 0 ≤ vonMangoldt n := by
    rw [vonMangoldt_eq_mathlib]
    exact ArithmeticFunction.vonMangoldt_nonneg
  have hinter :
      (∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              (perronLine c w) ^ 2) =
        (vonMangoldt n : ℂ) *
          (∫ w : ℝ in (-W)..W,
            Complex.exp (perronLine c w * Real.log (x / n)) /
              (perronLine c w) ^ 2) := by
    calc
      _ = ∫ w : ℝ in (-W)..W,
          (vonMangoldt n : ℂ) *
            (Complex.exp (perronLine c w * Real.log (x / n)) /
              (perronLine c w) ^ 2) := by
        apply intervalIntegral.integral_congr
        intro w hw
        dsimp
        rw [perronTerm_eq_kernel hx hn, vonMangoldt_eq_mathlib]
      _ = _ := intervalIntegral.integral_const_mul
        (vonMangoldt n : ℂ)
        (fun w : ℝ => Complex.exp (perronLine c w * Real.log (x / n)) /
          (perronLine c w) ^ 2)
  rw [hinter, ← mul_sub, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hv_nonneg]
  calc
    vonMangoldt n *
        ‖(∫ w : ℝ in (-W)..W,
            Complex.exp (perronLine c w * Real.log (x / n)) /
              (perronLine c w) ^ 2) -
          ((max (Real.log (x / n)) 0 : ℝ) : ℂ)‖ ≤
        vonMangoldt n *
          (Real.exp (c * Real.log (x / n)) /
            (2 * Real.pi ^ 2 * W)) := by
      apply mul_le_mul_of_nonneg_left _ hv_nonneg
      simpa [perronLine] using
        norm_truncated_secondOrderPerron_sub_max_le
          (c := c) (u := Real.log (x / n)) (W := W) hc hW
    _ = vonMangoldt n * (x / n) ^ c /
          (2 * Real.pi ^ 2 * W) := by
      rw [Real.rpow_def_of_pos (div_pos hx hn_pos)]
      ring

/-- Complete finite-height second-order Perron formula on the right of
`Re(s) = 1`, with the full von Mangoldt Dirichlet series and an explicit
summable `1/W` error. -/
theorem norm_truncated_neg_logDeriv_riemannZeta_sub_smoothedPsi_le
    {x c W : ℝ} (hx : 0 < x) (hc : 1 < c) (hW : 0 < W) :
    ‖(∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          (-deriv riemannZeta (perronLine c w) /
            riemannZeta (perronLine c w)) /
              (perronLine c w) ^ 2) -
        (smoothedChebyshevPsi x : ℂ)‖ ≤
      ∑' n : ℕ,
        vonMangoldt n * (x / n) ^ c / (2 * Real.pi ^ 2 * W) := by
  let A : ℕ → ℂ := fun n => ∫ w : ℝ in (-W)..W,
    (x : ℂ) ^ perronLine c w *
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (perronLine c w) n /
          (perronLine c w) ^ 2
  let M : ℕ → ℂ := fun n =>
    (vonMangoldt n : ℂ) * ((max (Real.log (x / n)) 0 : ℝ) : ℂ)
  let B : ℕ → ℝ := fun n =>
    vonMangoldt n * (x / n) ^ c / (2 * Real.pi ^ 2 * W)
  have hc_pos : 0 < c := one_pos.trans hc
  have hden_pos : 0 < 2 * Real.pi ^ 2 * W := by positivity
  have hnorm_summable : Summable fun n =>
      ‖LSeries.term
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖ := by
    have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := (c : ℂ)) (by simpa using hc)
    rw [LSeriesSummable, ← summable_norm_iff] at hs
    simpa using hs
  have hB_eq (n : ℕ) : B n =
      (x ^ c / (2 * Real.pi ^ 2 * W)) *
        ‖LSeries.term
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖ := by
    by_cases hn : n = 0
    · subst n
      simp [B, LSeries.term, vonMangoldt_eq_mathlib]
    · have hn_pos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      dsimp [B]
      rw [LSeries.norm_term_eq, vonMangoldt_eq_mathlib,
        Real.div_rpow hx.le hn_pos.le]
      simp only [hn, if_false, Complex.ofReal_re]
      rw [norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      field_simp
  have hB_summable : Summable B := by
    rw [show B = fun n =>
      (x ^ c / (2 * Real.pi ^ 2 * W)) *
        ‖LSeries.term
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖ by
      funext n
      exact hB_eq n]
    exact Summable.mul_left _ hnorm_summable
  have hpoint (n : ℕ) : ‖A n - M n‖ ≤ B n := by
    simpa [A, M, B] using
      norm_intervalIntegral_perronTerm_sub_max_le hx hc_pos hW n
  have hM_zero : ∀ n ∉ Finset.Ico 1 (Nat.floor x + 1), M n = 0 := by
    intro n hnS
    by_cases hn0 : n = 0
    · subst n
      simp [M, vonMangoldt_eq_mathlib]
    · have hn_lower : Nat.floor x + 1 ≤ n := by
        have : ¬(1 ≤ n ∧ n < Nat.floor x + 1) := by
          simpa [Finset.mem_Ico] using hnS
        omega
      have hn_pos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
      have hxn : x < (n : ℝ) :=
        (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hn_lower)
      have hratio_nonneg : 0 ≤ x / (n : ℝ) := div_nonneg hx.le hn_pos.le
      have hratio_le : x / (n : ℝ) ≤ 1 := (div_le_one₀ hn_pos).2 hxn.le
      simp [M, max_eq_right (Real.log_nonpos hratio_nonneg hratio_le)]
  have hM_summable : Summable M := summable_of_ne_finset_zero hM_zero
  have hM_tsum : (∑' n, M n) = (smoothedChebyshevPsi x : ℂ) := by
    rw [tsum_eq_sum hM_zero]
    simp only [M, ← Complex.ofReal_mul]
    rw [← Complex.ofReal_sum,
      sum_vonMangoldt_max_log_div_eq_smoothedChebyshevPsi
        x hx (Nat.floor x + 1) (Nat.lt_succ_self _)]
  have hE_summable : Summable fun n => A n - M n :=
    hB_summable.of_norm_bounded hpoint
  have hA_summable : Summable A := by
    simpa [sub_add_cancel] using hE_summable.add hM_summable
  rw [intervalIntegral_neg_logDeriv_riemannZeta_eq_vonMangoldt_tsum hx hc]
  change ‖(∑' n, A n) - (smoothedChebyshevPsi x : ℂ)‖ ≤ ∑' n, B n
  rw [← hM_tsum, ← hA_summable.tsum_sub hM_summable]
  exact tsum_of_norm_bounded hB_summable.hasSum hpoint

end PrimeNumberTheorem
