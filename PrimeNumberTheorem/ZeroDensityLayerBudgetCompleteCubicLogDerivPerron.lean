import PrimeNumberTheorem.CompletePerron
import PrimeNumberTheorem.ZeroDensityLayerBudgetVonMangoldtSecondRieszPerron

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction BigOperators LSeries.notation

namespace PrimeNumberTheorem

theorem intervalIntegral_vonMangoldt_LSeries_thirdOrder_eq_tsum
    {x c W : ℝ} (hx : 0 < x) (hc : 1 < c) :
    (∫ w : ℝ in (-W)..W,
      (x : ℂ) ^ perronLine c w *
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (perronLine c w) /
          (perronLine c w) ^ 3) =
      ∑' n : ℕ, ∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              (perronLine c w) ^ 3 := by
  let coeff : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let F : ℕ → ℝ → ℂ := fun n w =>
    (x : ℂ) ^ perronLine c w * LSeries.term coeff (perronLine c w) n /
      (perronLine c w) ^ 3
  let f : ℝ → ℂ := fun w =>
    (x : ℂ) ^ perronLine c w * LSeries coeff (perronLine c w) /
      (perronLine c w) ^ 3
  let B : ℕ → ℝ := fun n =>
    x ^ c / c ^ 3 * ‖LSeries.term coeff (c : ℂ) n‖
  have hc_pos : 0 < c := one_pos.trans hc
  have hline_re (w : ℝ) : (perronLine c w).re = c := by simp [perronLine]
  have hline_ne (w : ℝ) : perronLine c w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hline_re] at hre
    simp at hre
    linarith
  have hnorm_summable : Summable fun n =>
      ‖LSeries.term coeff (c : ℂ) n‖ := by
    have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := (c : ℂ)) (by simpa using hc)
    rw [LSeriesSummable, ← summable_norm_iff] at hs
    simpa [coeff] using hs
  have hB_summable : Summable B :=
    Summable.mul_left (x ^ c / c ^ 3) hnorm_summable
  have hF_meas : ∀ n, AEStronglyMeasurable (F n)
      (volume.restrict (uIoc (-W) W)) := by
    intro n
    apply Continuous.aestronglyMeasurable
    by_cases hn : n = 0
    · subst n
      simpa [F] using (continuous_const : Continuous fun _ : ℝ => (0 : ℂ))
    · have hline_cont : Continuous (perronLine c) := by
        unfold perronLine
        fun_prop
      have hxpow_cont : Continuous fun w : ℝ => (x : ℂ) ^ perronLine c w :=
        hline_cont.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
      have hnpow_cont : Continuous fun w : ℝ => (n : ℂ) ^ perronLine c w :=
        hline_cont.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn))
      have hterm_cont : Continuous fun w : ℝ =>
          coeff n / (n : ℂ) ^ perronLine c w :=
        continuous_const.div₀ hnpow_cont (fun w =>
          cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn)))
      have hden_cont : Continuous fun w : ℝ => (perronLine c w) ^ 3 :=
        hline_cont.pow 3
      simpa [F, LSeries.term_of_ne_zero hn] using
        (hxpow_cont.mul hterm_cont).div₀ hden_cont
          (fun w => pow_ne_zero 3 (hline_ne w))
  have hbound : ∀ n w, ‖F n w‖ ≤ B n := by
    intro n w
    have hterm : ‖LSeries.term coeff (perronLine c w) n‖ =
        ‖LSeries.term coeff (c : ℂ) n‖ := by
      simp [LSeries.norm_term_eq, hline_re]
    have hc_norm : c ≤ ‖perronLine c w‖ := by
      have h := abs_re_le_norm (perronLine c w)
      rw [hline_re, abs_of_pos hc_pos] at h
      exact h
    have hline_cube : c ^ 3 ≤ ‖perronLine c w‖ ^ 3 := by gcongr
    have hnum_nonneg : 0 ≤ x ^ c * ‖LSeries.term coeff (c : ℂ) n‖ :=
      mul_nonneg (Real.rpow_nonneg hx.le c) (norm_nonneg _)
    dsimp [F, B]
    rw [norm_div, norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx,
      hline_re, hterm]
    calc
      x ^ c * ‖LSeries.term coeff (c : ℂ) n‖ / ‖perronLine c w‖ ^ 3 ≤
          (x ^ c * ‖LSeries.term coeff (c : ℂ) n‖) / c ^ 3 :=
        div_le_div_of_nonneg_left hnum_nonneg (by positivity) hline_cube
      _ = x ^ c / c ^ 3 * ‖LSeries.term coeff (c : ℂ) n‖ := by ring
  have hlim : ∀ w, HasSum (fun n => F n w) (f w) := by
    intro w
    have hs := (ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := perronLine c w) (by simpa [hline_re] using hc)).LSeriesHasSum
    have hmul := hs.mul_left
      ((x : ℂ) ^ perronLine c w / (perronLine c w) ^ 3)
    simpa [F, f, coeff, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hHas := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := -W) (b := W) (F := F) (f := f)
    (fun n _ => B n) hF_meas
    (fun n => ae_of_all _ fun w hw => hbound n w)
    (ae_of_all _ fun w hw => hB_summable)
    intervalIntegrable_const
    (ae_of_all _ fun w hw => hlim w)
  simpa [F, f, coeff] using hHas.tsum_eq.symm

theorem intervalIntegral_negLogDeriv_thirdOrder_eq_vonMangoldt_tsum
    {x c W : ℝ} (hx : 0 < x) (hc : 1 < c) :
    (∫ w : ℝ in (-W)..W,
      (x : ℂ) ^ perronLine c w *
        (-deriv riemannZeta (perronLine c w) /
          riemannZeta (perronLine c w)) /
            (perronLine c w) ^ 3) =
      ∑' n : ℕ, ∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              (perronLine c w) ^ 3 := by
  rw [← intervalIntegral_vonMangoldt_LSeries_thirdOrder_eq_tsum hx hc]
  apply intervalIntegral.integral_congr
  intro w hw
  dsimp
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div]
  simp [perronLine, hc]

lemma perronTerm_thirdOrder_eq_kernel
    {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) (c w : ℝ) :
    (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              (perronLine c w) ^ 3 =
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        (exp (perronLine c w * Real.log (x / n)) /
          (perronLine c w) ^ 3) := by
  have h := congrArg (fun z : ℂ => z / perronLine c w)
    (perronTerm_eq_kernel hx hn c w)
  convert h using 1 <;> ring

lemma norm_intervalIntegral_perronTerm_thirdOrder_sub_half_sq_max_le
    {x c W : ℝ} (hx : 0 < x) (hc : 0 < c) (hW : 0 < W) (n : ℕ) :
    ‖(∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              (perronLine c w) ^ 3) -
        (vonMangoldt n : ℂ) *
          (((max (Real.log (x / n)) 0) ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      vonMangoldt n * (x / n) ^ c /
        (8 * Real.pi ^ 3 * W ^ 2) := by
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
              (perronLine c w) ^ 3) =
        (vonMangoldt n : ℂ) *
          (∫ w : ℝ in (-W)..W,
            exp (perronLine c w * Real.log (x / n)) /
              (perronLine c w) ^ 3) := by
    calc
      _ = ∫ w : ℝ in (-W)..W,
          (vonMangoldt n : ℂ) *
            (exp (perronLine c w * Real.log (x / n)) /
              (perronLine c w) ^ 3) := by
        apply intervalIntegral.integral_congr
        intro w hw
        dsimp
        rw [perronTerm_thirdOrder_eq_kernel hx hn, vonMangoldt_eq_mathlib]
      _ = _ := intervalIntegral.integral_const_mul
        (vonMangoldt n : ℂ)
        (fun w : ℝ => exp (perronLine c w * Real.log (x / n)) /
          (perronLine c w) ^ 3)
  rw [hinter, ← mul_sub, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hv_nonneg]
  calc
    vonMangoldt n *
        ‖(∫ w : ℝ in (-W)..W,
            exp (perronLine c w * Real.log (x / n)) /
              (perronLine c w) ^ 3) -
          (((max (Real.log (x / n)) 0) ^ 2 / 2 : ℝ) : ℂ)‖ ≤
        vonMangoldt n *
          (Real.exp (c * Real.log (x / n)) /
            (8 * Real.pi ^ 3 * W ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hv_nonneg
      simpa [perronLine] using
        norm_truncated_thirdOrderPerron_sub_half_sq_max_le
          (c := c) (u := Real.log (x / n)) (W := W) hc hW
    _ = vonMangoldt n * (x / n) ^ c /
          (8 * Real.pi ^ 3 * W ^ 2) := by
      rw [Real.rpow_def_of_pos (div_pos hx hn_pos)]
      ring

/-- Complete finite-height cubic Perron formula for the actual zeta logarithmic
derivative and the von Mangoldt second Riesz mean. -/
theorem norm_truncated_negLogDeriv_thirdOrder_sub_secondRieszPsi_le
    {x c W : ℝ} (hx : 0 < x) (hc : 1 < c) (hW : 0 < W) :
    ‖(∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          (-deriv riemannZeta (perronLine c w) /
            riemannZeta (perronLine c w)) /
              (perronLine c w) ^ 3) -
        (secondRieszChebyshevPsi x : ℂ)‖ ≤
      ∑' n : ℕ,
        vonMangoldt n * (x / n) ^ c /
          (8 * Real.pi ^ 3 * W ^ 2) := by
  let A : ℕ → ℂ := fun n => ∫ w : ℝ in (-W)..W,
    (x : ℂ) ^ perronLine c w *
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (perronLine c w) n /
          (perronLine c w) ^ 3
  let M : ℕ → ℂ := fun n =>
    (vonMangoldt n : ℂ) *
      (((max (Real.log (x / n)) 0) ^ 2 / 2 : ℝ) : ℂ)
  let B : ℕ → ℝ := fun n =>
    vonMangoldt n * (x / n) ^ c /
      (8 * Real.pi ^ 3 * W ^ 2)
  have hc_pos : 0 < c := one_pos.trans hc
  have hden_pos : 0 < 8 * Real.pi ^ 3 * W ^ 2 := by positivity
  have hnorm_summable : Summable fun n =>
      ‖LSeries.term
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖ := by
    have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := (c : ℂ)) (by simpa using hc)
    rw [LSeriesSummable, ← summable_norm_iff] at hs
    simpa using hs
  have hB_eq (n : ℕ) : B n =
      (x ^ c / (8 * Real.pi ^ 3 * W ^ 2)) *
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
      (x ^ c / (8 * Real.pi ^ 3 * W ^ 2)) *
        ‖LSeries.term
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖ by
      funext n
      exact hB_eq n]
    exact Summable.mul_left _ hnorm_summable
  have hpoint (n : ℕ) : ‖A n - M n‖ ≤ B n := by
    simpa [A, M, B] using
      norm_intervalIntegral_perronTerm_thirdOrder_sub_half_sq_max_le
        hx hc_pos hW n
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
  have hM_tsum : (∑' n, M n) = (secondRieszChebyshevPsi x : ℂ) := by
    rw [tsum_eq_sum hM_zero]
    rw [← sum_vonMangoldt_half_sq_max_log_div_eq_secondRieszChebyshevPsi x hx,
      Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [M]
    push_cast
    ring
  have hE_summable : Summable fun n => A n - M n :=
    hB_summable.of_norm_bounded hpoint
  have hA_summable : Summable A := by
    simpa [sub_add_cancel] using hE_summable.add hM_summable
  rw [intervalIntegral_negLogDeriv_thirdOrder_eq_vonMangoldt_tsum hx hc]
  change ‖(∑' n, A n) - (secondRieszChebyshevPsi x : ℂ)‖ ≤ ∑' n, B n
  rw [← hM_tsum, ← hA_summable.tsum_sub hM_summable]
  exact tsum_of_norm_bounded hB_summable.hasSum hpoint

end PrimeNumberTheorem
