import PrimeNumberTheorem.FirstOrderPerron
import PrimeNumberTheorem.LSeriesPerron

set_option maxHeartbeats 800000

/-!
# Complete first-order Perron inversion for the von Mangoldt L-series

This module connects the conditionally convergent first-order Perron kernel to
the full von Mangoldt Dirichlet series.  On each finite vertical segment the
series-integral exchange is absolutely dominated.  The remaining limit in the
height variable is handled termwise with a summable Tannery majorant.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction BigOperators LSeries.notation

namespace PrimeNumberTheorem

/-- On a finite vertical segment to the right of absolute convergence, the
first-order Perron integral of the von Mangoldt L-series is its termwise
integral. -/
theorem intervalIntegral_vonMangoldt_LSeries_firstOrder_eq_tsum
    {x c W : ℝ} (hx : 0 < x) (hc : 1 < c) :
    (∫ w : ℝ in (-W)..W,
      (x : ℂ) ^ perronLine c w *
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (perronLine c w) /
            perronLine c w) =
      ∑' n : ℕ, ∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              perronLine c w := by
  let coeff : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let F : ℕ → ℝ → ℂ := fun n w =>
    (x : ℂ) ^ perronLine c w * LSeries.term coeff (perronLine c w) n /
      perronLine c w
  let f : ℝ → ℂ := fun w =>
    (x : ℂ) ^ perronLine c w * LSeries coeff (perronLine c w) /
      perronLine c w
  let B : ℕ → ℝ := fun n =>
    x ^ c / c * ‖LSeries.term coeff (c : ℂ) n‖
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
    Summable.mul_left (x ^ c / c) hnorm_summable
  have hF_meas : ∀ n, AEStronglyMeasurable (F n)
      (volume.restrict (Set.uIoc (-W) W)) := by
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
        continuous_const.div₀ hnpow_cont (fun _ =>
          cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn)))
      simpa [F, LSeries.term_of_ne_zero hn] using
        (hxpow_cont.mul hterm_cont).div₀ hline_cont hline_ne
  have hbound : ∀ n w, ‖F n w‖ ≤ B n := by
    intro n w
    have hterm : ‖LSeries.term coeff (perronLine c w) n‖ =
        ‖LSeries.term coeff (c : ℂ) n‖ := by
      simp [LSeries.norm_term_eq, hline_re]
    have hline_norm : c ≤ ‖perronLine c w‖ := by
      have hbase := abs_re_le_norm (perronLine c w)
      simpa [hline_re, abs_of_pos hc_pos] using hbase
    have hnum_nonneg : 0 ≤ x ^ c * ‖LSeries.term coeff (c : ℂ) n‖ :=
      mul_nonneg (Real.rpow_nonneg hx.le c) (norm_nonneg _)
    dsimp [F, B]
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
      hline_re, hterm]
    calc
      x ^ c * ‖LSeries.term coeff (c : ℂ) n‖ / ‖perronLine c w‖ ≤
          (x ^ c * ‖LSeries.term coeff (c : ℂ) n‖) / c :=
        div_le_div_of_nonneg_left hnum_nonneg hc_pos hline_norm
      _ = x ^ c / c * ‖LSeries.term coeff (c : ℂ) n‖ := by ring
  have hlim : ∀ w, HasSum (fun n => F n w) (f w) := by
    intro w
    have hs := (ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := perronLine c w) (by simpa [hline_re] using hc)).LSeriesHasSum
    have hmul := hs.mul_left ((x : ℂ) ^ perronLine c w / perronLine c w)
    simpa [F, f, coeff, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hHas := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := -W) (b := W) (F := F) (f := f)
    (fun n _ => B n) hF_meas
    (fun n => ae_of_all _ fun w _ => hbound n w)
    (ae_of_all _ fun _ _ => hB_summable)
    intervalIntegrable_const
    (ae_of_all _ fun w _ => hlim w)
  simpa [F, f, coeff] using hHas.tsum_eq.symm

/-- Finite-height first-order Perron series exchange in zeta logarithmic-
derivative notation. -/
theorem intervalIntegral_neg_logDeriv_riemannZeta_firstOrder_eq_vonMangoldt_tsum
    {x c W : ℝ} (hx : 0 < x) (hc : 1 < c) :
    (∫ w : ℝ in (-W)..W,
      (x : ℂ) ^ perronLine c w *
        (-deriv riemannZeta (perronLine c w) /
          riemannZeta (perronLine c w)) /
            perronLine c w) =
      ∑' n : ℕ, ∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              perronLine c w := by
  rw [← intervalIntegral_vonMangoldt_LSeries_firstOrder_eq_tsum hx hc]
  apply intervalIntegral.integral_congr
  intro w _hw
  dsimp
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div]
  simp [perronLine, hc]

/-- A single von Mangoldt first-order Perron term is the scalar multiple of
the normalized first-order kernel. -/
lemma firstOrderPerronTerm_eq_kernel
    {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) (c w : ℝ) :
    (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              perronLine c w =
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        (Complex.exp (perronLine c w * Real.log (x / n)) /
          perronLine c w) := by
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
          perronLine c w =
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        (((x : ℂ) ^ perronLine c w / (n : ℂ) ^ perronLine c w) /
          perronLine c w) by ring]
  rw [hpow]

/-- Integral form of `firstOrderPerronTerm_eq_kernel`. -/
lemma intervalIntegral_firstOrderPerronTerm_eq_vonMangoldt_kernel
    {x c W : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    (∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              perronLine c w) =
      (vonMangoldt n : ℂ) *
        (∫ w : ℝ in (-W)..W,
          Complex.exp (perronLine c w * Real.log (x / n)) /
            perronLine c w) := by
  calc
    _ = ∫ w : ℝ in (-W)..W,
        (vonMangoldt n : ℂ) *
          (Complex.exp (perronLine c w * Real.log (x / n)) /
            perronLine c w) := by
      apply intervalIntegral.integral_congr
      intro w _hw
      dsimp
      rw [firstOrderPerronTerm_eq_kernel hx hn, vonMangoldt_eq_mathlib]
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- Explicit first-order truncation error for one nonzero von Mangoldt term,
away from its possible jump. -/
lemma norm_intervalIntegral_firstOrderPerronTerm_sub_halfStep_le_of_log_ne_zero
    {x c W : ℝ} (hx : 0 < x) (hc : 0 < c) (hW : 0 < W)
    {n : ℕ} (hn : n ≠ 0) (hu : Real.log (x / n) ≠ 0) :
    ‖(∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              perronLine c w) -
        (vonMangoldt n : ℂ) *
          perronHalfStep (Real.log (x / n))‖ ≤
      vonMangoldt n * (x / n) ^ c /
        (Real.pi ^ 2 * |Real.log (x / n)| * W) := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hv_nonneg : 0 ≤ vonMangoldt n := by
    rw [vonMangoldt_eq_mathlib]
    exact ArithmeticFunction.vonMangoldt_nonneg
  rw [intervalIntegral_firstOrderPerronTerm_eq_vonMangoldt_kernel hx hn,
    ← mul_sub, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hv_nonneg]
  calc
    vonMangoldt n *
        ‖(∫ w : ℝ in (-W)..W,
            Complex.exp (perronLine c w * Real.log (x / n)) /
              perronLine c w) -
          perronHalfStep (Real.log (x / n))‖ ≤
        vonMangoldt n *
          (Real.exp (c * Real.log (x / n)) /
            (Real.pi ^ 2 * |Real.log (x / n)| * W)) := by
      apply mul_le_mul_of_nonneg_left _ hv_nonneg
      simpa [perronLine] using
        norm_truncated_firstOrderPerron_sub_halfStep_le_of_ne_zero
          (c := c) (u := Real.log (x / n)) (W := W) hc hu hW
    _ = vonMangoldt n * (x / n) ^ c /
          (Real.pi ^ 2 * |Real.log (x / n)| * W) := by
      rw [Real.rpow_def_of_pos (div_pos hx hn_pos)]
      ring

/-- Pointwise height limit for one term of the full first-order Perron
Dirichlet series. -/
theorem tendsto_intervalIntegral_firstOrderPerronTerm_atTop
    {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (n : ℕ) :
    Tendsto
      (fun W : ℝ => ∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              perronLine c w)
      atTop (nhds ((vonMangoldt n : ℂ) *
        perronHalfStep (Real.log (x / n)))) := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term, vonMangoldt_eq_mathlib]
  · have hkernel :=
      (tendsto_truncated_firstOrderPerronKernel_atTop c hc
        (Real.log (x / n))).const_mul (vonMangoldt n : ℂ)
    convert hkernel using 1
    funext W
    exact intervalIntegral_firstOrderPerronTerm_eq_vonMangoldt_kernel hx hn

private noncomputable def firstOrderPerronTanneryError
    (x c : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else if Real.log (x / n) = 0 then vonMangoldt n
  else vonMangoldt n * (x / n) ^ c /
    (Real.pi ^ 2 * |Real.log (x / n)|)

private lemma firstOrderPerronLimit_zero_outside
    {x : ℝ} (hx : 0 < x) {n : ℕ}
    (hn : n ∉ Finset.Ico 1 (Nat.floor x + 1)) :
    (vonMangoldt n : ℂ) * perronHalfStep (Real.log (x / n)) = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [vonMangoldt_eq_mathlib]
  · have hn_lower : Nat.floor x + 1 ≤ n := by
      have : ¬(1 ≤ n ∧ n < Nat.floor x + 1) := by
        simpa [Finset.mem_Ico] using hn
      omega
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hxn : x < (n : ℝ) :=
      (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hn_lower)
    have hratio_pos : 0 < x / (n : ℝ) := div_pos hx hn_pos
    have hratio_lt : x / (n : ℝ) < 1 := (div_lt_one hn_pos).2 hxn
    have hlog : Real.log (x / n) < 0 := Real.log_neg hratio_pos hratio_lt
    simp [perronHalfStep, hlog.not_gt, hlog.ne]

private lemma summable_firstOrderPerronTanneryError
    {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    Summable (firstOrderPerronTanneryError x c) := by
  let coeff : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let C : ℝ := x ^ c / (Real.pi ^ 2 * Real.log 2)
  let G : ℕ → ℝ := fun n => C * ‖LSeries.term coeff (c : ℂ) n‖
  have hnorm_summable : Summable fun n =>
      ‖LSeries.term coeff (c : ℂ) n‖ := by
    have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := (c : ℂ)) (by simpa using hc)
    rw [LSeriesSummable, ← summable_norm_iff] at hs
    simpa [coeff] using hs
  have hG_summable : Summable G :=
    Summable.mul_left C hnorm_summable
  apply hG_summable.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (Nat.floor (2 * x) + 1)] with n hn
  have hn0 : n ≠ 0 := by omega
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hfloor_le : (Nat.floor (2 * x) : ℝ) + 1 ≤ n := by
    exact_mod_cast hn
  have h2xn : 2 * x < (n : ℝ) :=
    (Nat.lt_floor_add_one (2 * x)).trans_le hfloor_le
  have hratio_pos : 0 < x / (n : ℝ) := div_pos hx hn_pos
  have hratio_half : x / (n : ℝ) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hn_pos).2
    linarith
  have hratio_one : x / (n : ℝ) < 1 := by linarith
  have hlog_neg : Real.log (x / n) < 0 :=
    Real.log_neg hratio_pos hratio_one
  have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  have hlog_le : Real.log (x / n) ≤ -Real.log 2 := by
    have := Real.log_le_log hratio_pos hratio_half
    linarith
  have hlog_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have habs : Real.log 2 ≤ |Real.log (x / n)| := by
    rw [abs_of_nonpos hlog_neg.le]
    linarith
  have hu : Real.log (x / n) ≠ 0 := hlog_neg.ne
  have hv_nonneg : 0 ≤ vonMangoldt n := by
    rw [vonMangoldt_eq_mathlib]
    exact ArithmeticFunction.vonMangoldt_nonneg
  have htermnorm : ‖LSeries.term coeff (c : ℂ) n‖ =
      vonMangoldt n / (n : ℝ) ^ c := by
    rw [LSeries.norm_term_eq]
    simp only [coeff, hn0, if_false, Complex.ofReal_re]
    rw [norm_real, Real.norm_eq_abs, ← vonMangoldt_eq_mathlib,
      abs_of_nonneg hv_nonneg]
  let Q : ℝ := x ^ c / Real.pi ^ 2 *
    (vonMangoldt n / (n : ℝ) ^ c)
  have hQ_nonneg : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hE_nonneg : 0 ≤ firstOrderPerronTanneryError x c n := by
    rw [firstOrderPerronTanneryError, if_neg hn0, if_neg hu]
    positivity
  have hEeq : firstOrderPerronTanneryError x c n =
      Q / |Real.log (x / n)| := by
    rw [firstOrderPerronTanneryError, if_neg hn0, if_neg hu]
    rw [Real.div_rpow hx.le hn_pos.le]
    dsimp [Q]
    field_simp
  have hGeq : G n = Q / Real.log 2 := by
    dsimp [G]
    rw [htermnorm]
    dsimp [C, Q]
    field_simp
  rw [Real.norm_eq_abs, abs_of_nonneg hE_nonneg, hEeq, hGeq]
  exact div_le_div_of_nonneg_left hQ_nonneg hlog_two_pos habs

/-- Distinct positive integers below `2m` stay a polynomial distance apart
after taking the logarithm of their ratio. -/
private lemma one_div_abs_log_natCast_div_le_two_mul
    {m n : ℕ} (hm : 2 ≤ m) (hn : n ≠ 0) (hmn : m ≠ n)
    (hnlt : n < 2 * m) :
    1 / |Real.log ((m : ℝ) / (n : ℝ))| ≤ 2 * (m : ℝ) := by
  have hmpos_nat : 0 < m := by omega
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmpos_nat
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hratio_pos : 0 < (m : ℝ) / (n : ℝ) := div_pos hmpos hnpos
  rcases lt_or_gt_of_ne hmn with hmnlt | hmnlt
  · have hratio_lt : (m : ℝ) / (n : ℝ) < 1 :=
      (div_lt_one hnpos).2 (by exact_mod_cast hmnlt)
    have hlogneg : Real.log ((m : ℝ) / (n : ℝ)) < 0 :=
      Real.log_neg hratio_pos hratio_lt
    have hlog_upper := Real.log_le_sub_one_of_pos hratio_pos
    have hgap_nat : m + 1 ≤ n := Nat.succ_le_iff.mpr hmnlt
    have hn_le : (n : ℝ) ≤ 2 * (m : ℝ) := by
      exact_mod_cast (Nat.le_of_lt hnlt)
    have hgap_cast : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hgap_nat
    have hgap : (1 : ℝ) ≤ (n : ℝ) - (m : ℝ) := by linarith
    have hbase : 1 / (2 * (m : ℝ)) ≤ 1 - (m : ℝ) / (n : ℝ) := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * (m : ℝ))]
      field_simp [hnpos.ne']
      nlinarith
    have hlower : 1 / (2 * (m : ℝ)) ≤
        -Real.log ((m : ℝ) / (n : ℝ)) := by linarith
    rw [abs_of_neg hlogneg]
    apply (div_le_iff₀ (neg_pos.mpr hlogneg)).2
    have hmul := mul_le_mul_of_nonneg_left hlower
      (show 0 ≤ 2 * (m : ℝ) by positivity)
    calc
      1 = 2 * (m : ℝ) * (1 / (2 * (m : ℝ))) := by field_simp
      _ ≤ 2 * (m : ℝ) * -Real.log ((m : ℝ) / (n : ℝ)) := hmul
  · have hratio_gt : 1 < (m : ℝ) / (n : ℝ) :=
      (one_lt_div hnpos).2 (by exact_mod_cast hmnlt)
    have hlogpos : 0 < Real.log ((m : ℝ) / (n : ℝ)) :=
      Real.log_pos hratio_gt
    have hinv_pos : 0 < (n : ℝ) / (m : ℝ) := div_pos hnpos hmpos
    have hinv_upper := Real.log_le_sub_one_of_pos hinv_pos
    have hlog_inv : Real.log ((n : ℝ) / (m : ℝ)) =
        -Real.log ((m : ℝ) / (n : ℝ)) := by
      rw [Real.log_div hnpos.ne' hmpos.ne', Real.log_div hmpos.ne' hnpos.ne']
      ring
    have hgap_nat : n + 1 ≤ m := Nat.succ_le_iff.mpr hmnlt
    have hgap_cast : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hgap_nat
    have hgap : (1 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by linarith
    have hbase : 1 / (m : ℝ) ≤ 1 - (n : ℝ) / (m : ℝ) := by
      rw [div_le_iff₀ hmpos]
      rw [show (1 - (n : ℝ) / (m : ℝ)) * (m : ℝ) =
          (m : ℝ) - (n : ℝ) by field_simp]
      exact hgap
    rw [hlog_inv] at hinv_upper
    have hlower : 1 / (m : ℝ) ≤
        Real.log ((m : ℝ) / (n : ℝ)) := by linarith
    rw [abs_of_pos hlogpos]
    apply (div_le_iff₀ hlogpos).2
    have hmul := mul_le_mul_of_nonneg_left hlower
      (show 0 ≤ (m : ℝ) by positivity)
    have hone : 1 ≤ (m : ℝ) * Real.log ((m : ℝ) / (n : ℝ)) := by
      calc
        1 = (m : ℝ) * (1 / (m : ℝ)) := by field_simp
        _ ≤ (m : ℝ) * Real.log ((m : ℝ) / (n : ℝ)) := hmul
    nlinarith [mul_nonneg hmpos.le hlogpos.le]

/-- On the finite range containing the singular Perron terms, integer spacing
turns the Tannery majorant into a coarse polynomial bound. -/
private lemma firstOrderPerronTanneryError_natCast_le_four_mul_pow_four
    {m n : ℕ} (hm : 2 ≤ m) (hnlt : n < 2 * m) :
    firstOrderPerronTanneryError (m : ℝ) 2 n ≤
      4 * (m : ℝ) ^ 4 := by
  have hmpos_nat : 0 < m := by omega
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmpos_nat
  by_cases hn : n = 0
  · subst n
    simp [firstOrderPerronTanneryError]
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn_le_two_m : (n : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hnlt)
  have hv_nonneg : 0 ≤ vonMangoldt n := by
    rw [vonMangoldt_eq_mathlib]
    exact ArithmeticFunction.vonMangoldt_nonneg
  have hv_le_n : vonMangoldt n ≤ (n : ℝ) := by
    rw [vonMangoldt_eq_mathlib]
    calc
      ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
        ArithmeticFunction.vonMangoldt_le_log
      _ ≤ (n : ℝ) - 1 := Real.log_le_sub_one_of_pos hnpos
      _ ≤ (n : ℝ) := by linarith
  by_cases hnm : n = m
  · subst n
    simp only [firstOrderPerronTanneryError, hmpos_nat.ne',
      div_self hmpos.ne', Real.log_one, ↓reduceIte]
    have hm_one : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos_nat
    nlinarith [sq_nonneg ((m : ℝ) ^ 2 - 1)]
  have hratio_pos : 0 < (m : ℝ) / (n : ℝ) := div_pos hmpos hnpos
  have hmn : m ≠ n := Ne.symm hnm
  have hratio_ne_one : (m : ℝ) / (n : ℝ) ≠ 1 := by
    intro hratio
    have hcast : (m : ℝ) = (n : ℝ) := (div_eq_one_iff_eq hnpos.ne').mp hratio
    exact hmn (Nat.cast_inj.mp hcast)
  have hlog_ne : Real.log ((m : ℝ) / (n : ℝ)) ≠ 0 := by
    intro hlog
    rcases Real.log_eq_zero.mp hlog with hzero | hone | hneg
    · exact hratio_pos.ne' hzero
    · exact hratio_ne_one hone
    · linarith
  rw [firstOrderPerronTanneryError, if_neg hn, if_neg hlog_ne,
    Real.rpow_two]
  have hratio_le : (m : ℝ) / (n : ℝ) ≤ (m : ℝ) := by
    apply (div_le_iff₀ hnpos).2
    nlinarith
  have hratio_nonneg : 0 ≤ (m : ℝ) / (n : ℝ) := hratio_pos.le
  have hratio_sq : ((m : ℝ) / (n : ℝ)) ^ 2 ≤ (m : ℝ) ^ 2 := by
    nlinarith
  have hlog_recip := one_div_abs_log_natCast_div_le_two_mul hm hn hmn hnlt
  have hpi_sq : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have habs_pos : 0 < |Real.log ((m : ℝ) / (n : ℝ))| :=
    abs_pos.mpr hlog_ne
  calc
    vonMangoldt n * ((m : ℝ) / (n : ℝ)) ^ 2 /
          (Real.pi ^ 2 * |Real.log ((m : ℝ) / (n : ℝ))|) ≤
        vonMangoldt n * ((m : ℝ) / (n : ℝ)) ^ 2 /
          |Real.log ((m : ℝ) / (n : ℝ))| := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg hv_nonneg (sq_nonneg ((m : ℝ) / (n : ℝ))))
        habs_pos
      nlinarith
    _ = (vonMangoldt n * ((m : ℝ) / (n : ℝ)) ^ 2) *
          (1 / |Real.log ((m : ℝ) / (n : ℝ))|) := by ring
    _ ≤ ((n : ℝ) * (m : ℝ) ^ 2) * (2 * (m : ℝ)) := by
      gcongr
    _ ≤ 4 * (m : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((m : ℝ) ^ 2)]

/-- Beyond `2m`, the logarithmic denominator is bounded away from zero and
the Perron majorant is dominated by the absolutely convergent zeta line
`Re(s)=2`. -/
private lemma firstOrderPerronTanneryError_natCast_tail_le
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 * m ≤ n) :
    firstOrderPerronTanneryError (m : ℝ) 2 n ≤
      ((m : ℝ) ^ 2 / Real.log 2) *
        ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (2 : ℂ) n‖ := by
  have hmpos_nat : 0 < m := by omega
  have hnpos_nat : 0 < n := by omega
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmpos_nat
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn0 : n ≠ 0 := hnpos_nat.ne'
  have hmn : m ≠ n := by omega
  have hratio_pos : 0 < (m : ℝ) / (n : ℝ) := div_pos hmpos hnpos
  have hratio_half : (m : ℝ) / (n : ℝ) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hnpos).2
    have hn_cast : 2 * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hratio_one : (m : ℝ) / (n : ℝ) < 1 := by linarith
  have hlogneg : Real.log ((m : ℝ) / (n : ℝ)) < 0 :=
    Real.log_neg hratio_pos hratio_one
  have hlogne : Real.log ((m : ℝ) / (n : ℝ)) ≠ 0 := hlogneg.ne
  have hlog_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  have habs : Real.log 2 ≤ |Real.log ((m : ℝ) / (n : ℝ))| := by
    have hlog_le := Real.log_le_log hratio_pos hratio_half
    rw [hlog_half] at hlog_le
    rw [abs_of_neg hlogneg]
    linarith
  have hv_nonneg : 0 ≤ vonMangoldt n := by
    rw [vonMangoldt_eq_mathlib]
    exact ArithmeticFunction.vonMangoldt_nonneg
  have htermnorm :
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (2 : ℂ) n‖ = vonMangoldt n / (n : ℝ) ^ 2 := by
    rw [LSeries.norm_term_eq]
    simp only [hn0, if_false]
    norm_num
    rw [← vonMangoldt_eq_mathlib, abs_of_nonneg hv_nonneg]
  rw [firstOrderPerronTanneryError, if_neg hn0, if_neg hlogne,
    Real.rpow_two, htermnorm]
  have hpi_sq : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have habs_pos : 0 < |Real.log ((m : ℝ) / (n : ℝ))| := abs_pos.mpr hlogne
  calc
    vonMangoldt n * ((m : ℝ) / (n : ℝ)) ^ 2 /
          (Real.pi ^ 2 * |Real.log ((m : ℝ) / (n : ℝ))|) ≤
        vonMangoldt n * ((m : ℝ) / (n : ℝ)) ^ 2 /
          |Real.log ((m : ℝ) / (n : ℝ))| := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg hv_nonneg (sq_nonneg ((m : ℝ) / (n : ℝ)))) habs_pos
      nlinarith
    _ ≤ vonMangoldt n * ((m : ℝ) / (n : ℝ)) ^ 2 / Real.log 2 := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg hv_nonneg (sq_nonneg ((m : ℝ) / (n : ℝ))))
        hlog_two_pos habs
    _ = ((m : ℝ) ^ 2 / Real.log 2) *
          (vonMangoldt n / (n : ℝ) ^ 2) := by field_simp

/-- The complete first-order Perron Tannery majorant is polynomially uniform
at positive integral sampling points. -/
private theorem exists_tsum_firstOrderPerronTanneryError_natCast_le_pow_five :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m →
      (∑' n : ℕ, firstOrderPerronTanneryError (m : ℝ) 2 n) ≤
        C * (m : ℝ) ^ 5 := by
  let coeff : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let B : ℝ := ∑' n : ℕ, ‖LSeries.term coeff (2 : ℂ) n‖
  let C : ℝ := 8 + B / Real.log 2
  have hseries := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (2 : ℂ)) (by norm_num)
  have hBsum : Summable fun n : ℕ => ‖LSeries.term coeff (2 : ℂ) n‖ := by
    rw [LSeriesSummable, ← summable_norm_iff] at hseries
    simpa [coeff] using hseries
  have hB : 0 ≤ B := by
    dsimp [B]
    exact tsum_nonneg fun n => norm_nonneg _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro m hm
  have hmpos_nat : 0 < m := by omega
  have hm_one : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos_nat
  have hE := summable_firstOrderPerronTanneryError
    (x := (m : ℝ)) (c := 2) (by positivity) (by norm_num)
  have hsplit := hE.sum_add_tsum_nat_add (2 * m)
  have hfinite :
      (∑ n ∈ Finset.range (2 * m),
          firstOrderPerronTanneryError (m : ℝ) 2 n) ≤
        8 * (m : ℝ) ^ 5 := by
    calc
      _ ≤ ∑ _n ∈ Finset.range (2 * m), 4 * (m : ℝ) ^ 4 := by
        exact Finset.sum_le_sum fun n hn =>
          firstOrderPerronTanneryError_natCast_le_four_mul_pow_four
            hm (Finset.mem_range.mp hn)
      _ = 8 * (m : ℝ) ^ 5 := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
        push_cast
        ring
  have hBsplit := hBsum.sum_add_tsum_nat_add (2 * m)
  have hBtail :
      (∑' n : ℕ, ‖LSeries.term coeff (2 : ℂ) (n + 2 * m)‖) ≤ B := by
    have hfiniteB : 0 ≤
        ∑ n ∈ Finset.range (2 * m), ‖LSeries.term coeff (2 : ℂ) n‖ :=
      Finset.sum_nonneg fun n _hn => norm_nonneg _
    dsimp [B]
    rw [← hBsplit]
    linarith
  have hEtailSum : Summable fun n : ℕ =>
      firstOrderPerronTanneryError (m : ℝ) 2 (n + 2 * m) :=
    (summable_nat_add_iff (2 * m)).mpr hE
  have hmajorTail : Summable fun n : ℕ =>
      ((m : ℝ) ^ 2 / Real.log 2) *
        ‖LSeries.term coeff (2 : ℂ) (n + 2 * m)‖ :=
    ((summable_nat_add_iff (2 * m)).mpr hBsum).mul_left _
  have htail :
      (∑' n : ℕ,
          firstOrderPerronTanneryError (m : ℝ) 2 (n + 2 * m)) ≤
        ((m : ℝ) ^ 2 / Real.log 2) * B := by
    calc
      _ ≤ ∑' n : ℕ, ((m : ℝ) ^ 2 / Real.log 2) *
          ‖LSeries.term coeff (2 : ℂ) (n + 2 * m)‖ := by
        apply Summable.tsum_le_tsum _ hEtailSum hmajorTail
        intro n
        simpa [coeff, Nat.add_comm] using
          firstOrderPerronTanneryError_natCast_tail_le
            hm (show 2 * m ≤ n + 2 * m by omega)
      _ = ((m : ℝ) ^ 2 / Real.log 2) *
          (∑' n : ℕ, ‖LSeries.term coeff (2 : ℂ) (n + 2 * m)‖) :=
        tsum_mul_left
      _ ≤ ((m : ℝ) ^ 2 / Real.log 2) * B := by
        apply mul_le_mul_of_nonneg_left hBtail
        positivity
  have hpow : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 5 := by
    have hm3 : 1 ≤ (m : ℝ) ^ 3 := one_le_pow₀ hm_one
    calc
      (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * (m : ℝ) ^ 3 :=
        by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hm3 (sq_nonneg (m : ℝ))
      _ = (m : ℝ) ^ 5 := by ring
  calc
    (∑' n : ℕ, firstOrderPerronTanneryError (m : ℝ) 2 n) =
        (∑ n ∈ Finset.range (2 * m),
          firstOrderPerronTanneryError (m : ℝ) 2 n) +
        ∑' n : ℕ, firstOrderPerronTanneryError (m : ℝ) 2 (n + 2 * m) :=
      hsplit.symm
    _ ≤ 8 * (m : ℝ) ^ 5 + ((m : ℝ) ^ 2 / Real.log 2) * B :=
      add_le_add hfinite htail
    _ ≤ 8 * (m : ℝ) ^ 5 + ((m : ℝ) ^ 5 / Real.log 2) * B := by
      gcongr
    _ = C * (m : ℝ) ^ 5 := by
      dsimp [C]
      field_simp

/-- At a jump of `psi`, the first-order Perron kernel has an explicit
`O(1 / W)` approach to its half-weight. -/
private lemma norm_intervalIntegral_firstOrderPerronTerm_sub_halfStep_le_of_log_eq_zero
    {x c W : ℝ} (hx : 0 < x) (hc : 0 < c) (hW : 0 < W)
    {n : ℕ} (hn : n ≠ 0) (hu : Real.log (x / n) = 0) :
    ‖(∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              perronLine c w) -
        (vonMangoldt n : ℂ) * perronHalfStep (Real.log (x / n))‖ ≤
      c * vonMangoldt n / (2 * Real.pi ^ 2 * W) := by
  have hv_nonneg : 0 ≤ vonMangoldt n := by
    rw [vonMangoldt_eq_mathlib]
    exact ArithmeticFunction.vonMangoldt_nonneg
  let y : ℝ := 2 * Real.pi * W / c
  have hy : 0 < y := by dsimp [y]; positivity
  have hatan_nonneg : 0 ≤ Real.arctan y := Real.arctan_nonneg.mpr hy.le
  have hatan_lt : Real.arctan y < Real.pi / 2 := Real.arctan_lt_pi_div_two y
  have hratio_le : Real.arctan y / Real.pi ≤ 1 / 2 := by
    apply (div_le_iff₀ Real.pi_pos).2
    linarith
  have hatan_inv_le : Real.arctan y⁻¹ ≤ y⁻¹ := by
    have hnonneg : 0 ≤ Real.arctan y⁻¹ :=
      Real.arctan_nonneg.mpr (inv_nonneg.mpr hy.le)
    have htan := Real.le_tan hnonneg (Real.arctan_lt_pi_div_two y⁻¹)
    simpa using htan
  have hscalar :
      1 / 2 - Real.arctan y / Real.pi ≤
        c / (2 * Real.pi ^ 2 * W) := by
    calc
      1 / 2 - Real.arctan y / Real.pi =
          (Real.pi / 2 - Real.arctan y) / Real.pi := by
        field_simp [Real.pi_ne_zero]
      _ = Real.arctan y⁻¹ / Real.pi := by
        rw [Real.arctan_inv_of_pos hy]
      _ ≤ y⁻¹ / Real.pi :=
        div_le_div_of_nonneg_right hatan_inv_le Real.pi_pos.le
      _ = c / (2 * Real.pi ^ 2 * W) := by
        dsimp [y]
        field_simp [Real.pi_ne_zero, hc.ne', hW.ne']
  rw [intervalIntegral_firstOrderPerronTerm_eq_vonMangoldt_kernel hx hn, hu]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hzero :
      (∫ w : ℝ in (-W)..W,
        (1 : ℂ) / perronLine c w) =
          (Real.arctan (2 * Real.pi * W / c) / Real.pi : ℝ) := by
    simpa [perronLine] using intervalIntegral_firstOrderPerron_zero_eq (W := W) hc
  rw [hzero]
  simp only [perronHalfStep, lt_self_iff_false, ↓reduceIte, one_div]
  rw [← mul_sub, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hv_nonneg]
  have hcast :
      ((Real.arctan (2 * Real.pi * W / c) / Real.pi : ℝ) : ℂ) - (2 : ℂ)⁻¹ =
        ((Real.arctan (2 * Real.pi * W / c) / Real.pi - 1 / 2 : ℝ) : ℂ) := by
    push_cast
    norm_num
  rw [hcast, norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by simpa [y] using sub_nonpos.mpr hratio_le)]
  have hscalar' :
      1 / 2 - Real.arctan (2 * Real.pi * W / c) / Real.pi ≤
        c / (2 * Real.pi ^ 2 * W) := by
    simpa [y] using hscalar
  convert mul_le_mul_of_nonneg_left hscalar' hv_nonneg using 1 <;> ring

/-- The full von Mangoldt Dirichlet series satisfies ordinary first-order
Perron inversion.  The symmetric truncation converges to the midpoint value
`psi0`, with half weight at an integral jump. -/
theorem tendsto_vonMangoldt_firstOrder_tsum_atTop
    {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    Tendsto
      (fun W : ℝ => ∑' n : ℕ, ∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              perronLine c w)
      atTop (nhds (chebyshevPsi0 x : ℂ)) := by
  let A : ℝ → ℕ → ℂ := fun W n => ∫ w : ℝ in (-W)..W,
    (x : ℂ) ^ perronLine c w *
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (perronLine c w) n /
          perronLine c w
  let M : ℕ → ℂ := fun n =>
    (vonMangoldt n : ℂ) * perronHalfStep (Real.log (x / n))
  let E : ℕ → ℝ := firstOrderPerronTanneryError x c
  let B : ℕ → ℝ := fun n => ‖M n‖ + E n
  have hc_pos : 0 < c := one_pos.trans hc
  have hM_zero : ∀ n ∉ Finset.Ico 1 (Nat.floor x + 1), M n = 0 := by
    intro n hn
    exact firstOrderPerronLimit_zero_outside hx hn
  have hM_summable : Summable M := summable_of_ne_finset_zero hM_zero
  have hM_tsum : (∑' n, M n) = (chebyshevPsi0 x : ℂ) := by
    rw [tsum_eq_sum hM_zero]
    exact sum_vonMangoldt_perronHalfStep_log_div_eq_chebyshevPsi0 x hx
  have hE_summable : Summable E :=
    summable_firstOrderPerronTanneryError hx hc
  have hB_summable : Summable B := hM_summable.norm.add hE_summable
  have hpoint (n : ℕ) : Tendsto (fun W => A W n) atTop (nhds (M n)) := by
    simpa [A, M] using
      tendsto_intervalIntegral_firstOrderPerronTerm_atTop hx hc_pos n
  have hbound : ∀ᶠ W in atTop, ∀ n, ‖A W n‖ ≤ B n := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with W hW n
    have hW_pos : 0 < W := zero_lt_one.trans_le hW
    by_cases hn : n = 0
    · subst n
      simp [A, M, E, B, firstOrderPerronTanneryError, LSeries.term,
        vonMangoldt_eq_mathlib]
    · have hv_nonneg : 0 ≤ vonMangoldt n := by
        rw [vonMangoldt_eq_mathlib]
        exact ArithmeticFunction.vonMangoldt_nonneg
      by_cases hu : Real.log (x / n) = 0
      · have harg_nonneg : 0 ≤ 2 * Real.pi * W / c := by positivity
        have hratio_nonneg :
            0 ≤ Real.arctan (2 * Real.pi * W / c) / Real.pi :=
          div_nonneg (Real.arctan_nonneg.mpr harg_nonneg) Real.pi_pos.le
        have hratio_le_one :
            Real.arctan (2 * Real.pi * W / c) / Real.pi ≤ 1 := by
          apply (div_le_one₀ Real.pi_pos).2
          exact (Real.arctan_lt_pi_div_two _).le.trans (by linarith [Real.pi_pos])
        have hAeq : A W n =
            (vonMangoldt n : ℂ) *
              (Real.arctan (2 * Real.pi * W / c) / Real.pi : ℝ) := by
          dsimp [A]
          rw [intervalIntegral_firstOrderPerronTerm_eq_vonMangoldt_kernel hx hn,
            hu]
          congr 1
          simpa [perronLine] using
            intervalIntegral_firstOrderPerron_zero_eq (W := W) hc_pos
        have hA_le : ‖A W n‖ ≤ vonMangoldt n := by
          rw [hAeq, norm_mul, norm_real, Real.norm_eq_abs,
            abs_of_nonneg hv_nonneg, norm_real, Real.norm_eq_abs,
            abs_of_nonneg hratio_nonneg]
          exact mul_le_of_le_one_right hv_nonneg hratio_le_one
        calc
          ‖A W n‖ ≤ vonMangoldt n := hA_le
          _ ≤ ‖M n‖ + E n := by
            dsimp [E, B]
            rw [firstOrderPerronTanneryError, if_neg hn, if_pos hu]
            exact le_add_of_nonneg_left (norm_nonneg _)
      · have herr :=
          norm_intervalIntegral_firstOrderPerronTerm_sub_halfStep_le_of_log_ne_zero
            hx hc_pos hW_pos hn hu
        have hE_nonneg : 0 ≤ E n := by
          dsimp [E]
          rw [firstOrderPerronTanneryError, if_neg hn, if_neg hu]
          positivity
        have herr_le : ‖A W n - M n‖ ≤ E n := by
          have hdiv :
              vonMangoldt n * (x / n) ^ c /
                    (Real.pi ^ 2 * |Real.log (x / n)| * W) = E n / W := by
            dsimp [E]
            rw [firstOrderPerronTanneryError, if_neg hn, if_neg hu]
            field_simp
          calc
            ‖A W n - M n‖ ≤
                vonMangoldt n * (x / n) ^ c /
                  (Real.pi ^ 2 * |Real.log (x / n)| * W) := by
              simpa [A, M] using herr
            _ = E n / W := hdiv
            _ ≤ E n := by
              apply (div_le_iff₀ hW_pos).2
              simpa [mul_comm] using
                mul_le_mul_of_nonneg_left hW hE_nonneg
        calc
          ‖A W n‖ = ‖M n + (A W n - M n)‖ := by ring_nf
          _ ≤ ‖M n‖ + ‖A W n - M n‖ := norm_add_le _ _
          _ ≤ ‖M n‖ + E n := add_le_add_right herr_le _
          _ = B n := rfl
  have ht := tendsto_tsum_of_dominated_convergence hB_summable hpoint hbound
  rw [hM_tsum] at ht
  simpa [A] using ht

/-- Complete first-order Perron formula in zeta logarithmic-derivative
notation, on every vertical line `Re(s) = c > 1`. -/
theorem tendsto_truncated_neg_logDeriv_firstOrderPerron_atTop
    {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    Tendsto
      (fun W : ℝ => ∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          (-deriv riemannZeta (perronLine c w) /
            riemannZeta (perronLine c w)) /
              perronLine c w)
      atTop (nhds (chebyshevPsi0 x : ℂ)) := by
  have h := tendsto_vonMangoldt_firstOrder_tsum_atTop hx hc
  convert h using 1
  funext W
  exact intervalIntegral_neg_logDeriv_riemannZeta_firstOrder_eq_vonMangoldt_tsum
    hx hc

/-- Quantitative first-order Perron inversion for the von Mangoldt series.
For fixed `x` and any vertical line `Re(s) = c > 1`, the finite-height
logarithmic-derivative integral approaches `psi0 x` at rate `O(1 / W)`. -/
theorem exists_norm_truncated_neg_logDeriv_firstOrderPerron_sub_chebyshevPsi0_le_div
    {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ, 1 ≤ W →
      ‖(∫ w : ℝ in (-W)..W,
          (x : ℂ) ^ perronLine c w *
            (-deriv riemannZeta (perronLine c w) /
              riemannZeta (perronLine c w)) /
                perronLine c w) -
          (chebyshevPsi0 x : ℂ)‖ ≤ C / W := by
  let A : ℝ → ℕ → ℂ := fun W n => ∫ w : ℝ in (-W)..W,
    (x : ℂ) ^ perronLine c w *
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (perronLine c w) n /
          perronLine c w
  let M : ℕ → ℂ := fun n =>
    (vonMangoldt n : ℂ) * perronHalfStep (Real.log (x / n))
  let E : ℕ → ℝ := firstOrderPerronTanneryError x c
  let R : ℕ → ℝ := fun n => E n + c * ‖M n‖
  have hc_pos : 0 < c := one_pos.trans hc
  have hM_zero : ∀ n ∉ Finset.Ico 1 (Nat.floor x + 1), M n = 0 := by
    intro n hn
    exact firstOrderPerronLimit_zero_outside hx hn
  have hM_summable : Summable M := summable_of_ne_finset_zero hM_zero
  have hM_tsum : (∑' n, M n) = (chebyshevPsi0 x : ℂ) := by
    rw [tsum_eq_sum hM_zero]
    exact sum_vonMangoldt_perronHalfStep_log_div_eq_chebyshevPsi0 x hx
  have hE_summable : Summable E := summable_firstOrderPerronTanneryError hx hc
  have hE_nonneg (n : ℕ) : 0 ≤ E n := by
    dsimp [E]
    rw [firstOrderPerronTanneryError]
    split_ifs with hn hu
    · exact le_rfl
    · rw [vonMangoldt_eq_mathlib]
      exact ArithmeticFunction.vonMangoldt_nonneg
    · have hn_pos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hv_nonneg : 0 ≤ vonMangoldt n := by
        rw [vonMangoldt_eq_mathlib]
        exact ArithmeticFunction.vonMangoldt_nonneg
      exact div_nonneg
        (mul_nonneg hv_nonneg (Real.rpow_nonneg (div_nonneg hx.le hn_pos.le) c))
        (mul_nonneg (sq_nonneg Real.pi) (abs_nonneg _))
  have hR_nonneg (n : ℕ) : 0 ≤ R n := by
    dsimp [R]
    exact add_nonneg (hE_nonneg n) (mul_nonneg hc_pos.le (norm_nonneg _))
  have hR_summable : Summable R := by
    exact hE_summable.add (hM_summable.norm.mul_left c)
  refine ⟨∑' n, R n, tsum_nonneg hR_nonneg, ?_⟩
  intro W hW
  have hW_pos : 0 < W := zero_lt_one.trans_le hW
  have hpoint (n : ℕ) : ‖A W n - M n‖ ≤ R n / W := by
    by_cases hn : n = 0
    · subst n
      simp [A, M, E, R, firstOrderPerronTanneryError, LSeries.term,
        vonMangoldt_eq_mathlib]
    · by_cases hu : Real.log (x / n) = 0
      · have hjump :=
          norm_intervalIntegral_firstOrderPerronTerm_sub_halfStep_le_of_log_eq_zero
            hx hc_pos hW_pos hn hu
        have hv_nonneg : 0 ≤ vonMangoldt n := by
          rw [vonMangoldt_eq_mathlib]
          exact ArithmeticFunction.vonMangoldt_nonneg
        have hpi_sq : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
        have hMnorm : ‖M n‖ = vonMangoldt n / 2 := by
          dsimp [M]
          rw [hu]
          simp [perronHalfStep, abs_of_nonneg hv_nonneg, div_eq_mul_inv]
        calc
          ‖A W n - M n‖ ≤ c * vonMangoldt n / (2 * Real.pi ^ 2 * W) := by
            simpa [A, M] using hjump
          _ ≤ (c * ‖M n‖) / W := by
            rw [hMnorm]
            have hcv : 0 ≤ c * vonMangoldt n := mul_nonneg hc_pos.le hv_nonneg
            calc
              c * vonMangoldt n / (2 * Real.pi ^ 2 * W) ≤
                  c * vonMangoldt n / (2 * W) := by
                apply div_le_div_of_nonneg_left hcv (by positivity)
                nlinarith
              _ = c * (vonMangoldt n / 2) / W := by ring
          _ ≤ R n / W := by
            apply div_le_div_of_nonneg_right _ hW_pos.le
            dsimp [R]
            exact le_add_of_nonneg_left (hE_nonneg n)
      · have herr :=
          norm_intervalIntegral_firstOrderPerronTerm_sub_halfStep_le_of_log_ne_zero
            hx hc_pos hW_pos hn hu
        have hEeq :
            vonMangoldt n * (x / n) ^ c /
                (Real.pi ^ 2 * |Real.log (x / n)| * W) = E n / W := by
          dsimp [E]
          rw [firstOrderPerronTanneryError, if_neg hn, if_neg hu]
          field_simp
        calc
          ‖A W n - M n‖ ≤
              vonMangoldt n * (x / n) ^ c /
                (Real.pi ^ 2 * |Real.log (x / n)| * W) := by
            simpa [A, M] using herr
          _ = E n / W := hEeq
          _ ≤ R n / W := by
            apply div_le_div_of_nonneg_right _ hW_pos.le
            dsimp [R]
            exact le_add_of_nonneg_right
              (mul_nonneg hc_pos.le (norm_nonneg _))
  have hR_div_summable : Summable (fun n => R n / W) :=
    hR_summable.div_const W
  have hdiff_summable : Summable (fun n => A W n - M n) :=
    Summable.of_norm_bounded hR_div_summable hpoint
  have hA_summable : Summable (A W) := by
    have hadd := hdiff_summable.add hM_summable
    simpa only [sub_add_cancel] using hadd
  rw [intervalIntegral_neg_logDeriv_riemannZeta_firstOrder_eq_vonMangoldt_tsum hx hc,
    ← hM_tsum, ← hA_summable.tsum_sub hM_summable]
  calc
    ‖∑' n, (A W n - M n)‖ ≤ ∑' n, ‖A W n - M n‖ :=
      norm_tsum_le_tsum_norm hdiff_summable.norm
    _ ≤ ∑' n, R n / W :=
      Summable.tsum_le_tsum hpoint hdiff_summable.norm hR_div_summable
    _ = (∑' n, R n) / W := by
      simp_rw [div_eq_mul_inv]
      rw [tsum_mul_right]

/-- On the fixed line `Re(s)=2`, first-order Perron inversion has one
polynomial error constant for every positive integral sampling point.  The
coarse exponent five is sufficient for later RH-scale arguments, where the
truncation height may be chosen as a higher power of the sampling point. -/
theorem
    exists_uniform_nat_norm_truncated_neg_logDeriv_firstOrderPerron_sub_chebyshevPsi0_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (W : ℝ), 2 ≤ m → 1 ≤ W →
      ‖(∫ w : ℝ in (-W)..W,
          ((m : ℝ) : ℂ) ^ perronLine 2 w *
            (-deriv riemannZeta (perronLine 2 w) /
              riemannZeta (perronLine 2 w)) /
                perronLine 2 w) -
          (chebyshevPsi0 (m : ℝ) : ℂ)‖ ≤
        C * (m : ℝ) ^ 5 / W := by
  rcases exists_tsum_firstOrderPerronTanneryError_natCast_le_pow_five with
    ⟨CE, hCE, hEbound⟩
  let K : ℝ := Real.log 4 + 4
  let C : ℝ := CE + 2 * K
  have hK : 0 ≤ K := by
    dsimp [K]
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro m W hm hW
  let x : ℝ := m
  let A : ℝ → ℕ → ℂ := fun W n => ∫ w : ℝ in (-W)..W,
    (x : ℂ) ^ perronLine 2 w *
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (perronLine 2 w) n /
          perronLine 2 w
  let M : ℕ → ℂ := fun n =>
    (vonMangoldt n : ℂ) * perronHalfStep (Real.log (x / n))
  let E : ℕ → ℝ := firstOrderPerronTanneryError x 2
  let R : ℕ → ℝ := fun n => E n + 2 * ‖M n‖
  have hx : 0 < x := by dsimp [x]; positivity
  have hM_zero : ∀ n ∉ Finset.Ico 1 (Nat.floor x + 1), M n = 0 := by
    intro n hn
    exact firstOrderPerronLimit_zero_outside hx hn
  have hM_summable : Summable M := summable_of_ne_finset_zero hM_zero
  have hM_tsum : (∑' n, M n) = (chebyshevPsi0 x : ℂ) := by
    rw [tsum_eq_sum hM_zero]
    exact sum_vonMangoldt_perronHalfStep_log_div_eq_chebyshevPsi0 x hx
  have hMnorm_point (n : ℕ) : ‖M n‖ ≤ vonMangoldt n := by
    have hv : 0 ≤ vonMangoldt n := by
      rw [vonMangoldt_eq_mathlib]
      exact ArithmeticFunction.vonMangoldt_nonneg
    have hstep : ‖perronHalfStep (Real.log (x / n))‖ ≤ 1 := by
      unfold perronHalfStep
      split_ifs <;> norm_num
    dsimp [M]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
    exact mul_le_of_le_one_right hv hstep
  have hMnorm_zero : ∀ n ∉ Finset.Ico 1 (Nat.floor x + 1), ‖M n‖ = 0 := by
    intro n hn
    rw [hM_zero n hn, norm_zero]
  have hMnorm_bound : (∑' n : ℕ, ‖M n‖) ≤ K * x := by
    rw [tsum_eq_sum hMnorm_zero]
    calc
      (∑ n ∈ Finset.Ico 1 (Nat.floor x + 1), ‖M n‖) ≤
          ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1), vonMangoldt n :=
        Finset.sum_le_sum fun n _hn => hMnorm_point n
      _ = chebyshevPsi x := rfl
      _ ≤ K * x := by
        dsimp [K]
        rw [chebyshevPsi_eq_mathlib]
        exact Chebyshev.psi_le_const_mul_self hx.le
  have hE_summable : Summable E :=
    summable_firstOrderPerronTanneryError hx (by norm_num)
  have hE_nonneg (n : ℕ) : 0 ≤ E n := by
    dsimp [E]
    rw [firstOrderPerronTanneryError]
    split_ifs with hn hu
    · exact le_rfl
    · rw [vonMangoldt_eq_mathlib]
      exact ArithmeticFunction.vonMangoldt_nonneg
    · have hn_pos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hv_nonneg : 0 ≤ vonMangoldt n := by
        rw [vonMangoldt_eq_mathlib]
        exact ArithmeticFunction.vonMangoldt_nonneg
      exact div_nonneg
        (mul_nonneg hv_nonneg (Real.rpow_nonneg (div_nonneg hx.le hn_pos.le) 2))
        (mul_nonneg (sq_nonneg Real.pi) (abs_nonneg _))
  have hR_summable : Summable R := by
    exact hE_summable.add (hM_summable.norm.mul_left 2)
  have hEpoly : (∑' n : ℕ, E n) ≤ CE * x ^ 5 := by
    simpa [E, x] using hEbound m hm
  have hx_le_pow : x ≤ x ^ 5 := by
    have hx1 : 1 ≤ x := by
      dsimp [x]
      exact_mod_cast (show 1 ≤ m by omega)
    have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx1
    calc
      x = x * 1 := by ring
      _ ≤ x * x ^ 4 := mul_le_mul_of_nonneg_left hx4 hx.le
      _ = x ^ 5 := by ring
  have hRpoly : (∑' n : ℕ, R n) ≤ C * x ^ 5 := by
    have hMnorm_summable := hM_summable.norm
    have hRsum : (∑' n : ℕ, R n) =
        (∑' n : ℕ, E n) + 2 * (∑' n : ℕ, ‖M n‖) := by
      simp_rw [R]
      rw [hE_summable.tsum_add (hMnorm_summable.mul_left 2), tsum_mul_left]
    rw [hRsum]
    calc
      _ ≤ CE * x ^ 5 + 2 * (K * x) :=
        add_le_add hEpoly (mul_le_mul_of_nonneg_left hMnorm_bound (by norm_num))
      _ ≤ CE * x ^ 5 + 2 * (K * x ^ 5) := by
        gcongr
      _ = C * x ^ 5 := by dsimp [C]; ring
  have hW_pos : 0 < W := zero_lt_one.trans_le hW
  have hpoint (n : ℕ) : ‖A W n - M n‖ ≤ R n / W := by
    by_cases hn : n = 0
    · subst n
      simp [A, M, E, R, firstOrderPerronTanneryError, LSeries.term,
        vonMangoldt_eq_mathlib]
    · by_cases hu : Real.log (x / n) = 0
      · have hjump :=
          norm_intervalIntegral_firstOrderPerronTerm_sub_halfStep_le_of_log_eq_zero
            hx (by norm_num : (0 : ℝ) < 2) hW_pos hn hu
        have hv_nonneg : 0 ≤ vonMangoldt n := by
          rw [vonMangoldt_eq_mathlib]
          exact ArithmeticFunction.vonMangoldt_nonneg
        have hpi_sq : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
        have hMnorm : ‖M n‖ = vonMangoldt n / 2 := by
          dsimp [M]
          rw [hu]
          simp [perronHalfStep, abs_of_nonneg hv_nonneg, div_eq_mul_inv]
        calc
          ‖A W n - M n‖ ≤ 2 * vonMangoldt n / (2 * Real.pi ^ 2 * W) := by
            simpa [A, M] using hjump
          _ ≤ (2 * ‖M n‖) / W := by
            rw [hMnorm]
            have hv2 : 0 ≤ 2 * vonMangoldt n := mul_nonneg (by norm_num) hv_nonneg
            calc
              2 * vonMangoldt n / (2 * Real.pi ^ 2 * W) ≤
                  2 * vonMangoldt n / (2 * W) := by
                apply div_le_div_of_nonneg_left hv2 (by positivity)
                nlinarith
              _ = 2 * (vonMangoldt n / 2) / W := by ring
          _ ≤ R n / W := by
            apply div_le_div_of_nonneg_right _ hW_pos.le
            dsimp [R]
            exact le_add_of_nonneg_left (hE_nonneg n)
      · have herr :=
          norm_intervalIntegral_firstOrderPerronTerm_sub_halfStep_le_of_log_ne_zero
            hx (by norm_num : (0 : ℝ) < 2) hW_pos hn hu
        have hEeq :
            vonMangoldt n * (x / n) ^ (2 : ℝ) /
                (Real.pi ^ 2 * |Real.log (x / n)| * W) = E n / W := by
          dsimp [E]
          rw [firstOrderPerronTanneryError, if_neg hn, if_neg hu]
          field_simp
        calc
          ‖A W n - M n‖ ≤
              vonMangoldt n * (x / n) ^ (2 : ℝ) /
                (Real.pi ^ 2 * |Real.log (x / n)| * W) := by
            simpa [A, M] using herr
          _ = E n / W := hEeq
          _ ≤ R n / W := by
            apply div_le_div_of_nonneg_right _ hW_pos.le
            dsimp [R]
            exact le_add_of_nonneg_right
              (mul_nonneg (by norm_num) (norm_nonneg _))
  have hR_div_summable : Summable (fun n => R n / W) :=
    hR_summable.div_const W
  have hdiff_summable : Summable (fun n => A W n - M n) :=
    Summable.of_norm_bounded hR_div_summable hpoint
  have hA_summable : Summable (A W) := by
    have hadd := hdiff_summable.add hM_summable
    simpa only [sub_add_cancel] using hadd
  change ‖(∫ w : ℝ in (-W)..W,
      (x : ℂ) ^ perronLine 2 w *
        (-deriv riemannZeta (perronLine 2 w) /
          riemannZeta (perronLine 2 w)) /
            perronLine 2 w) -
      (chebyshevPsi0 x : ℂ)‖ ≤ C * x ^ 5 / W
  rw [intervalIntegral_neg_logDeriv_riemannZeta_firstOrder_eq_vonMangoldt_tsum
      hx (by norm_num), ← hM_tsum, ← hA_summable.tsum_sub hM_summable]
  calc
    ‖∑' n, (A W n - M n)‖ ≤ ∑' n, ‖A W n - M n‖ :=
      norm_tsum_le_tsum_norm hdiff_summable.norm
    _ ≤ ∑' n, R n / W :=
      Summable.tsum_le_tsum hpoint hdiff_summable.norm hR_div_summable
    _ = (∑' n, R n) / W := by
      simp_rw [div_eq_mul_inv]
      rw [tsum_mul_right]
    _ ≤ C * x ^ 5 / W :=
      div_le_div_of_nonneg_right hRpoly hW_pos.le

end PrimeNumberTheorem
