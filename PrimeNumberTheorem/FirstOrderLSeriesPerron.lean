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

end PrimeNumberTheorem
