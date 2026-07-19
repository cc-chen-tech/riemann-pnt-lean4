import HardyTheorem.OscillatoryIntegral
import Mathlib.Analysis.Calculus.MeanValue

open Set

namespace HardyTheorem.OscillatoryIntegral

/-- The real logarithm is `1 / T`-Lipschitz on `[T, ∞)` when `T > 0`. -/
theorem abs_log_sub_log_le_div
    {T x y : ℝ} (hT : 0 < T) (hx : T ≤ x) (hy : T ≤ y) :
    |Real.log y - Real.log x| ≤ |y - x| / T := by
  have hdiff : ∀ z ∈ Ici T, DifferentiableAt ℝ Real.log z := by
    intro z hz
    exact Real.differentiableAt_log (ne_of_gt (hT.trans_le hz))
  have hderiv : ∀ z ∈ Ici T, ‖deriv Real.log z‖ ≤ 1 / T := by
    intro z hz
    have hzpos : 0 < z := hT.trans_le hz
    rw [Real.deriv_log, Real.norm_eq_abs, abs_inv, abs_of_pos hzpos]
    simpa only [one_div] using one_div_le_one_div_of_le hT hz
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    hdiff hderiv (convex_Ici T) hx hy
  simpa only [Real.norm_eq_abs, div_eq_mul_inv, one_mul, mul_one, mul_comm] using h

/-- The phase occurring in a shifted cross term of the Hardy first model. -/
noncomputable def hardyPhaseCorrelation
    (m n : ℕ) (v w t : ℝ) : ℝ :=
  hardyPhase m (t + v) - hardyPhase n (t + w)

/-- The first derivative of a shifted Hardy-phase correlation. -/
theorem deriv_hardyPhaseCorrelation
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {v w t : ℝ} (htv : 0 < t + v) (htw : 0 < t + w) :
    deriv (hardyPhaseCorrelation m n v w) t =
      (1 / 2) * Real.log
          ((t + v) / (2 * Real.pi * ((m : ℝ) ^ 2))) -
        (1 / 2) * Real.log
          ((t + w) / (2 * Real.pi * ((n : ℝ) ^ 2))) := by
  have hmDiff : DifferentiableAt ℝ (fun x : ℝ => hardyPhase m (x + v)) t :=
    by
      simpa [Function.comp_def] using
        (((contDiffAt_hardyPhase_two hm htv).differentiableAt (by norm_num)).comp t
          ((hasDerivAt_id t).add_const v).differentiableAt)
  have hnDiff : DifferentiableAt ℝ (fun x : ℝ => hardyPhase n (x + w)) t :=
    by
      simpa [Function.comp_def] using
        (((contDiffAt_hardyPhase_two hn htw).differentiableAt (by norm_num)).comp t
          ((hasDerivAt_id t).add_const w).differentiableAt)
  unfold hardyPhaseCorrelation
  rw [deriv_fun_sub hmDiff hnDiff, deriv_comp_add_const,
    deriv_comp_add_const, deriv_hardyPhase hm htv,
    deriv_hardyPhase hn htw]

/-- The second derivative of a shifted Hardy-phase correlation is the
difference of two reciprocal heights. In particular, the dependence on the
Dirichlet indices disappears after two derivatives. -/
theorem iteratedDeriv_two_hardyPhaseCorrelation
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {v w t : ℝ} (htv : 0 < t + v) (htw : 0 < t + w) :
    iteratedDeriv 2 (hardyPhaseCorrelation m n v w) t =
      1 / (2 * (t + v)) - 1 / (2 * (t + w)) := by
  have hmCont : ContDiffAt ℝ 2 (fun x : ℝ => hardyPhase m (x + v)) t :=
    (contDiffAt_hardyPhase_two hm htv).comp t
      (contDiffAt_id.add contDiffAt_const)
  have hnCont : ContDiffAt ℝ 2 (fun x : ℝ => hardyPhase n (x + w)) t :=
    (contDiffAt_hardyPhase_two hn htw).comp t
      (contDiffAt_id.add contDiffAt_const)
  unfold hardyPhaseCorrelation
  rw [iteratedDeriv_fun_sub hmCont hnCont]
  rw [show iteratedDeriv 2 (fun x : ℝ => hardyPhase m (x + v)) t =
      iteratedDeriv 2 (hardyPhase m) (t + v) by
        exact congrFun (iteratedDeriv_comp_add_const
          (n := 2) (f := hardyPhase m) (s := v)) t]
  rw [show iteratedDeriv 2 (fun x : ℝ => hardyPhase n (x + w)) t =
      iteratedDeriv 2 (hardyPhase n) (t + w) by
        exact congrFun (iteratedDeriv_comp_add_const
          (n := 2) (f := hardyPhase n) (s := w)) t]
  rw [iteratedDeriv_two_hardyPhase hm htv,
    iteratedDeriv_two_hardyPhase hn htw]

/-- With equal shifts, the nonlinear common phase cancels completely: the
correlation derivative is the constant logarithmic frequency gap. -/
theorem deriv_hardyPhaseCorrelation_same_shift
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {v t : ℝ} (htv : 0 < t + v) :
    deriv (hardyPhaseCorrelation m n v v) t =
      Real.log n - Real.log m := by
  rw [deriv_hardyPhaseCorrelation hm hn htv htv]
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have htpos : 0 < t + v := htv
  rw [Real.log_div (ne_of_gt htpos) (by positivity),
    Real.log_div (ne_of_gt htpos) (by positivity)]
  rw [Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (by positivity : (m : ℝ) ^ 2 ≠ 0),
    Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (by positivity : (n : ℝ) ^ 2 ≠ 0)]
  rw [Real.log_pow]
  rw [Real.log_pow]
  ring

/-- A shifted correlation derivative is its logarithmic frequency gap plus
a height-shift correction. -/
theorem deriv_hardyPhaseCorrelation_eq_log_gap_add
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {v w t : ℝ} (htv : 0 < t + v) (htw : 0 < t + w) :
    deriv (hardyPhaseCorrelation m n v w) t =
      (Real.log n - Real.log m) +
        (1 / 2) * (Real.log (t + v) - Real.log (t + w)) := by
  rw [deriv_hardyPhaseCorrelation hm hn htv htw]
  rw [Real.log_div (ne_of_gt htv) (by positivity),
    Real.log_div (ne_of_gt htw) (by positivity)]
  rw [Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (by positivity : (m : ℝ) ^ 2 ≠ 0),
    Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (by positivity : (n : ℝ) ^ 2 ≠ 0)]
  rw [Real.log_pow, Real.log_pow]
  ring

/-- On a positive-height strip, shifting the two arguments changes the
correlation frequency by at most `|v-w| / (2T)`. -/
theorem abs_deriv_hardyPhaseCorrelation_sub_log_gap_le
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {T v w t : ℝ} (hT : 0 < T)
    (htv : T ≤ t + v) (htw : T ≤ t + w) :
    |deriv (hardyPhaseCorrelation m n v w) t -
        (Real.log n - Real.log m)| ≤
      |v - w| / (2 * T) := by
  have htvpos : 0 < t + v := hT.trans_le htv
  have htwpos : 0 < t + w := hT.trans_le htw
  rw [deriv_hardyPhaseCorrelation_eq_log_gap_add hm hn htvpos htwpos]
  have hlog := abs_log_sub_log_le_div hT htw htv
  calc
    |(Real.log n - Real.log m +
          1 / 2 * (Real.log (t + v) - Real.log (t + w))) -
        (Real.log n - Real.log m)| =
        (1 / 2) * |Real.log (t + v) - Real.log (t + w)| := by
      rw [show (Real.log n - Real.log m +
          1 / 2 * (Real.log (t + v) - Real.log (t + w))) -
          (Real.log n - Real.log m) =
          1 / 2 * (Real.log (t + v) - Real.log (t + w)) by ring]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ (1 / 2) * (|(t + v) - (t + w)| / T) := by
      gcongr
    _ = |v - w| / (2 * T) := by
      rw [show (t + v) - (t + w) = v - w by ring]
      field_simp

end HardyTheorem.OscillatoryIntegral
