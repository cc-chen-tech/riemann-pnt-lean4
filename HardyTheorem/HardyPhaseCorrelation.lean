import HardyTheorem.OscillatoryIntegral

open Set

namespace HardyTheorem.OscillatoryIntegral

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

end HardyTheorem.OscillatoryIntegral
