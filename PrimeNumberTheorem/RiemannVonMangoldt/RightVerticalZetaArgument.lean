import PrimeNumberTheorem.RiemannVonMangoldt.HalfBoundary
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open Complex MeasureTheory Set Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt

private theorem summable_one_div_nat_add_two_sq :
    Summable (fun n : ℕ => 1 / (n + 2 : ℝ) ^ 2) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
    simpa [Real.rpow_two] using
      ((Real.summable_one_div_nat_rpow).mpr (by norm_num : (1 : ℝ) < 2))
  convert (summable_nat_add_iff 2).mpr hbase using 1 with n
  norm_num

private theorem riemannZeta_sub_one_eq_tail (t : ℝ) :
    riemannZeta ((2 : ℂ) + (t : ℂ) * I) - 1 =
      ∑' n : ℕ, 1 / (n + 2 : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I) := by
  let s : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hs : 1 < s.re := by simp [s]
  have hseries : Summable (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) := by
    rw [show (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) =
      fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s by
        funext n
        norm_num]
    exact (summable_nat_add_iff 1).mpr
      ((Complex.summable_one_div_nat_cpow).mpr hs)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, hseries.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, one_cpow, div_one, add_sub_cancel_left]
  congr 1
  funext n
  congr 2
  push_cast
  ring

private theorem tsum_one_div_nat_add_two_sq :
    (∑' n : ℕ, 1 / (n + 2 : ℝ) ^ 2) = Real.pi ^ 2 / 6 - 1 := by
  have hzeta :
      riemannZeta (2 : ℂ) - 1 =
        ∑' n : ℕ, 1 / (n + 2 : ℂ) ^ (2 : ℂ) := by
    simpa using riemannZeta_sub_one_eq_tail 0
  have hcast := Complex.ofRealCLM.map_tsum summable_one_div_nat_add_two_sq
  rw [riemannZeta_two] at hzeta
  apply Complex.ofReal_injective
  change Complex.ofRealCLM (∑' n : ℕ, 1 / (n + 2 : ℝ) ^ 2) =
    ((Real.pi ^ 2 / 6 - 1 : ℝ) : ℂ)
  rw [hcast]
  convert hzeta.symm using 1 <;> norm_num

private theorem summable_zeta_tail (t : ℝ) :
    Summable (fun n : ℕ =>
      1 / (n + 2 : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I)) := by
  let s : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hs : 1 < s.re := by simp [s]
  have hbase := (Complex.summable_one_div_nat_cpow).mpr hs
  convert (summable_nat_add_iff 2).mpr hbase using 1 with n
  simp [s]

private theorem norm_riemannZeta_two_add_mul_I_sub_one_lt_one (t : ℝ) :
    ‖riemannZeta ((2 : ℂ) + (t : ℂ) * I) - 1‖ < 1 := by
  rw [riemannZeta_sub_one_eq_tail]
  calc
    ‖∑' n : ℕ, 1 / (n + 2 : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I)‖ ≤
        ∑' n : ℕ, ‖1 / (n + 2 : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I)‖ :=
      norm_tsum_le_tsum_norm (summable_zeta_tail t).norm
    _ = ∑' n : ℕ, 1 / (n + 2 : ℝ) ^ 2 := by
      apply tsum_congr
      intro n
      have hbase : (n + 2 : ℂ) = ((n + 2 : ℝ) : ℂ) := by norm_num
      rw [norm_div, norm_one, hbase, Complex.norm_cpow_eq_rpow_re_of_pos]
      · simp
      · positivity
    _ = Real.pi ^ 2 / 6 - 1 := tsum_one_div_nat_add_two_sq
    _ < 1 := by
      have hpiSq : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 :=
        (sq_lt_sq₀ Real.pi_pos.le (by norm_num)).2 Real.pi_lt_d2
      nlinarith

private theorem riemannZeta_two_add_mul_I_re_pos (t : ℝ) :
    0 < (riemannZeta ((2 : ℂ) + (t : ℂ) * I)).re := by
  have hre := Complex.abs_re_le_norm
    (riemannZeta ((2 : ℂ) + (t : ℂ) * I) - 1)
  have hdiff :
      -‖riemannZeta ((2 : ℂ) + (t : ℂ) * I) - 1‖ ≤
        (riemannZeta ((2 : ℂ) + (t : ℂ) * I) - 1).re := by
    linarith [neg_abs_le
      (riemannZeta ((2 : ℂ) + (t : ℂ) * I) - 1).re]
  simp only [Complex.sub_re, Complex.one_re] at hdiff
  linarith [norm_riemannZeta_two_add_mul_I_sub_one_lt_one t]

private theorem hasDerivAt_zetaRightVerticalArgument (t : ℝ) :
    HasDerivAt
      (fun x : ℝ =>
        (Complex.log (riemannZeta ((2 : ℂ) + (x : ℂ) * I))).im)
      (logDeriv riemannZeta ((2 : ℂ) + (t : ℂ) * I)).re t := by
  let s : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have hline : HasDerivAt
      (fun x : ℝ => (2 : ℂ) + (x : ℂ) * I) I t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
      ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add (2 : ℂ)
  have hzeta : HasDerivAt
      (fun x : ℝ => riemannZeta ((2 : ℂ) + (x : ℂ) * I))
      (deriv riemannZeta s * I) t := by
    simpa [s] using
      (differentiableAt_riemannZeta hs1).hasDerivAt.comp t hline
  have hslit : riemannZeta s ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (by simpa [s] using riemannZeta_two_add_mul_I_re_pos t)
  have hlog := hzeta.clog_real hslit
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hlog
  convert him using 1
  simp only [Complex.imCLM_apply, logDeriv_apply]
  change (deriv riemannZeta s / riemannZeta s).re =
    (deriv riemannZeta s * I / riemannZeta s).im
  rw [show deriv riemannZeta s * I / riemannZeta s =
    I * (deriv riemannZeta s / riemannZeta s) by ring]
  simp

private theorem intervalIntegrable_zetaRightVerticalArgument (U T : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        (logDeriv riemannZeta ((2 : ℂ) + (t : ℂ) * I)).re)
      volume U T := by
  apply ContinuousOn.intervalIntegrable
  intro t _ht
  let s : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have han := ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_one_le_re_of_ne_one
    (z := s) (by simp [s]) hs1
  have hmap : ContinuousAt
      (fun x : ℝ => (2 : ℂ) + (x : ℂ) * I) t := by fun_prop
  have hcomp : ContinuousAt
      (fun x : ℝ => logDeriv riemannZeta ((2 : ℂ) + (x : ℂ) * I)) t :=
    han.continuousAt.comp_of_eq hmap rfl
  exact (Complex.continuous_re.continuousAt.comp_of_eq hcomp rfl).continuousWithinAt

/-- The branch-free zeta argument variation on the line `Re(s)=2`. -/
noncomputable def zetaRightVerticalArgumentVariation (U T : ℝ) : ℝ :=
  ∫ t in U..T,
    (logDeriv riemannZeta ((2 : ℂ) + (t : ℂ) * I)).re

/-- The zeta argument on `Re(s)=2` stays in `(-pi/2, pi/2)`, so its total
variation between any two heights is at most `pi`. -/
theorem abs_zetaRightVerticalArgumentVariation_le_pi (U T : ℝ) :
    |zetaRightVerticalArgumentVariation U T| ≤ Real.pi := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ht => hasDerivAt_zetaRightVerticalArgument t)
    (intervalIntegrable_zetaRightVerticalArgument U T)
  have hvariation : zetaRightVerticalArgumentVariation U T =
      (riemannZeta ((2 : ℂ) + (T : ℂ) * I)).arg -
        (riemannZeta ((2 : ℂ) + (U : ℂ) * I)).arg := by
    rw [zetaRightVerticalArgumentVariation, hFTC]
    simp only [Complex.log_im]
  rw [hvariation]
  have hTarg :
      |(riemannZeta ((2 : ℂ) + (T : ℂ) * I)).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr
      (Or.inl (riemannZeta_two_add_mul_I_re_pos T))
  have hUarg :
      |(riemannZeta ((2 : ℂ) + (U : ℂ) * I)).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr
      (Or.inl (riemannZeta_two_add_mul_I_re_pos U))
  apply le_of_lt
  calc
    |(riemannZeta ((2 : ℂ) + (T : ℂ) * I)).arg -
        (riemannZeta ((2 : ℂ) + (U : ℂ) * I)).arg| ≤
      |(riemannZeta ((2 : ℂ) + (T : ℂ) * I)).arg| +
        |(riemannZeta ((2 : ℂ) + (U : ℂ) * I)).arg| :=
      abs_sub _ _
    _ < Real.pi / 2 + Real.pi / 2 := add_lt_add hTarg hUarg
    _ = Real.pi := by ring

end RiemannVonMangoldt
end PrimeNumberTheorem
