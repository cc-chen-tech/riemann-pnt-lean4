import PrimeNumberTheorem.GlobalZeroCount
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Complex Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ExplicitFormulaAux

/-!
# Spatial variation of the finite explicit formula

At a fixed truncation height, each normalized zero term has derivative
`x ^ (rho - 1)`.  The critical-strip bound `rho.re < 1` makes this derivative
uniformly bounded on `x >= 1`.  Summing analytic multiplicities gives a
Lipschitz constant equal to the total zero multiplicity below the truncation.
-/

/-- A single nontrivial-zero term is `1`-Lipschitz on the positive ray
`[1, infinity)`.  The division by `rho` is exactly cancelled by
differentiation. -/
theorem norm_zeroTerm_sub_zeroTerm_le_abs_sub
    {rho : ℂ} (hrho : RiemannHypothesis.IsNontrivialZero rho)
    {x m : ℝ} (hx : 1 ≤ x) (hm : 1 ≤ m) :
    ‖(x : ℂ) ^ rho / rho - (m : ℂ) ^ rho / rho‖ ≤
      |x - m| := by
  have hrho0 : rho ≠ 0 := by
    intro hrhoEq
    have hre := congrArg Complex.re hrhoEq
    simp at hre
    linarith [hrho.2.1]
  let f : ℝ → ℂ := fun y => (y : ℂ) ^ rho / rho
  have hderiv :
      ∀ y ∈ Ici (1 : ℝ),
        HasDerivWithinAt f ((y : ℂ) ^ (rho - 1)) (Ici (1 : ℝ)) y := by
    intro y hy
    have hy0 : y ≠ 0 := by
      have hy1 : 1 ≤ y := hy
      linarith
    have hpow :=
      (hasDerivAt_ofReal_cpow_const hy0 hrho0).div_const rho
    have hpow' :
        HasDerivAt f ((y : ℂ) ^ (rho - 1)) y := by
      simpa [f, hrho0, mul_div_assoc] using hpow
    exact hpow'.hasDerivWithinAt
  have hbound :
      ∀ y ∈ Ici (1 : ℝ), ‖(y : ℂ) ^ (rho - 1)‖ ≤ (1 : ℝ) := by
    intro y hy
    have hypos : 0 < y := zero_lt_one.trans_le hy
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hypos, sub_re, one_re]
    exact
      Real.rpow_le_one_of_one_le_of_nonpos hy
        (sub_nonpos.mpr hrho.2.2.le)
  have hmv :=
    (convex_Ici (1 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound hm hx
  simpa [f, Real.norm_eq_abs] using hmv

/-- The multiplicity-aware finite zero sum is Lipschitz in its spatial
variable.  Its Lipschitz constant is the total analytic multiplicity of the
zeros included at height `T`. -/
theorem norm_finiteNontrivialZeroSumWithMultiplicity_sub_le
    {x m T : ℝ} (hx : 1 ≤ x) (hm : 1 ≤ m) :
    ‖finiteNontrivialZeroSumWithMultiplicity x T -
        finiteNontrivialZeroSumWithMultiplicity m T‖ ≤
      globalZeroMultiplicity T * |x - m| := by
  classical
  unfold finiteNontrivialZeroSumWithMultiplicity
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ rho ∈ nontrivialZerosFinset T,
        ((analyticOrderNatAt riemannZeta rho : ℂ) * (x : ℂ) ^ rho / rho -
          (analyticOrderNatAt riemannZeta rho : ℂ) * (m : ℂ) ^ rho / rho)‖
        ≤
      ∑ rho ∈ nontrivialZerosFinset T,
        ‖(analyticOrderNatAt riemannZeta rho : ℂ) * (x : ℂ) ^ rho / rho -
          (analyticOrderNatAt riemannZeta rho : ℂ) * (m : ℂ) ^ rho / rho‖ := by
      exact norm_sum_le _ _
    _ ≤
      ∑ rho ∈ nontrivialZerosFinset T,
        (analyticOrderNatAt riemannZeta rho : ℝ) * |x - m| := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hzero := (mem_nontrivialZerosFinset.mp hrho).1
      have hsingle :=
        norm_zeroTerm_sub_zeroTerm_le_abs_sub hzero hx hm
      calc
        ‖(analyticOrderNatAt riemannZeta rho : ℂ) * (x : ℂ) ^ rho / rho -
            (analyticOrderNatAt riemannZeta rho : ℂ) * (m : ℂ) ^ rho / rho‖ =
            ‖(analyticOrderNatAt riemannZeta rho : ℂ) *
              ((x : ℂ) ^ rho / rho - (m : ℂ) ^ rho / rho)‖ := by
              congr 1
              ring
        _ = (analyticOrderNatAt riemannZeta rho : ℝ) *
              ‖(x : ℂ) ^ rho / rho - (m : ℂ) ^ rho / rho‖ := by
              rw [norm_mul]
              simp
        _ ≤ (analyticOrderNatAt riemannZeta rho : ℝ) * |x - m| :=
          mul_le_mul_of_nonneg_left hsingle (Nat.cast_nonneg _)
    _ = globalZeroMultiplicity T * |x - m| := by
      unfold globalZeroMultiplicity
      rw [Finset.sum_mul]

/-- The spatially moving part of the height-`T` explicit formula, consisting
of the main term and the finite multiplicity-weighted zero sum, has
Lipschitz constant `1 + globalZeroMultiplicity T` on `x >= 1`. -/
theorem norm_main_sub_finiteZeroSum_sub_le
    {x m T : ℝ} (hx : 1 ≤ x) (hm : 1 ≤ m) :
    ‖((x : ℂ) - finiteNontrivialZeroSumWithMultiplicity x T) -
        ((m : ℂ) - finiteNontrivialZeroSumWithMultiplicity m T)‖ ≤
      (1 + globalZeroMultiplicity T) * |x - m| := by
  have hzero :=
    norm_finiteNontrivialZeroSumWithMultiplicity_sub_le
      (T := T) hx hm
  calc
    ‖((x : ℂ) - finiteNontrivialZeroSumWithMultiplicity x T) -
        ((m : ℂ) - finiteNontrivialZeroSumWithMultiplicity m T)‖ =
        ‖((x : ℂ) - (m : ℂ)) -
          (finiteNontrivialZeroSumWithMultiplicity x T -
            finiteNontrivialZeroSumWithMultiplicity m T)‖ := by
          congr 1
          ring
    _ ≤ ‖(x : ℂ) - (m : ℂ)‖ +
          ‖finiteNontrivialZeroSumWithMultiplicity x T -
            finiteNontrivialZeroSumWithMultiplicity m T‖ :=
      norm_sub_le _ _
    _ ≤ |x - m| + globalZeroMultiplicity T * |x - m| := by
      rw [← ofReal_sub, norm_real, Real.norm_eq_abs]
      exact add_le_add_right hzero _
    _ = (1 + globalZeroMultiplicity T) * |x - m| := by ring

/-- Uniform `O(T log T)` spatial variation of the moving finite-height
explicit formula.  The constant is absolute and the estimate is simultaneous
in both spatial samples. -/
theorem exists_norm_main_sub_finiteZeroSum_sub_le_mul_log :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {x m T : ℝ}, 1 ≤ x → 1 ≤ m → 4 ≤ T →
        ‖((x : ℂ) - finiteNontrivialZeroSumWithMultiplicity x T) -
            ((m : ℂ) - finiteNontrivialZeroSumWithMultiplicity m T)‖ ≤
          (1 + C * T * (1 + Real.log (T + 6))) * |x - m| := by
  rcases exists_globalZeroMultiplicity_le_mul_log with
    ⟨C, hC, hglobal⟩
  refine ⟨C, hC, ?_⟩
  intro x m T hx hm hT
  apply (norm_main_sub_finiteZeroSum_sub_le
    (T := T) hx hm).trans
  have hcoef :
      1 + globalZeroMultiplicity T ≤
        1 + C * T * (1 + Real.log (T + 6)) := by
    linarith [hglobal T hT]
  exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)

end ExplicitFormulaAux
end PrimeNumberTheorem
