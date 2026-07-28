import PrimeNumberTheorem.ZeroDensityCount
import PrimeNumberTheorem.ZeroForcedOscillationComplementaryBound
import PrimeNumberTheorem.CarlsonAsymptotic

open Complex MeasureTheory Set
open Filter Asymptotics
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- Positive-height zeros counted by `zeroDensityCount`, with the selected
target zero removed. Multiplicity remains attached to each point in the sums
below. -/
def positiveZeroDensityResidualFinset
    (rho0 : ℂ) (sigma T : ℝ) : Finset ℂ :=
  (ZeroDensity.zeroDensityZerosFinset sigma T).erase rho0

/-- The positive-height zero-density package after deleting `rho0`, normalized
by the growth scale `exp (beta * y)`. This is a finite explicit-formula zero
sum; it does not include the negative-height conjugates or contour remainder. -/
def normalizedPositiveZeroDensityResidualContribution
    (rho0 : ℂ) (beta sigma T y : ℝ) : ℂ :=
  (Real.exp (-beta * y) : ℂ) *
    ∑ rho ∈ positiveZeroDensityResidualFinset rho0 sigma T,
      (analyticOrderNatAt riemannZeta rho : ℂ) *
        (Real.exp y : ℂ) ^ rho / rho

/-- After removing the target zero, a uniform real-part gap controls the
normalized positive-height residual by the multiplicity count. The factor `2`
uses only `Re rho > sigma ≥ 1/2`, hence `1 / ‖rho‖ < 2`. -/
theorem norm_normalizedPositiveZeroDensityResidualContribution_le_count
    {rho0 : ℂ} {beta sigma T delta y : ℝ}
    (hsigma : 1 / 2 ≤ sigma)
    (hy : 0 ≤ y)
    (hgap : ∀ rho ∈ positiveZeroDensityResidualFinset rho0 sigma T,
      rho.re ≤ beta - delta) :
    ‖normalizedPositiveZeroDensityResidualContribution
        rho0 beta sigma T y‖ ≤
      2 * Real.exp (-delta * y) *
        (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
  classical
  let S : ℂ :=
    ∑ rho ∈ positiveZeroDensityResidualFinset rho0 sigma T,
      (analyticOrderNatAt riemannZeta rho : ℂ) *
        (Real.exp y : ℂ) ^ rho / rho
  have hsum :
      ‖S‖ ≤
        2 * Real.exp ((beta - delta) * y) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
    calc
      ‖S‖ ≤
          ∑ rho ∈ positiveZeroDensityResidualFinset rho0 sigma T,
            ‖(analyticOrderNatAt riemannZeta rho : ℂ) *
                (Real.exp y : ℂ) ^ rho / rho‖ := by
        dsimp only [S]
        exact norm_sum_le _ _
      _ = ∑ rho ∈ positiveZeroDensityResidualFinset rho0 sigma T,
            (analyticOrderNatAt riemannZeta rho : ℝ) *
              (Real.exp y) ^ rho.re / ‖rho‖ := by
        refine Finset.sum_congr rfl fun rho _ => ?_
        exact ZeroForcedOscillation.norm_natCast_mul_cpow_div
          (Real.exp y) (Real.exp_pos y) rho _
      _ ≤ ∑ rho ∈ positiveZeroDensityResidualFinset rho0 sigma T,
            2 * Real.exp ((beta - delta) * y) *
              (analyticOrderNatAt riemannZeta rho : ℝ) := by
        refine Finset.sum_le_sum fun rho hrho => ?_
        have hrhoFull :
            rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T :=
          Finset.mem_of_mem_erase hrho
        have hre : sigma < rho.re :=
          (ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoFull).2.2.2
        have hreHalf : 1 / 2 < rho.re := lt_of_le_of_lt hsigma hre
        have hnormHalf : 1 / 2 < ‖rho‖ :=
          hreHalf.trans_le
            ((le_abs_self rho.re).trans (Complex.abs_re_le_norm rho))
        have hinv : 1 / ‖rho‖ ≤ (2 : ℝ) := by
          have h :=
            one_div_le_one_div_of_le
              (by norm_num : (0 : ℝ) < 1 / 2) hnormHalf.le
          norm_num at h ⊢
          exact h
        have hexp :
            (Real.exp y) ^ rho.re ≤
              Real.exp ((beta - delta) * y) := by
          rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp,
            mul_comm y rho.re]
          exact Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_right (hgap rho hrho) hy)
        have hcoeff :
            0 ≤ (analyticOrderNatAt riemannZeta rho : ℝ) *
              (Real.exp y) ^ rho.re :=
          mul_nonneg (Nat.cast_nonneg _)
            (Real.rpow_nonneg (Real.exp_pos y).le _)
        have hcoeffExp :
            (analyticOrderNatAt riemannZeta rho : ℝ) *
                (Real.exp y) ^ rho.re ≤
              (analyticOrderNatAt riemannZeta rho : ℝ) *
                Real.exp ((beta - delta) * y) :=
          mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)
        calc
          (analyticOrderNatAt riemannZeta rho : ℝ) *
                (Real.exp y) ^ rho.re / ‖rho‖ =
              ((analyticOrderNatAt riemannZeta rho : ℝ) *
                (Real.exp y) ^ rho.re) * (1 / ‖rho‖) := by ring
          _ ≤ ((analyticOrderNatAt riemannZeta rho : ℝ) *
                (Real.exp y) ^ rho.re) * 2 :=
            mul_le_mul_of_nonneg_left hinv hcoeff
          _ ≤ ((analyticOrderNatAt riemannZeta rho : ℝ) *
                Real.exp ((beta - delta) * y)) * 2 := by
            exact mul_le_mul_of_nonneg_right hcoeffExp (by norm_num)
          _ = 2 * Real.exp ((beta - delta) * y) *
                (analyticOrderNatAt riemannZeta rho : ℝ) := by ring
      _ = 2 * Real.exp ((beta - delta) * y) *
            ∑ rho ∈ positiveZeroDensityResidualFinset rho0 sigma T,
              (analyticOrderNatAt riemannZeta rho : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * Real.exp ((beta - delta) * y) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset rho0
              (ZeroDensity.zeroDensityZerosFinset sigma T))
            (fun _ _ _ => Nat.zero_le _)
        · positivity
  calc
    ‖normalizedPositiveZeroDensityResidualContribution
          rho0 beta sigma T y‖ =
        Real.exp (-beta * y) * ‖S‖ := by
      simp only [normalizedPositiveZeroDensityResidualContribution, S,
        norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-beta * y) *
          (2 * Real.exp ((beta - delta) * y) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _)
    _ = 2 * Real.exp (-delta * y) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
      calc
        Real.exp (-beta * y) *
              (2 * Real.exp ((beta - delta) * y) *
                (ZeroDensity.zeroDensityCount sigma T : ℝ)) =
            2 * (Real.exp (-beta * y) *
              Real.exp ((beta - delta) * y)) *
                (ZeroDensity.zeroDensityCount sigma T : ℝ) := by ring
        _ = 2 * Real.exp (-delta * y) *
              (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
          rw [← Real.exp_add]
          congr 3
          ring

/-- Squaring and integrating the pointwise residual bound gives an ordinary
local `L²` upper bound. No frequency separation is used; the cost is the square
of the zero-density count. -/
theorem
    integral_normSq_normalizedPositiveZeroDensityResidualContribution_le_count_sq
    {rho0 : ℂ} {beta sigma T delta a b : ℝ}
    (hsigma : 1 / 2 ≤ sigma)
    (hdelta : 0 ≤ delta)
    (ha : 0 ≤ a)
    (hab : a ≤ b)
    (hgap : ∀ rho ∈ positiveZeroDensityResidualFinset rho0 sigma T,
      rho.re ≤ beta - delta) :
    (∫ y in Icc a b,
      Complex.normSq
        (normalizedPositiveZeroDensityResidualContribution
          rho0 beta sigma T y)) ≤
      4 * (b - a) * Real.exp (-2 * delta * a) *
        (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2 := by
  classical
  let C : ℝ :=
    4 * Real.exp (-2 * delta * a) *
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2
  have hcontinuous :
      Continuous fun y : ℝ =>
        normalizedPositiveZeroDensityResidualContribution
          rho0 beta sigma T y := by
    dsimp only [normalizedPositiveZeroDensityResidualContribution]
    simp_rw [
      ZeroForcedOscillation.realExp_cpow_eq_growth_mul_oscillation
        _ _ _ rfl]
    fun_prop
  have hintegrable :
      IntegrableOn
        (fun y : ℝ =>
          Complex.normSq
            (normalizedPositiveZeroDensityResidualContribution
              rho0 beta sigma T y))
        (Icc a b) :=
    (Complex.continuous_normSq.comp hcontinuous).integrableOn_Icc
  have hpoint (y : ℝ) (hy : y ∈ Icc a b) :
      Complex.normSq
          (normalizedPositiveZeroDensityResidualContribution
            rho0 beta sigma T y) ≤ C := by
    have hnorm :=
      norm_normalizedPositiveZeroDensityResidualContribution_le_count
        (rho0 := rho0) (beta := beta) (sigma := sigma) (T := T)
        (delta := delta) (y := y) hsigma (ha.trans hy.1) hgap
    have hexp :
        Real.exp (-delta * y) ≤ Real.exp (-delta * a) := by
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left hy.1 (neg_nonpos.mpr hdelta))
    have hbound :
        ‖normalizedPositiveZeroDensityResidualContribution
            rho0 beta sigma T y‖ ≤
          2 * Real.exp (-delta * a) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
      exact hnorm.trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp (by norm_num))
          (Nat.cast_nonneg _))
    rw [Complex.normSq_eq_norm_sq]
    dsimp only [C]
    have hsquare :
        ‖normalizedPositiveZeroDensityResidualContribution
            rho0 beta sigma T y‖ ^ 2 ≤
          (2 * Real.exp (-delta * a) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) ^ 2 :=
      pow_le_pow_left₀
        (norm_nonneg
          (normalizedPositiveZeroDensityResidualContribution
            rho0 beta sigma T y))
        hbound 2
    calc
      ‖normalizedPositiveZeroDensityResidualContribution
            rho0 beta sigma T y‖ ^ 2 ≤
          (2 * Real.exp (-delta * a) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) ^ 2 := hsquare
      _ = 4 * Real.exp (-delta * a) ^ 2 *
            (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2 := by ring
      _ = 4 * Real.exp (-2 * delta * a) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2 := by
        rw [show Real.exp (-delta * a) ^ 2 =
            Real.exp (-2 * delta * a) by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring]
  have hconstantIntegrable :
      IntegrableOn (fun _y : ℝ => C) (Icc a b) :=
    integrableOn_const (μ := volume) (s := Icc a b)
      measure_Icc_lt_top.ne
  have hmono :
      (∫ y in Icc a b,
          Complex.normSq
            (normalizedPositiveZeroDensityResidualContribution
              rho0 beta sigma T y)) ≤
        ∫ _y in Icc a b, C := by
    apply integral_mono_ae hintegrable hconstantIntegrable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact hpoint y hy
  calc
    (∫ y in Icc a b,
        Complex.normSq
          (normalizedPositiveZeroDensityResidualContribution
            rho0 beta sigma T y)) ≤
        ∫ _y in Icc a b, C := hmono
    _ = C * (b - a) := by
      rw [integral_const]
      change
        (volume.restrict (Icc a b)).real Set.univ * C =
          C * (b - a)
      rw [Measure.real, Measure.restrict_apply_univ,
        Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
      ring
    _ = 4 * (b - a) * Real.exp (-2 * delta * a) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2 := by
      dsimp only [C]
      ring

/-- A pointwise exponential upper bound for the zero count converts the
count-squared estimate into a residual decay estimate. The exponent
`delta - kappa` is the exact competition between the real-part gap and the
growth rate of the number of residual zeros. -/
theorem
    integral_normSq_normalizedPositiveZeroDensityResidualContribution_le_of_count_exp
    {rho0 : ℂ} {beta sigma T delta a b C kappa : ℝ}
    (hsigma : 1 / 2 ≤ sigma)
    (hdelta : 0 ≤ delta)
    (ha : 0 ≤ a)
    (hab : a ≤ b)
    (hgap : ∀ rho ∈ positiveZeroDensityResidualFinset rho0 sigma T,
      rho.re ≤ beta - delta)
    (hcount :
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        C * Real.exp (kappa * a)) :
    (∫ y in Icc a b,
      Complex.normSq
        (normalizedPositiveZeroDensityResidualContribution
          rho0 beta sigma T y)) ≤
      4 * (b - a) * C ^ 2 *
        Real.exp (-2 * (delta - kappa) * a) := by
  have hbase :=
    integral_normSq_normalizedPositiveZeroDensityResidualContribution_le_count_sq
      (rho0 := rho0) (beta := beta) (sigma := sigma) (T := T)
      (delta := delta) (a := a) (b := b)
      hsigma hdelta ha hab hgap
  have hcountSq :
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2 ≤
        (C * Real.exp (kappa * a)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 2
  calc
    (∫ y in Icc a b,
        Complex.normSq
          (normalizedPositiveZeroDensityResidualContribution
            rho0 beta sigma T y)) ≤
        4 * (b - a) * Real.exp (-2 * delta * a) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2 := hbase
    _ ≤ 4 * (b - a) * Real.exp (-2 * delta * a) *
          (C * Real.exp (kappa * a)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hcountSq
        (mul_nonneg
          (mul_nonneg (by norm_num) (sub_nonneg.mpr hab))
          (Real.exp_nonneg _))
    _ = 4 * (b - a) * Real.exp (-2 * delta * a) *
          (C ^ 2 * Real.exp (2 * kappa * a)) := by
      rw [mul_pow, show Real.exp (kappa * a) ^ 2 =
          Real.exp (2 * kappa * a) by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring]
    _ = 4 * (b - a) * C ^ 2 *
          Real.exp (-2 * (delta - kappa) * a) := by
      calc
        4 * (b - a) * Real.exp (-2 * delta * a) *
              (C ^ 2 * Real.exp (2 * kappa * a)) =
            4 * (b - a) * C ^ 2 *
              (Real.exp (-2 * delta * a) *
                Real.exp (2 * kappa * a)) := by ring
        _ = _ := by
          rw [← Real.exp_add]
          congr 2
          ring

/-- Carlson's fixed-line estimate, evaluated at the exponential height
`T = exp (tau * a)`. The logarithmic fourth power is absorbed into an
arbitrarily small exponential loss `eta`. -/
theorem eventually_zeroDensityCount_exp_height_le_of_carlson
    {sigma tau eta : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (htau : 0 < tau)
    (heta : 0 < eta) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ a : ℝ in atTop,
        (ZeroDensity.zeroDensityCount sigma
            (Real.exp (tau * a)) : ℝ) ≤
          C * Real.exp
            ((4 * sigma * (1 - sigma) * tau + eta) * a) := by
  let q : ℝ := 4 * sigma * (1 - sigma)
  rcases
      (CarlsonZeroDensity.carlson_zeroDensity_isBigO
        hsigma hsigmaOne).bound with
    ⟨C0, hC0⟩
  have hheight :
      Tendsto (fun a : ℝ => Real.exp (tau * a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      ((tendsto_const_mul_atTop_of_pos htau).2 tendsto_id)
  have hCarlson :
      ∀ᶠ a : ℝ in atTop,
        ‖(ZeroDensity.zeroDensityCount sigma
            (Real.exp (tau * a)) : ℝ)‖ ≤
          C0 *
            ‖(Real.exp (tau * a)) ^ q *
              Real.log (Real.exp (tau * a)) ^ (4 : ℕ)‖ :=
    hheight.eventually hC0
  have hpoly :
      ∀ᶠ a : ℝ in atTop,
        a ^ (4 : ℕ) ≤ Real.exp (eta * a) := by
    have h :=
      (isLittleO_pow_exp_pos_mul_atTop (4 : ℕ) heta).bound
        (by norm_num : (0 : ℝ) < 1)
    filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with a haBound ha
    simpa [Real.norm_eq_abs, abs_of_pos ha, abs_of_pos (Real.exp_pos _)]
      using haBound
  refine ⟨|C0| * tau ^ 4, by positivity, ?_⟩
  filter_upwards [hCarlson, hpoly, eventually_gt_atTop (0 : ℝ)] with
    a hCarlsonA hpolyA ha
  have htauA : 0 < tau * a := mul_pos htau ha
  have hq : 0 < q := by
    dsimp only [q]
    have hsigmaPos : 0 < sigma := by linarith
    have honeSubPos : 0 < 1 - sigma := sub_pos.mpr hsigmaOne
    positivity
  have hmodelNonneg :
      0 ≤ (Real.exp (tau * a)) ^ q *
        Real.log (Real.exp (tau * a)) ^ (4 : ℕ) :=
    mul_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _)
      (by positivity)
  have hCarlsonA' :
      (ZeroDensity.zeroDensityCount sigma
          (Real.exp (tau * a)) : ℝ) ≤
        |C0| *
          ((Real.exp (tau * a)) ^ q *
            Real.log (Real.exp (tau * a)) ^ (4 : ℕ)) := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg hmodelNonneg] at hCarlsonA
    exact hCarlsonA.trans
      (mul_le_mul_of_nonneg_right (le_abs_self C0) hmodelNonneg)
  calc
    (ZeroDensity.zeroDensityCount sigma
          (Real.exp (tau * a)) : ℝ) ≤
        |C0| *
          ((Real.exp (tau * a)) ^ q *
            Real.log (Real.exp (tau * a)) ^ (4 : ℕ)) := hCarlsonA'
    _ = |C0| * Real.exp (q * tau * a) *
          (tau ^ 4 * a ^ 4) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      ring
    _ ≤ |C0| * Real.exp (q * tau * a) *
          (tau ^ 4 * Real.exp (eta * a)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpolyA
          (by positivity))
        (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
    _ = (|C0| * tau ^ 4) *
          Real.exp ((q * tau + eta) * a) := by
      calc
        |C0| * Real.exp (q * tau * a) *
              (tau ^ 4 * Real.exp (eta * a)) =
            (|C0| * tau ^ 4) *
              (Real.exp (q * tau * a) *
                Real.exp (eta * a)) := by ring
        _ = _ := by
          rw [← Real.exp_add]
          congr 2
          ring
    _ = (|C0| * tau ^ 4) *
          Real.exp
            ((4 * sigma * (1 - sigma) * tau + eta) * a) := by
      rfl

/-- Carlson's count bound inserted into the finite residual `L²` estimate on
the moving window `[a, a + L]`. The only remaining zeta input is the displayed
uniform real-part gap after deleting the selected target zero. -/
theorem
    eventually_integral_normSq_positiveZeroDensityResidual_le_of_carlson
    {rho0 : ℂ} {beta sigma tau eta delta L : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (htau : 0 < tau)
    (heta : 0 < eta)
    (hdelta : 0 ≤ delta)
    (hL : 0 ≤ L)
    (hgap :
      ∀ᶠ a : ℝ in atTop,
        ∀ rho ∈ positiveZeroDensityResidualFinset
            rho0 sigma (Real.exp (tau * a)),
          rho.re ≤ beta - delta) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ a : ℝ in atTop,
        (∫ y in Icc a (a + L),
          Complex.normSq
            (normalizedPositiveZeroDensityResidualContribution
              rho0 beta sigma (Real.exp (tau * a)) y)) ≤
          4 * L * C ^ 2 *
            Real.exp
              (-2 *
                (delta -
                  (4 * sigma * (1 - sigma) * tau + eta)) * a) := by
  rcases eventually_zeroDensityCount_exp_height_le_of_carlson
      hsigma hsigmaOne htau heta with
    ⟨C, hC, hcount⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hgap, hcount, eventually_ge_atTop (0 : ℝ)] with
    a hgapA hcountA ha
  have hbound :=
    integral_normSq_normalizedPositiveZeroDensityResidualContribution_le_of_count_exp
      (rho0 := rho0) (beta := beta) (sigma := sigma)
      (T := Real.exp (tau * a)) (delta := delta)
      (a := a) (b := a + L) (C := C)
      (kappa := 4 * sigma * (1 - sigma) * tau + eta)
      hsigma.le hdelta ha (le_add_of_nonneg_right hL) hgapA hcountA
  simpa only [add_sub_cancel_left] using hbound

/-- The exact parameter gate under which the Carlson-controlled residual
decays exponentially in the logarithmic window center. -/
theorem carlsonResidualDecayRate_pos
    {sigma tau eta delta : ℝ}
    (hgate : 4 * sigma * (1 - sigma) * tau + eta < delta) :
    0 <
      delta - (4 * sigma * (1 - sigma) * tau + eta) :=
  sub_pos.mpr hgate

/-- Exact feasibility criterion for a single exponential truncation scale.
The lower inequality `1 - beta < tau` is the rate required to suppress a
classical `x / T` contour error after normalization by `x^beta`; the upper
inequality is the Carlson residual-decay gate. -/
theorem exists_exponentialTruncationScale_iff
    {beta sigma eta delta : ℝ}
    (hq : 0 < 4 * sigma * (1 - sigma)) :
    (∃ tau : ℝ,
      1 - beta < tau ∧
        4 * sigma * (1 - sigma) * tau + eta < delta) ↔
      4 * sigma * (1 - sigma) * (1 - beta) + eta < delta := by
  let q : ℝ := 4 * sigma * (1 - sigma)
  constructor
  · rintro ⟨tau, hcontour, hresidual⟩
    have hmul : q * (1 - beta) < q * tau :=
      mul_lt_mul_of_pos_left hcontour (by simpa [q] using hq)
    dsimp only [q] at hmul ⊢
    linarith
  · intro hgate
    have hq' : 0 < q := by simpa [q] using hq
    have hlowerUpper :
        1 - beta < (delta - eta) / q := by
      apply (lt_div_iff₀ hq').2
      dsimp only [q]
      linarith [hgate]
    rcases exists_between hlowerUpper with
      ⟨tau, htauLower, htauUpper⟩
    refine ⟨tau, htauLower, ?_⟩
    have hmul : tau * q < delta - eta :=
      (lt_div_iff₀ hq').1 htauUpper
    dsimp only [q] at hmul
    nlinarith

/-- When the real-part gap is no larger than the combined contour and
Carlson cost, no exponential height scale can make both estimates decay. -/
theorem no_exponentialTruncationScale_of_gap_le
    {beta sigma eta delta : ℝ}
    (hq : 0 < 4 * sigma * (1 - sigma))
    (hgap :
      delta ≤ 4 * sigma * (1 - sigma) * (1 - beta) + eta) :
    ¬ ∃ tau : ℝ,
      1 - beta < tau ∧
        4 * sigma * (1 - sigma) * tau + eta < delta := by
  rw [exists_exponentialTruncationScale_iff hq]
  exact not_lt_of_ge hgap

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
