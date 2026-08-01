import PrimeNumberTheorem.ZeroDensityLayerBudgetActualFullTailExcludingClusterConjugation
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTRealOrdinateDecay

/-!
# Target-normalized real-ordinate residual outside a main cluster

Ordinary convergence of the real-ordinate residual is not enough for an
oscillation theorem because the target amplitude also tends to zero.  The
real-ordinate zero set is fixed once the dynamic height is nonnegative, so a
strict real-part gap below the target `beta` gives the required normalized
decay by finite summation.
-/

open scoped BigOperators

namespace PrimeNumberTheorem

open Filter

/-- One actual multiplicity-weighted zero contribution is negligible relative
to the target power whenever its real part is strictly below the target real
part. -/
theorem
    tendsto_norm_pntRelativeZeroContribution_div_targetZeroPowerAmplitude
    {rho : ℂ} {beta : ℝ} (hre : rho.re < beta) :
    Tendsto
      (fun x : ℝ =>
        ‖pntRelativeZeroContribution x rho‖ /
          targetZeroPowerAmplitude beta x)
      atTop (nhds 0) := by
  have hgap : 0 < beta - rho.re := sub_pos.mpr hre
  have hpower :
      Tendsto (fun x : ℝ => x ^ (rho.re - beta))
        atTop (nhds 0) := by
    convert tendsto_rpow_neg_atTop hgap using 1
    funext x
    congr 1
    ring
  have hscaled :
      Tendsto
        (fun x : ℝ =>
          ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) *
            x ^ (rho.re - beta))
        atTop (nhds 0) :=
    by
      have hconst :
          Tendsto
            (fun _ : ℝ =>
              (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖)
            atTop
            (nhds
              ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖)) :=
        tendsto_const_nhds
      simpa using hconst.mul hpower
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  symm
  have hpow :
      x ^ (rho.re - 1) / x ^ (beta - 1) =
        x ^ (rho.re - beta) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hx.le,
      ← Real.rpow_add hx]
    congr 1
    ring
  rw [norm_pntRelativeZeroContribution_eq_multiplicity_mul_norm,
    norm_pntRelativeSimpleZeroKernel_eq hx]
  simp only [targetZeroPowerAmplitude]
  calc
    (analyticOrderNatAt riemannZeta rho : ℝ) *
          (x ^ (rho.re - 1) / ‖rho‖) /
        x ^ (beta - 1) =
        ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) *
          (x ^ (rho.re - 1) / x ^ (beta - 1)) := by
      ring
    _ = ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) *
          x ^ (rho.re - beta) := by rw [hpow]

/-- A nonnegative dynamic height has the same outside-cluster real-ordinate
set as height zero. -/
theorem realOrdinateNontrivialZerosOutsideClusterFinset_eq_zeroHeight
    {T : ℝ} {S : Finset ℂ} (hT : 0 ≤ T) :
    realOrdinateNontrivialZerosOutsideClusterFinset T S =
      realOrdinateNontrivialZerosOutsideClusterFinset 0 S := by
  unfold realOrdinateNontrivialZerosOutsideClusterFinset
  rw [realOrdinateNontrivialZerosFinset_eq_zeroHeight hT]

/-- A strict real-part gap for the fixed real-ordinate zeros outside `S`
implies target-amplitude negligibility for every eventually nonnegative
dynamic height. -/
theorem
    dynamicRealOrdinateOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
    (height : ℝ → ℝ) (S : Finset ℂ) (beta : ℝ)
    (hheight : ∀ᶠ x in atTop, 0 ≤ height x)
    (hre :
      ∀ rho ∈
        realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicRealOrdinateOutsideClusterPNTZeroTailNorm height S) := by
  let realZeros :=
    realOrdinateNontrivialZerosOutsideClusterFinset 0 S
  have hsum :
      Tendsto
        (fun x : ℝ =>
          ∑ rho ∈ realZeros,
            ‖pntRelativeZeroContribution x rho‖ /
              targetZeroPowerAmplitude beta x)
        atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finset_sum realZeros fun rho hrho =>
        tendsto_norm_pntRelativeZeroContribution_div_targetZeroPowerAmplitude
          (hre rho hrho))
  unfold TargetAmplitudeNegligible
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards
      [targetZeroPowerAmplitude_eventually_pos beta] with x hx
    exact div_nonneg (abs_nonneg _) hx.le
  · filter_upwards
      [targetZeroPowerAmplitude_eventually_pos beta, hheight] with
      x hxAmplitude hxHeight
    have hset :
        realOrdinateNontrivialZerosOutsideClusterFinset (height x) S =
          realZeros := by
      exact
        realOrdinateNontrivialZerosOutsideClusterFinset_eq_zeroHeight
          hxHeight
    have hnorm :
        ‖∑ rho ∈ realZeros, pntRelativeZeroContribution x rho‖ ≤
          ∑ rho ∈ realZeros,
            ‖pntRelativeZeroContribution x rho‖ :=
      norm_sum_le _ _
    rw [dynamicRealOrdinateOutsideClusterPNTZeroTailNorm, hset,
      abs_of_nonneg (norm_nonneg _)]
    calc
      ‖∑ rho ∈ realZeros, pntRelativeZeroContribution x rho‖ /
            targetZeroPowerAmplitude beta x ≤
          (∑ rho ∈ realZeros,
            ‖pntRelativeZeroContribution x rho‖) /
              targetZeroPowerAmplitude beta x :=
        div_le_div_of_nonneg_right hnorm hxAmplitude.le
      _ = ∑ rho ∈ realZeros,
          ‖pntRelativeZeroContribution x rho‖ /
            targetZeroPowerAmplitude beta x := by
        rw [Finset.sum_div]

/-- Polynomial Carlson height is eventually nonnegative, so the finite
real-part separation condition automatically supplies the residual field used
by the outside-cluster Carlson certificate. -/
theorem
    dynamicRealOrdinateOutsideClusterPNTZeroTailNorm_carlsonPolynomial_negligible
    {alpha beta : ℝ} {S : Finset ℂ}
    (hre :
      ∀ rho ∈
        realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicRealOrdinateOutsideClusterPNTZeroTailNorm
        (carlsonPolynomialHeight alpha) S) := by
  apply
    dynamicRealOrdinateOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
      (carlsonPolynomialHeight alpha) S beta
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact Real.rpow_nonneg hx alpha
  · exact hre

end PrimeNumberTheorem
