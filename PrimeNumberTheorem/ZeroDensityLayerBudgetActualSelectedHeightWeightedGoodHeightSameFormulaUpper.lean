import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedGoodHeightNaturalTransfer

/-!
# Same-formula upper and lower transfer at the weighted good height

The earlier unified theorem pairs a pre-existing PNT upper theorem with the
actual weighted selected-height lower transfer.  This module reconstructs the
upper bound from the very same finite-height explicit-formula decomposition:

* the visible finite cluster is bounded explicitly by
  `sum_{rho in S} multiplicity(rho) / ‖rho‖`;
* the closed real-axis term, selected contour remainder, and actual signed
  outside-cluster complement are together smaller than half the target
  amplitude;
* the exact decomposition therefore gives an eventual
  `O(x ^ (beta - 1))` bound for the actual relative PNT error.

Thus the upper and lower conclusions now use the same zero cluster, the same
selected good height, and the same explicit formula.
-/

namespace PrimeNumberTheorem

open Complex Filter Topology
open scoped BigOperators

/-- Explicit coefficient of a finite visible zero cluster. -/
noncomputable def finiteVisibleClusterPNTAmplitudeCoefficient
    (S : Finset ℂ) : ℝ :=
  ∑ rho ∈ S,
    (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖

theorem finiteVisibleClusterPNTAmplitudeCoefficient_nonneg
    (S : Finset ℂ) :
    0 ≤ finiteVisibleClusterPNTAmplitudeCoefficient S := by
  unfold finiteVisibleClusterPNTAmplitudeCoefficient
  positivity

/-- One multiplicity-weighted zero contribution is bounded by the target
power when its real part is at most `beta`. -/
theorem norm_pntRelativeZeroContribution_le_coefficient_mul_target
    {rho : ℂ} {beta x : ℝ} (hx : 1 ≤ x) (hre : rho.re ≤ beta) :
    ‖pntRelativeZeroContribution x rho‖ ≤
      ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) *
        targetZeroPowerAmplitude beta x := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hpower :
      x ^ (rho.re - 1) ≤ x ^ (beta - 1) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  rw [norm_pntRelativeZeroContribution_eq_multiplicity_mul_norm,
    norm_pntRelativeSimpleZeroKernel_eq hxpos]
  unfold targetZeroPowerAmplitude
  calc
    (analyticOrderNatAt riemannZeta rho : ℝ) *
          (x ^ (rho.re - 1) / ‖rho‖) =
        ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) *
          x ^ (rho.re - 1) := by ring
    _ ≤ ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) *
          x ^ (beta - 1) := by
      exact mul_le_mul_of_nonneg_left hpower
        (div_nonneg (Nat.cast_nonneg _) (norm_nonneg _))

/-- The currently visible part of a fixed finite cluster is bounded uniformly
by the full finite-cluster coefficient. -/
theorem abs_dynamicVisibleClusterPNTMain_le_coefficient_mul_target
    (T : ℝ → ℝ) (S : Finset ℂ)
    {beta x : ℝ} (hx : 1 ≤ x)
    (hre : ∀ rho ∈ S, rho.re ≤ beta) :
    |dynamicVisibleClusterPNTMain T S x| ≤
      finiteVisibleClusterPNTAmplitudeCoefficient S *
        targetZeroPowerAmplitude beta x := by
  classical
  have hsum :
      ‖dynamicVisibleClusterPNTZeroSum T S x‖ ≤
        ∑ rho ∈ S, ‖pntRelativeZeroContribution x rho‖ := by
    unfold dynamicVisibleClusterPNTZeroSum
    calc
      ‖∑ rho ∈ nontrivialZerosFinset (T x),
          if rho ∈ S then pntRelativeZeroContribution x rho else 0‖ ≤
          ∑ rho ∈ nontrivialZerosFinset (T x),
            ‖if rho ∈ S then pntRelativeZeroContribution x rho else 0‖ :=
        norm_sum_le _ _
      _ =
          ∑ rho ∈ nontrivialZerosFinset (T x),
            if rho ∈ S then ‖pntRelativeZeroContribution x rho‖ else 0 := by
        apply Finset.sum_congr rfl
        intro rho _
        by_cases hrho : rho ∈ S <;> simp [hrho]
      _ =
          ∑ rho ∈
              (nontrivialZerosFinset (T x)).filter (fun rho => rho ∈ S),
            ‖pntRelativeZeroContribution x rho‖ := by
        rw [Finset.sum_filter]
      _ ≤ ∑ rho ∈ S, ‖pntRelativeZeroContribution x rho‖ := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun rho hrho => (Finset.mem_filter.mp hrho).2)
          (fun rho _ _ => norm_nonneg _)
  calc
    |dynamicVisibleClusterPNTMain T S x| ≤
        ‖dynamicVisibleClusterPNTZeroSum T S x‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑ rho ∈ S, ‖pntRelativeZeroContribution x rho‖ := hsum
    _ ≤
        ∑ rho ∈ S,
          ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) *
            targetZeroPowerAmplitude beta x := by
      exact Finset.sum_le_sum fun rho hrho =>
        norm_pntRelativeZeroContribution_le_coefficient_mul_target
          hx (hre rho hrho)
    _ =
        finiteVisibleClusterPNTAmplitudeCoefficient S *
          targetZeroPowerAmplitude beta x := by
      simp [finiteVisibleClusterPNTAmplitudeCoefficient, Finset.sum_mul]

/-- At the weighted selected good height, the exact relative PNT error is
eventually bounded by the visible-cluster coefficient plus half the target
amplitude. -/
theorem
    eventually_abs_relativeChebyshevPsi0Error_le_weightedBalancedGoodHeightClusterScale
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (hclusterRe : ∀ rho ∈ S, rho.re ≤ beta)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          S (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        (finiteVisibleClusterPNTAmplitudeCoefficient S + 1 / 2) *
          targetZeroPowerAmplitude beta (m : ℝ) := by
  let alpha :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau
  let H :=
    actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
      beta sigma tau selection
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  have halpha : 0 < alpha := hspec.2.1
  have halphaOne : alpha ≤ 1 := hspec.2.2.1.le
  have hmargin : 1 - beta < alpha := hspec.2.2.2.1
  let carlsonCertificate :=
    actualCarlsonOutsideClusterWeightedBalancedGoodHeightFiniteStripCertificate
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
      input kappa hS hfixedSigma hkappa hnorm hre hreal
  have remainderCertificate :
      ActualSelectedHeightNaturalPointRemainderCertificate beta H := by
    change
      ActualSelectedHeightNaturalPointRemainderCertificate beta
        (selectedUniformGoodHeight alpha selection)
    exact selectedUniformGoodHeight_actualNaturalRemainderCertificate
      hbeta halpha halphaOne hmargin selection
  have hresidual :
      ∀ᶠ m : ℕ in atTop,
        |actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
            actualPNTExplicitFormulaRelativeRemainder H (m : ℝ) +
            dynamicOutsideClusterPNTComplement H S (m : ℝ)| <
          targetZeroPowerAmplitude beta (m : ℝ) / 2 :=
    eventually_abs_naturalPoint_three_remainders_lt_half
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible
        hbeta).naturalPoint
      remainderCertificate.negligible
      (carlsonCertificate.actualSignedComplementCertificate
        |>.complement_negligible
        |>.naturalPoint)
  filter_upwards [hresidual, eventually_ge_atTop (1 : ℕ)] with m hsmall hm
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
    H S (m : ℝ)]
  calc
    |dynamicVisibleClusterPNTMain H S (m : ℝ) +
        (actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ) +
          dynamicOutsideClusterPNTComplement H S (m : ℝ))| ≤
        |dynamicVisibleClusterPNTMain H S (m : ℝ)| +
          |actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
            actualPNTExplicitFormulaRelativeRemainder H (m : ℝ) +
            dynamicOutsideClusterPNTComplement H S (m : ℝ)| :=
      abs_add_le _ _
    _ ≤
        finiteVisibleClusterPNTAmplitudeCoefficient S *
            targetZeroPowerAmplitude beta (m : ℝ) +
          targetZeroPowerAmplitude beta (m : ℝ) / 2 := by
      exact add_le_add
        (abs_dynamicVisibleClusterPNTMain_le_coefficient_mul_target
          H S hmReal hclusterRe)
        hsmall.le
    _ =
        (finiteVisibleClusterPNTAmplitudeCoefficient S + 1 / 2) *
          targetZeroPowerAmplitude beta (m : ℝ) := by ring

/-- The same-formula quantitative bound implies ordinary PNT decay because
`beta < 1`. -/
theorem
    tendsto_relativeChebyshevPsi0Error_natural_weightedBalancedGoodHeight
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (hclusterRe : ∀ rho ∈ S, rho.re ≤ beta)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          S (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    Tendsto
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop (nhds 0) := by
  have hbound :=
    eventually_abs_relativeChebyshevPsi0Error_le_weightedBalancedGoodHeightClusterScale
      hbeta hbetaOne sigma tau hsigma hsigmaOne htau hthreshold selection
      hclusterRe input kappa hS hfixedSigma hkappa hnorm hre hreal
  have htargetReal :
      Tendsto (targetZeroPowerAmplitude beta) atTop (nhds 0) := by
    unfold targetZeroPowerAmplitude
    convert tendsto_rpow_neg_atTop (sub_pos.mpr hbetaOne) using 1
    funext x
    congr 1
    ring
  have htarget :
      Tendsto
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        atTop (nhds 0) :=
    htargetReal.comp tendsto_natCast_atTop_atTop
  have hmajorant :
      Tendsto
        (fun m : ℕ =>
          (finiteVisibleClusterPNTAmplitudeCoefficient S + 1 / 2) *
            targetZeroPowerAmplitude beta (m : ℝ))
        atTop (nhds 0) := by
    simpa using htarget.const_mul
      (finiteVisibleClusterPNTAmplitudeCoefficient S + 1 / 2)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa [Real.norm_eq_abs] using
    (squeeze_zero'
      (Filter.Eventually.of_forall fun m : ℕ => abs_nonneg
        (relativeChebyshevPsi0Error (m : ℝ)))
      hbound hmajorant)

/-- Same-height, same-decomposition upper/lower transfer. -/
theorem
    unified_actualWeightedBalancedGoodHeightSameFormulaUpperLower
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (hclusterRe : ∀ rho ∈ S, rho.re ≤ beta)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          S (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S (m : ℝ))
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        (finiteVisibleClusterPNTAmplitudeCoefficient S + 1 / 2) *
          targetZeroPowerAmplitude beta (m : ℝ)) ∧
    Tendsto
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop (nhds 0) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      eventually_abs_relativeChebyshevPsi0Error_le_weightedBalancedGoodHeightClusterScale
        hbeta hbetaOne sigma tau hsigma hsigmaOne htau hthreshold selection
        hclusterRe input kappa hS hfixedSigma hkappa hnorm hre hreal
  · exact
      tendsto_relativeChebyshevPsi0Error_natural_weightedBalancedGoodHeight
        hbeta hbetaOne sigma tau hsigma hsigmaOne htau hthreshold selection
        hclusterRe input kappa hS hfixedSigma hkappa hnorm hre hreal
  · exact
      (unified_parametricPNTUpper_actualWeightedBalancedGoodHeightNaturalLower
        (1 / 2 + 1 / 4) (by norm_num) (by norm_num)
        hbeta hbetaOne sigma tau hsigma hsigmaOne htau hthreshold selection
        input kappa hS hfixedSigma hkappa hnorm hre hreal hmain).2

end PrimeNumberTheorem
