import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonDynamicTruncatedDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonOutsideClusterConjugation
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualRealOrdinateExcludingCluster

/-!
# Dynamic Carlson decay for the complete zero sum outside a cluster

This module combines three already concrete ingredients:

* dynamic Carlson decay for positive-ordinate zeta zeros;
* conjugation symmetry for the negative-ordinate contribution;
* target-amplitude decay for the real-ordinate contribution.

The real-ordinate term is not discarded.  Its existing decay theorem is
restricted from real scales to natural scales and included explicitly in the
majorant.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- The real-ordinate part of the dynamic zero sum, normalized by the target
zero amplitude. -/
noncomputable def actualCarlsonDynamicRealOrdinateNormalizedSum
    (alpha beta : ℝ) (S : Finset ℂ) (m : ℕ) : ℝ :=
  ‖∑ rho ∈
      realOrdinateNontrivialZerosOutsideClusterFinset
        (carlsonPolynomialHeight alpha (m : ℝ)) S,
      pntRelativeZeroContribution (m : ℝ) rho‖ /
    targetZeroPowerAmplitude beta (m : ℝ)

/-- The complete dynamic nontrivial-zero sum outside a finite cluster,
normalized by the target zero amplitude. -/
noncomputable def actualCarlsonDynamicTruncatedFullZeroNormalizedSum
    (alpha beta : ℝ) (S : Finset ℂ) (m : ℕ) : ℝ :=
  ‖∑ rho ∈
      nontrivialZerosOutsideClusterFinset
        (carlsonPolynomialHeight alpha (m : ℝ)) S,
      pntRelativeZeroContribution (m : ℝ) rho‖ /
    targetZeroPowerAmplitude beta (m : ℝ)

/-- Existing real-scale decay of the real-ordinate contribution remains valid
along natural scales. -/
theorem actualCarlsonDynamicRealOrdinateNormalizedSum_tendsto_zero
    {alpha beta : ℝ} {S : Finset ℂ}
    (hre :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    Tendsto
      (actualCarlsonDynamicRealOrdinateNormalizedSum alpha beta S)
      atTop (𝓝 0) := by
  have hreal :
      Tendsto
        (fun x : ℝ =>
          dynamicRealOrdinateOutsideClusterPNTZeroTailNorm
              (carlsonPolynomialHeight alpha) S x /
            targetZeroPowerAmplitude beta x)
        atTop (𝓝 0) := by
    simpa [TargetAmplitudeNegligible,
      dynamicRealOrdinateOutsideClusterPNTZeroTailNorm, abs_of_nonneg] using
      (dynamicRealOrdinateOutsideClusterPNTZeroTailNorm_carlsonPolynomial_negligible
        (alpha := alpha) (beta := beta) (S := S) hre)
  simpa [actualCarlsonDynamicRealOrdinateNormalizedSum,
    dynamicRealOrdinateOutsideClusterPNTZeroTailNorm, Function.comp_def] using
    hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The complete actual zeta-zero residual outside a conjugation-invariant
finite cluster is negligible at the target amplitude.

The low strip is controlled by its fixed real-part gap, the high strip by the
actual Carlson shell budget and pointwise gap, negative ordinates by
conjugation, and real ordinates by their separate concrete decay theorem. -/
theorem actualCarlsonDynamicTruncatedFullZeroNormalizedSum_tendsto_zero
    {n : ℕ} {sigma beta alpha kappa epsilon : ℝ}
    (S : Finset ℂ)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n)
    (i : Fin n)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hkappa : 0 < kappa)
    (hnorm :
      ∀ (x : ℝ), ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hreLow :
      ∀ (x : ℝ), ∀ rho ∈ (input x).layer i, rho.re ≤ sigma)
    (hlowCover :
      ∀ (x : ℝ),
        ∀ rho ∈
            positiveNontrivialZerosOutsideClusterFinset
              (carlsonPolynomialHeight alpha x) S,
          rho.re ≤ sigma → (input x).bucket rho = i)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + alpha + epsilon < 0)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          (actualCarlsonPositiveZero index).re < beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    Tendsto
      (actualCarlsonDynamicTruncatedFullZeroNormalizedSum alpha beta S)
      atTop (𝓝 0) := by
  have hpositive :
      Tendsto
        (actualCarlsonDynamicTruncatedPositiveZeroNormalizedSum alpha beta S)
        atTop (𝓝 0) :=
    actualCarlsonDynamicTruncatedPositiveZeroNormalizedSum_tendsto_zero
      S input i hhalf hone hkappa hnorm hreLow hlowCover halpha hepsilon
      hmargin hreHigh
  have hreal :
      Tendsto
        (actualCarlsonDynamicRealOrdinateNormalizedSum alpha beta S)
        atTop (𝓝 0) :=
    actualCarlsonDynamicRealOrdinateNormalizedSum_tendsto_zero hreReal
  have hmajor :
      Tendsto
        (fun m : ℕ =>
          2 *
              actualCarlsonDynamicTruncatedPositiveZeroNormalizedSum
                alpha beta S m +
            actualCarlsonDynamicRealOrdinateNormalizedSum alpha beta S m)
        atTop (𝓝 0) := by
    convert (hpositive.const_mul 2).add hreal using 1 <;> norm_num
  apply squeeze_zero'
  · have hampReal := targetZeroPowerAmplitude_eventually_pos beta
    have hampNat :
        ∀ᶠ m : ℕ in atTop,
          0 < targetZeroPowerAmplitude beta (m : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hampReal
    filter_upwards [hampNat] with m hm
    exact div_nonneg (norm_nonneg _) hm.le
  · have hampReal := targetZeroPowerAmplitude_eventually_pos beta
    have hampNat :
        ∀ᶠ m : ℕ in atTop,
          0 < targetZeroPowerAmplitude beta (m : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hampReal
    filter_upwards [eventually_gt_atTop (0 : ℕ), hampNat] with m hm hAmplitude
    have hmx : 0 < (m : ℝ) := by exact_mod_cast hm
    have hzero :=
      norm_fullOutsideClusterZeroSum_le_two_mul_positive_add_real
        (T := carlsonPolynomialHeight alpha (m : ℝ))
        (x := (m : ℝ)) hmx S hS
    calc
      actualCarlsonDynamicTruncatedFullZeroNormalizedSum alpha beta S m
          ≤
            (2 *
                  ‖∑ rho ∈
                      positiveNontrivialZerosOutsideClusterFinset
                        (carlsonPolynomialHeight alpha (m : ℝ)) S,
                      pntRelativeZeroContribution (m : ℝ) rho‖ +
                ‖∑ rho ∈
                    realOrdinateNontrivialZerosOutsideClusterFinset
                      (carlsonPolynomialHeight alpha (m : ℝ)) S,
                    pntRelativeZeroContribution (m : ℝ) rho‖) /
              targetZeroPowerAmplitude beta (m : ℝ) := by
                exact (div_le_div_iff_of_pos_right hAmplitude).2 hzero
      _ =
          2 *
              actualCarlsonDynamicTruncatedPositiveZeroNormalizedSum
                alpha beta S m +
            actualCarlsonDynamicRealOrdinateNormalizedSum alpha beta S m := by
              simp only [
                actualCarlsonDynamicTruncatedPositiveZeroNormalizedSum,
                actualCarlsonDynamicRealOrdinateNormalizedSum]
              ring
  · exact hmajor

end PrimeNumberTheorem
