import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicCarlsonWeightedGoodHeightPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightFiniteStripBottleneck

/-!
# Automatic target exponent for the dynamic Carlson PNT transfer

The fixed-target transfer requires every strip endpoint threshold and every
real-ordinate nontrivial zero to lie strictly below `beta`.  Both families are
finite.  This module takes their joint maximum and chooses the explicit
midpoint between that bottleneck and `1`.

Consequently the actual PNT upper transfer no longer needs a separately
supplied real-ordinate separation hypothesis or a manually chosen target
exponent.
-/

noncomputable section

namespace PrimeNumberTheorem

open Complex Filter Topology

/-- The largest real part among the fixed height-zero real-ordinate
nontrivial zeros, with `0` inserted to handle the empty-zero-set case. -/
noncomputable def realOrdinatePNTZeroBottleneck : ℝ :=
  let values :=
    insert 0
      ((realOrdinateNontrivialZerosFinset 0).image fun rho => rho.re)
  values.max' (Finset.insert_nonempty 0 _)

/-- The inserted zero makes the real-ordinate bottleneck nonnegative. -/
theorem realOrdinatePNTZeroBottleneck_nonneg :
    0 ≤ realOrdinatePNTZeroBottleneck := by
  let values :=
    insert 0
      ((realOrdinateNontrivialZerosFinset 0).image fun rho => rho.re)
  apply values.le_max'
  exact Finset.mem_insert_self 0 _

/-- Every fixed real-ordinate nontrivial zero lies below the finite
real-ordinate bottleneck. -/
theorem realOrdinateNontrivialZero_re_le_bottleneck
    {rho : ℂ} (hrho : rho ∈ realOrdinateNontrivialZerosFinset 0) :
    rho.re ≤ realOrdinatePNTZeroBottleneck := by
  let values :=
    insert 0
      ((realOrdinateNontrivialZerosFinset 0).image fun z => z.re)
  apply values.le_max'
  exact Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨rho, hrho, rfl⟩)

/-- The finite real-ordinate bottleneck is strictly below one because every
member is either the inserted zero or a nontrivial zeta zero. -/
theorem realOrdinatePNTZeroBottleneck_lt_one :
    realOrdinatePNTZeroBottleneck < 1 := by
  let values :=
    insert 0
      ((realOrdinateNontrivialZerosFinset 0).image fun rho => rho.re)
  change values.max' (Finset.insert_nonempty 0 _) < 1
  rw [Finset.max'_lt_iff]
  intro value hvalue
  rcases Finset.mem_insert.mp hvalue with hzero | hzero
  · rw [hzero]
    norm_num
  · obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp hzero
    exact
      (mem_nontrivialZerosFinset.mp
        (mem_realOrdinateNontrivialZerosFinset.mp hrho).1).1.2.2

/-- Joint obstruction coming from the worst Carlson strip and the fixed
real-ordinate zero residual. -/
noncomputable def dynamicCarlsonActualPNTBottleneck
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) : ℝ :=
  max
    (actualSelectedHeightFiniteStripBottleneck sigma tau)
    realOrdinatePNTZeroBottleneck

/-- Explicit automatic target exponent halfway between the joint bottleneck
and one. -/
noncomputable def dynamicCarlsonAutomaticTargetBeta
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) : ℝ :=
  (dynamicCarlsonActualPNTBottleneck sigma tau + 1) / 2

/-- If every strip threshold is below one, so is the joint bottleneck. -/
theorem dynamicCarlsonActualPNTBottleneck_lt_one
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hthresholdOne :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < 1) :
    dynamicCarlsonActualPNTBottleneck sigma tau < 1 := by
  apply max_lt
  · exact
      (actualSelectedHeightFiniteStripBottleneck_lt_iff
        sigma tau 1).2 hthresholdOne
  · exact realOrdinatePNTZeroBottleneck_lt_one

/-- The joint bottleneck is nonnegative. -/
theorem dynamicCarlsonActualPNTBottleneck_nonneg
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) :
    0 ≤ dynamicCarlsonActualPNTBottleneck sigma tau :=
  realOrdinatePNTZeroBottleneck_nonneg.trans
    (le_max_right _ _)

/-- The automatic target lies strictly above the joint bottleneck. -/
theorem dynamicCarlsonActualPNTBottleneck_lt_automaticTargetBeta
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hthresholdOne :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < 1) :
    dynamicCarlsonActualPNTBottleneck sigma tau <
      dynamicCarlsonAutomaticTargetBeta sigma tau := by
  have hbottleneck :=
    dynamicCarlsonActualPNTBottleneck_lt_one
      sigma tau hthresholdOne
  unfold dynamicCarlsonAutomaticTargetBeta
  linarith

/-- The automatic target remains strictly below one. -/
theorem dynamicCarlsonAutomaticTargetBeta_lt_one
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hthresholdOne :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < 1) :
    dynamicCarlsonAutomaticTargetBeta sigma tau < 1 := by
  have hbottleneck :=
    dynamicCarlsonActualPNTBottleneck_lt_one
      sigma tau hthresholdOne
  unfold dynamicCarlsonAutomaticTargetBeta
  linarith

/-- The automatic target is positive. -/
theorem dynamicCarlsonAutomaticTargetBeta_pos
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) :
    0 < dynamicCarlsonAutomaticTargetBeta sigma tau := by
  have hbottleneck :=
    dynamicCarlsonActualPNTBottleneck_nonneg sigma tau
  unfold dynamicCarlsonAutomaticTargetBeta
  linarith

/-- Every Carlson strip threshold lies strictly below the automatic target. -/
theorem carlsonStripEndpointTargetThreshold_lt_automaticTargetBeta
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hthresholdOne :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < 1)
    (i : Fin (n + 1)) :
    carlsonStripEndpointTargetThreshold (sigma i) (tau i) <
      dynamicCarlsonAutomaticTargetBeta sigma tau := by
  exact lt_of_le_of_lt
    (carlsonStripEndpointTargetThreshold_le_bottleneck sigma tau i)
    ((le_max_left _ _).trans_lt
      (dynamicCarlsonActualPNTBottleneck_lt_automaticTargetBeta
        sigma tau hthresholdOne))

/-- Every fixed real-ordinate nontrivial zero lies strictly below the
automatic target. -/
theorem realOrdinateNontrivialZero_re_lt_automaticTargetBeta
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hthresholdOne :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < 1)
    {rho : ℂ} (hrho : rho ∈ realOrdinateNontrivialZerosFinset 0) :
    rho.re < dynamicCarlsonAutomaticTargetBeta sigma tau := by
  exact lt_of_le_of_lt
    (realOrdinateNontrivialZero_re_le_bottleneck hrho)
    ((le_max_right _ _).trans_lt
      (dynamicCarlsonActualPNTBottleneck_lt_automaticTargetBeta
        sigma tau hthresholdOne))

/-- Fully automatic target-scale actual PNT upper transfer.  The target
exponent and the real-ordinate separation are both discharged by finite
bottleneck selection. -/
theorem
    relativeChebyshevPsi0Error_natural_dynamicCarlsonAutomaticBeta_negligible
    {n : ℕ} (sigma tau kappa : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthresholdOne :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < 1)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            (dynamicCarlsonAutomaticTargetBeta sigma tau)
            sigma tau selection x)
          (n + 1))
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ =>
        targetZeroPowerAmplitude
          (dynamicCarlsonAutomaticTargetBeta sigma tau) (m : ℝ))
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ)) := by
  exact
    relativeChebyshevPsi0Error_natural_weightedBalancedGoodHeight_dynamicCarlson_negligible
      (dynamicCarlsonAutomaticTargetBeta_pos sigma tau)
      sigma tau kappa
      (dynamicCarlsonAutomaticTargetBeta_lt_one
        sigma tau hthresholdOne)
      hsigma hsigmaOne htau
      (carlsonStripEndpointTargetThreshold_lt_automaticTargetBeta
        sigma tau hthresholdOne)
      selection input hfixedSigma hkappa hnorm hre
      (fun rho hrho =>
        realOrdinateNontrivialZero_re_lt_automaticTargetBeta
          sigma tau hthresholdOne hrho)

/-- The automatic target-scale estimate yields ordinary natural-point PNT
decay without a manually chosen `beta` or a real-ordinate residual input. -/
theorem
    tendsto_relativeChebyshevPsi0Error_natural_dynamicCarlsonAutomaticBeta
    {n : ℕ} (sigma tau kappa : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthresholdOne :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < 1)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            (dynamicCarlsonAutomaticTargetBeta sigma tau)
            sigma tau selection x)
          (n + 1))
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    Tendsto
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop (nhds 0) := by
  exact
    tendsto_relativeChebyshevPsi0Error_natural_dynamicCarlsonWeightedGoodHeight
      (dynamicCarlsonAutomaticTargetBeta_pos sigma tau)
      sigma tau kappa
      (dynamicCarlsonAutomaticTargetBeta_lt_one
        sigma tau hthresholdOne)
      hsigma hsigmaOne htau
      (carlsonStripEndpointTargetThreshold_lt_automaticTargetBeta
        sigma tau hthresholdOne)
      selection input hfixedSigma hkappa hnorm hre
      (fun rho hrho =>
        realOrdinateNontrivialZero_re_lt_automaticTargetBeta
          sigma tau hthresholdOne hrho)

end PrimeNumberTheorem
