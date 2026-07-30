import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageNaturalThresholdTransfer

/-!
# Same-real-part barrier for finite-strip Carlson transfer

Strict Carlson endpoint thresholds force every covered strip endpoint below
the target real part. Consequently a cofinal fixed finite cluster must contain
every positive-ordinate zero on the target real-part line.

For a height-truncated equal-real-part package this means that no zero on that
line may occur above the package height. This is the precise obstruction to
turning the fixed-package transfer into an unconditional Omega theorem.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

theorem not_carlsonStripEndpointTargetThreshold_lt_of_beta_le_tau
    {sigma tau beta : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hbetaOne : beta < 1) (hbetaTau : beta ≤ tau) :
    ¬ carlsonStripEndpointTargetThreshold sigma tau < beta := by
  intro hthreshold
  let q := 4 * sigma * (1 - sigma)
  have hq : 0 < q := by
    dsimp [q]
    exact mul_pos
      (mul_pos (by norm_num) (lt_trans (by norm_num) hsigma))
      (sub_pos.mpr hsigmaOne)
  have hden : 0 < 1 + q := by positivity
  rw [carlsonStripEndpointTargetThreshold] at hthreshold
  have hmul := (div_lt_iff₀ hden).mp hthreshold
  dsimp [q] at hmul hq
  nlinarith

theorem sameRealPart_not_mem_positiveOutsideCluster_of_thresholds
    {beta : ℝ} (hbetaOne : beta < 1)
    {S : Finset ℂ} {n : ℕ}
    {H : ℝ → ℝ}
    (sigma tau : Fin n → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (input :
      (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S n)
    (hre :
      ∀ i x, ∀ z ∈ (input x).layer i, z.re ≤ tau i)
    (x : ℝ) {z : ℂ} (hzre : z.re = beta) :
    z ∉ positiveNontrivialZerosOutsideClusterFinset (H x) S := by
  intro hz
  let i := (input x).bucket z
  have hzlayer : z ∈ (input x).layer i := by
    simp [PositiveZeroOutsideClusterBucketInput.layer, i, hz]
  have hbetaTau : beta ≤ tau i := by
    rw [← hzre]
    exact hre i x z hzlayer
  exact
    (not_carlsonStripEndpointTargetThreshold_lt_of_beta_le_tau
      (hsigma i) (hsigmaOne i) hbetaOne hbetaTau)
      (hthreshold i)

theorem fixedCluster_contains_positiveSameRealPartZeros_of_thresholds
    {beta : ℝ} (hbetaOne : beta < 1)
    {S : Finset ℂ} {n : ℕ}
    {H : ℝ → ℝ} (hH : Tendsto H atTop atTop)
    (sigma tau : Fin n → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (input :
      (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S n)
    (hre :
      ∀ i x, ∀ z ∈ (input x).layer i, z.re ≤ tau i)
    {z : ℂ} (hzero : RiemannHypothesis.IsNontrivialZero z)
    (hzim : 0 < z.im) (hzre : z.re = beta) :
    z ∈ S := by
  have hheight : ∀ᶠ x : ℝ in atTop, z.im ≤ H x :=
    hH.eventually_ge_atTop z.im
  rcases hheight.exists with ⟨x, hx⟩
  by_contra hzS
  have hzoutside :
      z ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S := by
    exact mem_positiveNontrivialZerosOutsideClusterFinset.mpr
      ⟨hzero, hzim, hx, hzS⟩
  exact
    (sameRealPart_not_mem_positiveOutsideCluster_of_thresholds
      hbetaOne sigma tau hsigma hsigmaOne hthreshold input hre x hzre)
      hzoutside

theorem equalRealPartZeroPackage_bounds_all_positiveSameRealPartZeros_of_thresholds
    {beta T : ℝ} (hbetaOne : beta < 1)
    {n : ℕ} {H : ℝ → ℝ} (hH : Tendsto H atTop atTop)
    (sigma tau : Fin n → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (H x) (ZeroForcedOscillation.equalRealPartZeroPackage T beta) n)
    (hre :
      ∀ i x, ∀ z ∈ (input x).layer i, z.re ≤ tau i)
    {z : ℂ} (hzero : RiemannHypothesis.IsNontrivialZero z)
    (hzim : 0 < z.im) (hzre : z.re = beta) :
    z.im ≤ T := by
  have hzmem :
      z ∈ ZeroForcedOscillation.equalRealPartZeroPackage T beta :=
    fixedCluster_contains_positiveSameRealPartZeros_of_thresholds
      hbetaOne hH sigma tau hsigma hsigmaOne hthreshold input hre
      hzero hzim hzre
  exact le_trans (le_abs_self z.im)
    (ZeroForcedOscillation.mem_equalRealPartZeroPackage.mp hzmem).2.1

theorem not_equalRealPartZeroPackage_thresholds_of_positiveSameRealPartZero_above
    {beta T : ℝ} (hbetaOne : beta < 1)
    {n : ℕ} {H : ℝ → ℝ} (hH : Tendsto H atTop atTop)
    (sigma tau : Fin n → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (H x) (ZeroForcedOscillation.equalRealPartZeroPackage T beta) n)
    (hre :
      ∀ i x, ∀ z ∈ (input x).layer i, z.re ≤ tau i)
    {z : ℂ} (hzero : RiemannHypothesis.IsNontrivialZero z)
    (hzim : 0 < z.im) (hzre : z.re = beta) (habove : T < z.im) :
    False := by
  have hbound :=
    equalRealPartZeroPackage_bounds_all_positiveSameRealPartZeros_of_thresholds
      hbetaOne hH sigma tau hsigma hsigmaOne hthreshold input hre
      hzero hzim hzre
  exact (not_lt_of_ge hbound) habove

end PrimeNumberTheorem
