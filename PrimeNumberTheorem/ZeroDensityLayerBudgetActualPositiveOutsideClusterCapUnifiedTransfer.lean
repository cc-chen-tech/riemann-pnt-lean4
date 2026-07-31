import PrimeNumberTheorem.ZeroDensityLayerBudgetActualGlobalRealPartBoundUnifiedTransfer

/-!
# Automatic actual transfer from a positive outside-cluster cap

The global positive-zero real-part cap is weakened to a cap only on zeros
outside the distinguished finite cluster. This leaves target-cluster zeros
available for a genuinely nontrivial reverse transfer.
-/

namespace PrimeNumberTheorem

open Filter

/-- Every positive-ordinate nontrivial zeta zero outside `S` has real part at
most `upper`. Zeros in the distinguished cluster are exempt. -/
def PositiveOutsideClusterRealPartCap
    (S : Finset ℂ) (upper : ℝ) : Prop :=
  ∀ rho : ℂ,
    RiemannHypothesis.IsNontrivialZero rho →
      0 < rho.im →
        rho ∉ S →
          rho.re ≤ upper

/-- A global positive-zero cap specializes to every outside-cluster cap. -/
theorem positiveOutsideClusterRealPartCap_of_global
    {S : Finset ℂ} {upper : ℝ}
    (hglobal :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
          0 < rho.im →
            rho.re ≤ upper) :
    PositiveOutsideClusterRealPartCap S upper := by
  intro rho hzero him _hout
  exact hglobal rho hzero him

/-- Enlarging the distinguished cluster weakens, and therefore preserves, an
outside-cluster cap. -/
theorem PositiveOutsideClusterRealPartCap.mono_cluster
    {S T : Finset ℂ} {upper : ℝ}
    (hcap : PositiveOutsideClusterRealPartCap S upper)
    (hST : S ⊆ T) :
    PositiveOutsideClusterRealPartCap T upper := by
  intro rho hzero him houtT
  apply hcap rho hzero him
  intro hinS
  exact houtT (hST hinS)

/-- Adjoining every real-ordinate nontrivial zero preserves the positive
outside-cluster cap. -/
theorem PositiveOutsideClusterRealPartCap.adjoinRealOrdinateZeros
    {S : Finset ℂ} {upper : ℝ}
    (hcap : PositiveOutsideClusterRealPartCap S upper) :
    PositiveOutsideClusterRealPartCap
      (actualCarlsonAdjoinRealOrdinateZeros S) upper := by
  apply hcap.mono_cluster
  intro rho hrho
  unfold actualCarlsonAdjoinRealOrdinateZeros
  exact Finset.mem_union_left _ hrho

/-- The fully automatic actual Pintz-Carlson-explicit-formula transfer from a
positive real-part cap only on zeros outside the visible cluster.

Unlike the global-cap version, zeros in `S` may lie to the right of `theta`.
The sole remaining lower-bound input is the natural-point target-amplitude
witness for the enlarged visible cluster. -/
theorem
    exists_automaticGoodHeight_positiveOutsideClusterRealPartCapNaturalTargetTransfer
    {S : Finset ℂ} {beta theta : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (htheta : theta < (3 * beta - 1) / 2)
    (hS : IsConjugationInvariantCluster S)
    (hcap : PositiveOutsideClusterRealPartCap S theta) :
    ∃ sigma tau alpha : ℝ,
      1 / 2 < sigma ∧
      sigma < tau ∧
      theta < tau ∧
      tau < beta ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      ∀ (selection : UniformNaturalPointGoodHeightSelection),
        HasFarNaturalPointTargetAmplitudeWitness
            (fun m =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight alpha selection)
                (actualCarlsonAdjoinRealOrdinateZeros S)
                (m : ℝ))
            (fun m => targetZeroPowerAmplitude beta (m : ℝ)) →
        (∃ rate : ℝ,
            0 < rate ∧
            rate ≤ 1 ∧
            Tendsto
              (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
              atTop (nhds 0)) ∧
          HasFarTargetAmplitudeWitness
            relativeChebyshevPsi0Error
            (fun x => targetZeroPowerAmplitude beta x / 2) := by
  rcases
      exists_jointTwoHeightTargetAmplitudeParameters_above_cap
        hbeta hbetaOne htheta with
    ⟨sigma, tau, alpha, gammaLow, gammaHigh,
      epsilonLow, epsilonHigh,
      hsigmaHalf, hsigmaTau, hthetaTau, htauBeta, hsigmaOne,
      hcontour, halpha, halphaOne, _hgammaLowEq,
      hgammaLow, _hgammaLowAlpha, _hgammaHighEq,
      hgammaHigh, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowLow, hlowHigh, hstripLow, hstripHigh⟩
  have hSAdjoined :
      IsConjugationInvariantCluster
        (actualCarlsonAdjoinRealOrdinateZeros S) := by
    intro rho
    exact
      (actualCarlsonAdjoinRealOrdinateZeros_conjugationStable
        S (fun z => (hS z).symm) rho).symm
  have hcapAdjoined :
      PositiveOutsideClusterRealPartCap
        (actualCarlsonAdjoinRealOrdinateZeros S) theta :=
    hcap.adjoinRealOrdinateZeros
  have hreal :
      ∀ rho ∈
        realOrdinateNontrivialZerosOutsideClusterFinset 0
          (actualCarlsonAdjoinRealOrdinateZeros S),
        rho.re < beta := by
    intro rho hrho
    have hempty :=
      realOrdinateNontrivialZerosOutsideClusterFinset_adjoin_eq_empty S
    rw [hempty] at hrho
    simp at hrho
  have hbetaPos : 0 < beta := by
    linarith
  refine
    ⟨sigma, tau, alpha,
      hsigmaHalf, hsigmaTau, hthetaTau, htauBeta,
      hcontour, halpha, halphaOne, ?_⟩
  intro selection hmain
  have hselectedCap :
      ∀ (x : ℝ),
        ∀ rho ∈
          positiveNontrivialZerosOutsideClusterFinset
            (selectedUniformGoodHeight alpha selection x)
            (actualCarlsonAdjoinRealOrdinateZeros S),
          sigma < rho.re →
            rho.re ≤ tau := by
    intro x rho hrho _hright
    rcases
        mem_positiveNontrivialZerosOutsideClusterFinset.mp hrho with
      ⟨hzero, him, _hheight, houtside⟩
    exact
      (hcapAdjoined rho hzero him houtside).trans hthetaTau.le
  exact
    unified_automaticGoodHeight_twoHeight_naturalTargetTransfer
      (S := actualCarlsonAdjoinRealOrdinateZeros S)
      (beta := beta) (sigma := sigma) (tau := tau) (alpha := alpha)
      (gammaLow := gammaLow) (epsilonLow := epsilonLow)
      (gammaHigh := gammaHigh) (epsilonHigh := epsilonHigh)
      hbetaPos halphaOne hcontour selection hSAdjoined
      hsigmaHalf hsigmaOne halpha
      hgammaLow hepsilonLow hlowLow hlowHigh
      hgammaHigh hgammaHighAlpha.le hepsilonHigh
      hstripLow hstripHigh hselectedCap hreal hmain

end PrimeNumberTheorem
