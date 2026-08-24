import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTSignedReverseZeroFree
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedGoodHeightOptimality

/-!
# Cofinal dynamic-height reverse transfer to a global zeta zero-free half-plane

The finite-height signed reverse theorem excludes right-edge zeros only up to a
fixed height `H`.  A genuinely dynamic reverse transfer must explain why
zero-freeness along a cofinal height schedule excludes every fixed zero.

This module supplies that bridge.  It proves that selected polynomial good
heights, and in particular the weighted-balanced height shared by Carlson and
the explicit formula, tend to infinity.  It then shows that eventual
finite-height right-edge zero-freeness along any cofinal schedule implies the
global statement that every nontrivial zeta zero lies strictly to the left of
the target line.

The theorem does not construct the eventual finite-height zero-free input; that
is supplied by the signed reverse transfer and its analytic hypotheses.
-/

open scoped Topology

noncomputable section

namespace PrimeNumberTheorem

open Filter

/-- Every nontrivial zeta zero lies strictly to the left of `Re(s) = beta`. -/
def GlobalRightEdgeZeroFree (beta : ℝ) : Prop :=
  ∀ rho : ℂ,
    RiemannHypothesis.IsNontrivialZero rho →
      rho.re < beta

/-- A selected good height immediately below a positive polynomial scale is
cofinal. -/
theorem selectedUniformGoodHeight_tendsto_atTop
    {alpha : ℝ}
    (halpha : 0 < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (selectedUniformGoodHeight alpha selection)
      atTop
      atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  have hpower :
      Tendsto (fun x : ℝ => x ^ alpha) atTop atTop :=
    tendsto_rpow_atTop halpha
  have hlarge :=
    (tendsto_atTop.1 hpower) (b + 1)
  filter_upwards
      [hlarge, eventually_selectedUniformGoodHeight_mem halpha selection]
      with x hx hselected
  linarith [hselected.1]

/-- The actual weighted-balanced good height used by the Carlson/explicit
formula transfer tends to infinity. -/
theorem
    actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_tendsto_atTop
    {beta : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
        beta sigma tau selection)
      atTop
      atTop := by
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  change
    Tendsto
      (selectedUniformGoodHeight
        (actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau)
        selection)
      atTop atTop
  exact selectedUniformGoodHeight_tendsto_atTop hspec.2.1 selection

/-- Global right-edge zero-freeness is exactly finite-height right-edge
zero-freeness at every height. -/
theorem globalRightEdgeZeroFree_iff_forall_finiteHeight
    (beta : ℝ) :
    GlobalRightEdgeZeroFree beta ↔
      ∀ H : ℝ, FiniteHeightRightEdgeZeroFree beta H := by
  constructor
  · intro hglobal H rho hzero hheight
    exact hglobal rho hzero
  · intro hfinite rho hzero
    exact hfinite |rho.im| rho hzero le_rfl

/-- Eventual finite-height zero-freeness along any cofinal height schedule
excludes every nontrivial zero at or to the right of the target line. -/
theorem globalRightEdgeZeroFree_of_eventually_finiteHeight_of_tendsto
    {beta : ℝ} {height : ℝ → ℝ}
    (hheight : Tendsto height atTop atTop)
    (hfinite :
      ∀ᶠ x : ℝ in atTop,
        FiniteHeightRightEdgeZeroFree beta (height x)) :
    GlobalRightEdgeZeroFree beta := by
  intro rho hzero
  have hlarge :
      ∀ᶠ x : ℝ in atTop, |rho.im| ≤ height x :=
    (tendsto_atTop.1 hheight) |rho.im|
  have hboth :
      ∀ᶠ x : ℝ in atTop,
        FiniteHeightRightEdgeZeroFree beta (height x) ∧
          |rho.im| ≤ height x :=
    hfinite.and hlarge
  rcases hboth.exists with ⟨x, hzeroFree, hrhoHeight⟩
  exact hzeroFree rho hzero hrhoHeight

/-- Eventual finite-height zero-freeness at the actual weighted-balanced good
height implies a global right-edge zeta zero-free half-plane. -/
theorem
    globalRightEdgeZeroFree_of_eventually_actualWeightedBalancedGoodHeight
    {beta : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hfinite :
      ∀ᶠ x : ℝ in atTop,
        FiniteHeightRightEdgeZeroFree beta
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)) :
    GlobalRightEdgeZeroFree beta :=
  globalRightEdgeZeroFree_of_eventually_finiteHeight_of_tendsto
    (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_tendsto_atTop
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection)
    hfinite

end PrimeNumberTheorem
