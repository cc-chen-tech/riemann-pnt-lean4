import HardyTheorem.ConreyExplicitIntegralBridge
import HardyTheorem.ConreySimpleZeroCount

open Filter Topology

namespace HardyTheorem

/-!
# The exact remaining analytic interface for Conrey's two-fifths theorem

The elementary double integral and the multiplicity-sensitive zero counts are
already formalized.  This module records, as an explicit hypothesis rather
than an axiom or theorem, the remaining analytic conclusion of Conrey's
argument-principle and mollified mean-square proof.
-/

/-- The simple-zero proportion supplied by the explicit double integral. -/
noncomputable def conreyExplicitIntegralProportion : ℝ :=
  1 - Real.log conreyExplicitMeanSquareIntegral / conreyExplicitR

/-- The exact eventual lower-bound conclusion still to be supplied by the
analytic Levinson--Conrey argument.  Quantifying over every strict lower
constant exposes the `o(1)` margin and avoids asserting the endpoint itself. -/
def conreyExplicitAnalyticLowerBound : Prop :=
  ∀ c : ℝ, c < conreyExplicitIntegralProportion →
    ∀ᶠ T in atTop,
      c * (PrimeNumberTheorem.RiemannVonMangoldt.riemannZeroCount T : ℝ) ≤
        (positiveCriticalLineSimpleZeroCount T : ℝ)

/-- Once the genuine analytic lower bound is proved, the already certified
strict numerical margin gives Conrey's genuine `> 2/5` simple-zero target. -/
theorem conreyTwoFifthsSimpleZerosTarget_of_explicit_analytic_lower_bound
    (h : conreyExplicitAnalyticLowerBound) :
    conreyTwoFifthsSimpleZerosTarget := by
  let c : ℝ := ((2 : ℝ) / 5 + conreyExplicitIntegralProportion) / 2
  have hmargin : (2 : ℝ) / 5 < conreyExplicitIntegralProportion := by
    exact conreyExplicitIntegralProportion_gt_two_fifths
  have hc_lower : (2 : ℝ) / 5 < c := by
    dsimp [c]
    linarith
  have hc_upper : c < conreyExplicitIntegralProportion := by
    dsimp [c]
    linarith
  exact ⟨c, hc_lower, h c hc_upper⟩

end HardyTheorem
