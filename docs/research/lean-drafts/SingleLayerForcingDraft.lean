/-
# DRAFT (uncompiled): single-layer forcing, beta > 14/17

Paper: `docs/research/single-layer-forcing-beta-14-17.md`.
Shape-only draft; the analytic pieces live in the cubic worktree
(`actual-cubic-two-height-l2-tail`), which is an active user worktree —
coordinate with that line before implementing there.

ALIGNMENT with the user's numerical core (2026-08-15, read-only check):
- `ZeroDensityLayerBudgetDirectL2NumericalCore` defines exactly
  `directL2RightPowerExponent beta lambda theta gamma sigma
    = 2 lambda (sigma - beta) + gamma (q sigma - 2 + theta)`
  and the feasibility theorems
  `exists_directL2_twoSidedParameters`,
  `directL2RightPowerExponent_witness_le_neg_margin`,
  `directL2LeftPowerExponent_fixed_le_neg_margin`,
  `directL2RightPowerMargin_pos`, `directL2LeftPowerMargin_pos`.
- The counting exponent used here is
  `2 lam (beta - sigma) - gamma (q sigma + theta)
     = - directL2RightPowerExponent beta lam theta gamma sigma - 2 gamma`
  (the extra `2 gamma` is the seed-height normalization `T0 = X^gamma`;
  the window-length factor `+ lam` in the energy form cancels in the
  ratio comparison).
- The contradiction condition `e_M / gamma > q sigma` in the theta = 0,
  gamma -> g, sigma -> 2/3+ limit is exactly `beta > 14/17`
  (exact-fraction check in the paper doc).
-/

import PrimeNumberTheorem.ZeroDensityAmplificationAudit
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlson

namespace PrimeNumberTheorem
namespace SingleLayerForcing

open Filter
open scoped BigOperators

/-- INPUT (cubic worktree): the F_R/F_L tail bound.  Expected shape of the
theorem owned by `ZeroDensityLayerBudgetDirectL2NumericalCore`:

    theorem tail_bound (beta lam gamma sigma : ℝ)
        (hparams : DirectL2Feasible beta lam gamma sigma) :
        -- GramTail(X) <= C X^(-1/20) (1 + log X)^(5+r) in the fixed grid

represented here as an input structure. -/
structure CubicTailInput (beta lam gamma sigma : ℝ) where
  feasible : Prop
  -- tail bound: for X large, the sigma-right zero tail in the window
  -- [X, X^lam] is bounded by C X^(2 lam sigma + lam + gamma (q sigma - 2)) M
  tail_le :
    ∃ C, 0 ≤ C ∧ ∀ᶠ X in atTop,
      cubicTailEnergy X ≤
        C * X ^ (2 * lam * sigma + lam + gamma * (4 * sigma * (1 - sigma) - 2))
          * (windowedZeroCount sigma (X ^ gamma) : ℝ) * (1 + Real.log X) ^ 5

/-- INPUT (proved, main): Carlson majorant at `sigma`. -/
structure CarlsonInput (sigma : ℝ) where
  hσ : 1 / 2 < sigma
  hσ1 : sigma < 1

/-- INPUT (vk-edge / zero-forced oscillation): the seed energy lower bound
`X^(2 lam beta + lam - 2 gamma)` at scale X (the strict pi/2 constant is
not needed for the counting contradiction — any positive constant works
for the exponent comparison). -/
structure SeedEnergyInput (beta lam gamma : ℝ) where
  lower :
    ∃ C, 0 < C ∧ ∀ᶠ X in atTop,
      C * X ^ (2 * lam * beta + lam - 2 * gamma) ≤ seedEnergy X

/-- MAIN (single layer): a seed with `beta > 14/17` contradicts Carlson.

Proof shape:
- tail_le + seed lower: if the sigma-right count in the window is M then
  seedEnergy ≤ tailEnergy ≤ C X^(...) M log^5, so
  M ≥ c X^(2 lam (beta - sigma) - gamma q(sigma)) log^-5;
- with the optimal parameters (gamma -> g, sigma -> 2/3+) the exponent
  beats q(sigma) = 8/9 exactly when beta > 14/17;
- one-window contradiction via
  `disjointWindowFamily_carlson_contradiction` (depth 1);
- conclusion: False. -/
theorem singleLayerCarlsonContradiction
    {beta lam gamma sigma : ℝ}
    (hbeta : (14 / 17 : ℝ) < beta) (hsigma : (2 / 3 : ℝ) < sigma)
    (hsigma_lt : sigma < beta)
    (hparams : 0 < lam) (hgamma : 0 < gamma)
    (C : CubicTailInput beta lam gamma sigma)
    (S : SeedEnergyInput beta lam gamma)
    (hcar : CarlsonInput sigma) :
    False := by
  sorry
  -- 1. windowed count lower bound from tail_le + S.lower
  -- 2. exponent comparison: 2 lam (beta - sigma) - gamma q(sigma) > gamma q(sigma)
  --    (i.e. beta > 14/17 in the optimal limit; here assumed directly)
  -- 3. disjointWindowFamily_carlson_contradiction with depth 1

/-- FINAL PARTIAL THEOREM: no non-trivial zero with Re > 14/17. -/
theorem no_nontrivial_zero_re_gt_fourteen_over_seventeen
    (hInputs :
      ∀ {beta lam gamma sigma : ℝ}, (14 / 17 : ℝ) < beta → (2 / 3 : ℝ) < sigma →
        sigma < beta → 0 < lam → 0 < gamma →
        CubicTailInput beta lam gamma sigma ∧ SeedEnergyInput beta lam gamma) :
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → ρ.re ≤ (14 / 17 : ℝ) := by
  intro ρ hρ
  by_contra hgt
  have hbeta : (14 / 17 : ℝ) < ρ.re := lt_of_not_ge hgt
  let beta : ℝ := ρ.re
  let sigma : ℝ := (2 / 3 + beta) / 2
  have hsigma : (2 / 3 : ℝ) < sigma ∧ sigma < beta := by
    dsimp [sigma]; constructor <;> linarith
  let lam : ℝ := 1.1
  let gamma : ℝ := lam * (1 - beta)
  have hlam : 0 < lam := by norm_num
  have hgamma : 0 < gamma := by dsimp [gamma]; positivity
  rcases hInputs (beta := beta) (lam := lam) (gamma := gamma) (sigma := sigma)
      hbeta hsigma.1 hsigma.2 hlam hgamma with ⟨C, S⟩
  have hcar : CarlsonInput sigma := ⟨by linarith [hsigma.1], by linarith [hsigma.2]⟩
  exact False.elim (singleLayerCarlsonContradiction hbeta hsigma.1 hsigma.2
    hlam hgamma C S hcar)

end SingleLayerForcing
end PrimeNumberTheorem
