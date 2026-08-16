/-
# DRAFT (uncompiled): gate instantiation and the main theorem

Paper: `docs/research/gate-windowed-detector-instantiation.md`.

This skeleton pins the Lean shape of goal steps (4) and (5): the six gate
inputs instantiated from the windowed detector, and the final exclusion
theorem.  All analytic inputs are named; each `sorry` cites its supplier
(L1/L2/L3 documents, proved repo modules).  Uncompiled.

-/
import PrimeNumberTheorem.ExceptionalZeroAmplificationGateContract
import PrimeNumberTheorem.HalfIsolatedZeroDichotomy.DetectionPointChoice

namespace PrimeNumberTheorem
namespace WindowedDetectorGate

open Filter
open ExceptionalZeroAmplificationGate

/-- Supplier of one windowed successor per separated height window: the L3
conclusion.  For a seed `rho` (real part `beta`) and a height window
`[T0, T0+H]` containing no top-layer zero, the L3 comparison (gap,
eta-avoidance, cubic margin) forces a top-layer zero inside the window.
Statement shape only. -/
structure WindowedDetectorInput (beta gap sigma T0 H : ℝ) where
  hgapPos : 0 < gap
  hWindow : 0 < T0
  -- the L3 analytic conclusion, to be supplied by the L3 assembly
  forces_zero :
    ∀ γ₀ : ℝ, T0 ≤ γ₀ → γ₀ ≤ T0 + H →
      (∀ ρ, RiemannHypothesis.IsNontrivialZero ρ → ρ.re = beta →
        T0 ≤ ρ.im → ρ.im ≤ T0 + H → False) →
      ∃ ρ, RiemannHypothesis.IsNontrivialZero ρ ∧ ρ.re = beta ∧
        T0 ≤ ρ.im ∧ ρ.im ≤ T0 + H

/-- MAIN THEOREM (goal step 5): no non-trivial zero strictly right of 2/3.

Proof shape (by contradiction):
- assume `rho_0` with `2/3 < beta := Re rho_0`;
- pick `sigma in (2/3, beta)`, `gap`, `T0`, `H = T0^h'` per the L3 parameter
  feasibility (`gap > (1-h') gamma0 / lambda` feasible for every `beta`);
- the windowed detector input (L3) supplies one successor per separated
  window: `q(T) = H / (2 delta)`-ary branching per node (instantiation
  table in the paper doc);
- `hroots`/`hbranch`/`hdisjoint`/certificate/`hlower`/`hgap` all hold;
- `amplificationGate` yields `False`, and
  `amplificationGate_excludes_seed` finishes. -/
theorem no_nontrivial_zero_re_gt_two_thirds
    (hDetector :
      ∀ {beta gap sigma T0 H : ℝ}, 2 / 3 < beta → sigma < beta →
        2 / 3 < sigma → 0 < gap →
        Nonempty (WindowedDetectorInput beta gap sigma T0 H)) :
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → ρ.re ≤ (2 / 3 : ℝ) := by
  intro ρ hρ
  by_contra hgt
  have hbeta : (2 / 3 : ℝ) < ρ.re := lt_of_not_ge hgt
  -- parameter choice (L3 feasibility)
  let beta : ℝ := ρ.re
  let sigma : ℝ := (2 / 3 + beta) / 2
  have hsigma : (2 / 3 : ℝ) < sigma ∧ sigma < beta := by
    dsimp [sigma]; constructor <;> linarith
  let gap : ℝ := (beta - sigma) / 2
  have hgap : 0 < gap := by dsimp [gap]; positivity
  -- T0, H, delta: choose T0 large, H = T0^h', delta > 0 constant
  let T0 : ℝ := 100
  let H : ℝ := T0
  -- six gate inputs (each from the instantiation table)
  -- hroots: the seed
  sorry -- roots T = {ρ}; nonempty
  -- hbranch: per separated window, one forced successor; q T = H/(2δ)
  sorry -- uses hDetector / L3 per window; δ-分离保证窗口不交
  -- hdisjoint: windows 2δ-separated
  sorry -- topLayerWindow_disjoint_of_imag_separation
  -- certificate C: windows = window index finset, cluster = forced zeros
  sorry
  -- hlower: forced zeros counted into zeroDensityCount sigma (T+H)
  sorry -- disjointWindowFamilyLowerCount_eventually_le_zeroDensity
  -- hgap: q(T)^depth = (H/(2δ))^depth beats Carlson T^(4σ(1-σ)) log^4
  sorry -- depth chosen with (h'-κ)·depth > 4σ(1-σ); h'=1, κ=0 here
  -- apply the gate
  exact False.elim (amplificationGate hsigma.1 hsigma.2 _ _ _ _ _ _ _ _ _)

end WindowedDetectorGate
end PrimeNumberTheorem
