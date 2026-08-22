import PrimeNumberTheorem.ExceptionalZeroAmplificationGateContract

/-!
# Gate instantiation skeleton: the terminal exclusion interface

The terminal assembly of the `β > 2/3` exclusion.  The gate contract's
`AmplificationGateInputs` bundle already packages all six inputs; this
module supplies the structural pieces that do not depend on the cubic
kernel line:

- `seedRoots`: the seed layer `roots T = {ρ₀}` with the `hroots` proof;
- `no_nontrivial_zero_re_gt_two_thirds_of_gateInputs`: the terminal
  theorem — a counterfactual zero with `Re ρ > 2/3` contradicts Carlson,
  conditional on the remaining inputs (branching, separation, window
  certificate, lower count, exponent gap) being supplied for every
  feasible parameter tuple.

The remaining inputs are exactly the L3 windowed-detector conclusion
(`docs/research/windowed-detector-lean-spec.md`): `hbranch`/`hdisjoint`/
`hbranch_le` from the L3 top-layer window detector, `hlower` from the
existing `disjointWindowFamilyLowerCount` bridge, and `hgap` from
`AmplificationGateExponentBudget` (round-36 module).  Once the cubic
kernel line supplies them, the hypothesis of the terminal theorem
becomes provable and the full exclusion follows.

Axiom audit: this module's theorems depend only on the gate contract
(whose audit is clean) and the standard mathlib axioms.
-/

namespace PrimeNumberTheorem
namespace ExceptionalZeroAmplificationGate

open Filter

/-- The seed layer: the single counterfactual zero `ρ₀` at every height. -/
noncomputable def seedRoots (ρ₀ : ℂ) : ℝ → Finset ℂ := fun _ => {ρ₀}

/-- Gate input 1 (`hroots`) for the seed layer. -/
theorem seedRoots_eventually_nonempty (ρ₀ : ℂ) :
    ∀ᶠ T in atTop, 1 ≤ (seedRoots ρ₀ T).card := by
  filter_upwards with T
  dsimp [seedRoots]
  rw [Finset.card_singleton]

/--
Terminal interface: if the six gate inputs are supplied for every feasible
parameter tuple, then no non-trivial zero has real part `> 2/3`.

The counterfactual seed `ρ` with `β = Re ρ > 2/3` is turned into the gate
bundle at `σ = (2/3 + β)/2`, `δ = 1`, `H = 1`, `depth = 2`; the gate
yields `False`, and `amplificationGate_excludes_seed` finishes.
-/
theorem no_nontrivial_zero_re_gt_two_thirds_of_gateInputs
    (hInputs : ∀ β δ σ H : ℝ, ∀ depth : ℕ,
      (2 / 3 : ℝ) < β → β < 1 → (1 / 2 : ℝ) < σ → σ < β → 0 < δ → 0 < H →
        AmplificationGateInputs β δ σ H depth) :
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → ρ.re ≤ (2 / 3 : ℝ) := by
  intro ρ hρ
  by_contra hgt
  have hbeta : (2 / 3 : ℝ) < ρ.re := lt_of_not_ge hgt
  have hre_lt_one : ρ.re < 1 := hρ.2.2
  let σ : ℝ := ((2 / 3 : ℝ) + ρ.re) / 2
  have hσ : (1 / 2 : ℝ) < σ := by dsimp [σ]; linarith
  have hσβ : σ < ρ.re := by dsimp [σ]; linarith
  have hσ1 : σ < 1 := by dsimp [σ]; linarith [hre_lt_one]
  let depth : ℕ := 2
  have G : AmplificationGateInputs ρ.re (1 : ℝ) σ (1 : ℝ) depth :=
    hInputs ρ.re (1 : ℝ) σ (1 : ℝ) depth hbeta hre_lt_one hσ hσβ
      (by norm_num) (by norm_num)
  have hFalse := amplificationGate_of_inputs (β := ρ.re) (δ := 1) (sigma := σ)
    (H := (1 : ℝ)) (depth := depth) G
  exact False.elim hFalse

end ExceptionalZeroAmplificationGate
end PrimeNumberTheorem
