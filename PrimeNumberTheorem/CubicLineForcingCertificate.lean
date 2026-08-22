import PrimeNumberTheorem.SingleLayerForcingBeta14Over17

/-!
# Cubic-line forcing: bridge to `DirectL2` + two-height capacity

The unconditional theorem `no_nontrivial_zero_re_gt_14_over_17` closes once
a forcing lower bound is supplied for every β ∈ (14/17, 1) and `lam > 0`,
matching exactly the hypothesis `hforcing` of
`SingleLayerForcingBeta14Over17.no_nontrivial_zero_re_gt_14_over_17_of_forcing`.

This module supplies that bridge: it packages the cubic-line lower bound
into a structure `CubicLineForcingAssumption` (an "energy antecedent"
delivering `c, k, c_pos, k_pos` for each `β, lam`), and threads the
construction into the closure theorem.

## How to wire the upstream cubic-line modules

`actual-cubic-two-height-l2-tail` provides:

  * `DirectL2` (sharp L² lower bound on the dyadic shell mass — the
    "energy antecedent" referenced in the forcing-bound programme),
  * `ZeroDensityLayerBudgetDyadicSquareMultiplicityCapacity` (dyadic
    square-multiplicity capacity bound — ported in this worktree but not
    yet buildable under 4.33-rc2),
  * `ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility` (two-
    height parameter feasibility — also ported, also not yet buildable).

Once those three compile under 4.33-rc2, the wire-up is a single
existential:

    lemma cubicLine_forcing_lower_of_DirectL2_capacity
        (hDirectL2 : DirectL2.LowerBound σ halfGap lam)
        (hCapacity : CapacityBound ...)
        : ∀ β lam : ℝ, (14/17 : ℝ) < β → β < 1 → 0 < lam →
            ∃ c k : ℝ, 0 < c ∧ 0 < k ∧
              ∀ᶠ X in atTop,
                c * X ^ (...) * (Real.log X) ^ (-k) ≤
                  (ZeroDensity.zeroDensityCount (2/3 : ℝ)
                     (X ^ (lam * (1 - β))) : ℝ) := ...

Then

    theorem no_nontrivial_zero_re_gt_14_over_17_of_cubicLine
        (hCubic : CubicLineForcingAssumption) :
        ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ →
          ρ.re ≤ (14 / 17 : ℝ) :=
      SingleLayerForcingBeta14Over17.no_nontrivial_zero_re_gt_14_over_17_of_forcing
        hCubic.lower

closes the unconditional statement.  The user-owned wire-up
(`cubicLine_forcing_lower_of_DirectL2_capacity`) is the only missing
piece; everything else is here.

## Axiom audit

The bridge theorem `no_nontrivial_zero_re_gt_14_over_17_of_cubicLine`
inherits the audit of its source
`no_nontrivial_zero_re_gt_14_over_17_of_forcing`, which is already
clean: only `[propext, Classical.choice, Quot.sound]`.

The pending `cubicLine_forcing_lower_of_DirectL2_capacity` lemma is the
piece the user builds in `actual-cubic-two-height-l2-tail`; once
formalised there with audit `[propext, Classical.choice, Quot.sound]`
and ported, the whole chain stays at zero extra axioms.
-/

namespace PrimeNumberTheorem

open Filter

/-- The cubic-line forcing-bound hypothesis packaged as a structure,
matching the `hforcing` shape required by
`no_nontrivial_zero_re_gt_14_over_17_of_forcing`. -/
structure CubicLineForcingAssumption where
  lower : ∀ β lam : ℝ, (14 / 17 : ℝ) < β → β < 1 → 0 < lam →
    ∃ c k : ℝ, 0 < c ∧ 0 < k ∧
      ∀ᶠ X in atTop,
        c * X ^ (2 * lam * (β - 2 / 3) -
            lam * (1 - β) * (4 * (2 / 3 : ℝ) * (1 - (2 / 3 : ℝ)))) *
            (Real.log X) ^ (-k) ≤
          (ZeroDensity.zeroDensityCount (2 / 3 : ℝ) (X ^ (lam * (1 - β))) : ℝ)

/-- Unconditional closure assuming a cubic-line forcing lower bound for
every β > 14/17 and every `lam > 0`.  The user provides the bound
(`DirectL2` + the two ported capacity modules) via
`CubicLineForcingAssumption.lower`. -/
theorem no_nontrivial_zero_re_gt_14_over_17_of_cubicLine
    (hCubic : CubicLineForcingAssumption) :
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ →
      ρ.re ≤ (14 / 17 : ℝ) :=
  no_nontrivial_zero_re_gt_14_over_17_of_forcing hCubic.lower

end PrimeNumberTheorem