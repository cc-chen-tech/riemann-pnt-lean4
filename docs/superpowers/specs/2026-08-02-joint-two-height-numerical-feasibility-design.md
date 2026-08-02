# Joint two-height numerical feasibility design

## Goal

Extract and audit the real-arithmetic parameter theorem needed by a later
two-height transfer.  For every target real part `beta` with

```text
2 / 3 < beta < 1,
```

the public theorem chooses the seven parameters

```text
sigma tau alpha gammaLow gammaHigh epsilonLow epsilonHigh
```

and proves the two low-layer and two Carlson-strip exponents are strictly
negative with explicit positive margins.

This is a numerical feasibility result only.  It does not prove decay of an
actual zeta-zero tail, bound a contour remainder, connect the E2 energy to an
explicit formula, or exclude any zero.

## Stack and provenance

The branch is stacked directly on Draft PR #278 at commit `b5f5e043`.  The
mathematical construction is audited from research commits `71fe009e` and
`28105ae9`, but those commits are not cherry-picked because their imports
would bring the old analytic two-height and full-tail dependency chain.

The new implementation re-lands only the pure real-arithmetic core.  It must
not import modules defining actual zero sets, zero counts, explicit-formula
tails, contour remainders, smoothing, or Witness assumptions.

## Module boundary

### `ZeroDensityLayerBudgetTwoHeightNumericalCore`

Create

```text
PrimeNumberTheorem/ZeroDensityLayerBudgetTwoHeightNumericalCore.lean
```

as the single numerical source for the following exact definitions:

```lean
def carlsonTwoHeightDensityExponent (sigma : ℝ) : ℝ :=
  4 * sigma * (1 - sigma)

noncomputable def carlsonTwoHeightBalancedCut
    (sigma alpha : ℝ) : ℝ :=
  carlsonTwoHeightDensityExponent sigma * alpha /
    (carlsonTwoHeightDensityExponent sigma + 1)

def targetAmplitudeCarlsonTwoHeightLowExponent
    (beta sigma tau gamma : ℝ) : ℝ :=
  carlsonTwoHeightDensityExponent sigma * gamma + tau - beta

def targetAmplitudeCarlsonTwoHeightHighExponent
    (beta sigma tau alpha gamma : ℝ) : ℝ :=
  carlsonTwoHeightDensityExponent sigma * alpha + tau - beta - gamma

noncomputable def targetAmplitudeCarlsonTwoHeightBalancedSlope
    (sigma : ℝ) : ℝ :=
  carlsonTwoHeightDensityExponent sigma ^ 2 /
    (carlsonTwoHeightDensityExponent sigma + 1)

noncomputable def targetAmplitudeCarlsonTwoHeightBalancedExponent
    (beta sigma tau alpha : ℝ) : ℝ :=
  tau - beta +
    targetAmplitudeCarlsonTwoHeightBalancedSlope sigma * alpha
```

The public algebraic lemmas are limited to what the joint theorem and future
adapters actually consume:

- `carlsonTwoHeightDensityExponent_pos` and
  `carlsonTwoHeightDensityExponent_lt_one`, giving `0 < q < 1` when
  `1 / 2 < sigma < 1`;
- `carlsonTwoHeightBalancedCut_pos` and
  `carlsonTwoHeightBalancedCut_lt_alpha`, giving
  `0 < gammaHigh < alpha` when `0 < alpha`;
- `targetAmplitudeCarlsonTwoHeightLowExponent_balanced` and
  `targetAmplitudeCarlsonTwoHeightHighExponent_balanced`, identifying both
  exponents at `gammaHigh` with the common balanced exponent;
- `targetAmplitudeCarlsonTwoHeightBalancedSlope_pos` and
  `targetAmplitudeCarlsonTwoHeightBalancedSlope_lt_half`.

No analytic theorem is moved into this module.  Future analytic modules must
import this numerical core instead of redefining these formulas.

### `ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility`

Create

```text
PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility.lean
```

with the public theorem

```lean
theorem exists_jointTwoHeightTargetAmplitudeParameters
    {beta : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    ∃ sigma tau alpha gammaLow gammaHigh epsilonLow epsilonHigh : ℝ,
      1 / 2 < sigma ∧
      sigma < tau ∧
      tau < beta ∧
      sigma < 1 ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      gammaLow = alpha / 2 ∧
      0 < gammaLow ∧
      gammaLow ≤ alpha ∧
      gammaHigh = carlsonTwoHeightBalancedCut sigma alpha ∧
      0 < gammaHigh ∧
      gammaHigh < alpha ∧
      0 < epsilonLow ∧
      0 < epsilonHigh ∧
      gammaLow + sigma - beta + epsilonLow < 0 ∧
      alpha + sigma - beta - gammaLow + epsilonLow < 0 ∧
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gammaHigh + epsilonHigh < 0 ∧
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gammaHigh + epsilonHigh < 0
```

The theorem keeps all constants explicit.  It does not replace them with a
structure, hide either margin in a fresh existential, or weaken the result
to a single inequality.

## Construction

Set

```text
threshold = (3 * beta - 1) / 2
```

and choose `sigma` strictly between `1 / 2` and `threshold`.  With

```text
q = 4 * sigma * (1 - sigma),
slope = q^2 / (q + 1),
```

the core lemma `slope < 1 / 2` gives

```text
slope * (1 - beta) + sigma - beta < 0.
```

Choose `tau` strictly between `sigma` and

```text
beta - slope * (1 - beta).
```

The following three upper bounds are then strictly above the contour floor
`1 - beta`:

- `1`;
- `2 * (beta - sigma)`, which closes both low-layer exponents at
  `gammaLow = alpha / 2`;
- `(beta - tau) / slope`, which closes the common balanced Carlson exponent.

Choose `alpha` strictly between `1 - beta` and the minimum of those bounds,
set

```text
gammaLow = alpha / 2,
gammaHigh = q * alpha / (q + 1),
```

and take each epsilon to be half the negative of its corresponding common
exponent.  The strict assumptions `2 / 3 < beta < 1` are part of the public
contract; this PR makes no endpoint claim at `beta = 2 / 3`.

## Tests and audit

Use test-first contracts in this order:

1. an exact-formula contract for the numerical core, initially failing
   because the new module and declarations do not exist;
2. the minimal definitions and algebraic lemmas needed to make that contract
   pass;
3. an exact theorem contract for all seven witnesses and all four strict
   negative-margin inequalities, initially failing because the joint theorem
   does not exist;
4. the joint construction and proof;
5. axiom audits for both public modules.

The final serial verification order is:

1. numerical-core implementation;
2. numerical-core exact contract;
3. numerical-core axiom audit;
4. joint-theorem implementation;
5. joint-theorem exact contract;
6. joint-theorem axiom audit;
7. forbidden-declaration and accidental-axiom scans.

The only accepted axioms in `#print axioms` output are `propext`,
`Classical.choice`, and `Quot.sound`.  The scan must reject `sorry`, `admit`,
new axioms, analytic zero/tail declarations, smoothing declarations, and
Witness declarations in the files added by this PR.

The worktree may contain the ignored local `vendor -> ../../vendor` symlink
needed by Lake.  Neither `vendor` nor `.lake` is committed.

## Explicit exclusions and follow-up

This PR does not port the old full-tail chain and does not add placeholder
interfaces for smoothing.  In particular, it proves none of the following:

- that an actual selected-height or dyadic zeta-zero tail tends to zero;
- that the unsmoothed contour remainder is compatible with target-height
  normalization;
- that PR #278's centered-frozen E2 energy is controlled by a two-height
  explicit formula;
- that a Sharp/Witness lower bound exists uniformly over finite `S`;
- that any zero with real part greater than `2 / 3` is excluded.

Later work may add, in separate PRs and only with real analytic input:

1. a selected-height adapter importing this numerical core;
2. a smoothed or higher-order contour transfer from outer height to the low
   probing height;
3. a bridge from that transfer to the E2 centered-frozen energy dichotomy.

Witness remains frozen until Sharp supplies a cofinal, `S`-uniform positive
energy lower bound or a quantified degeneration compatible with capacity.

## PR acceptance boundary

The Draft PR is acceptable only if the exact public formulas and theorem type
compile from the #278 base, the contracts pass, the axiom boundary is clean,
and the new source imports remain numerical.  Its mathematical conclusion is
precisely:

> For every fixed `2 / 3 < beta < 1`, the stated seven real parameters exist
> and make all four displayed numerical exponents strictly negative with
> positive explicit margins.

No stronger analytic or zero-free conclusion may appear in the title,
module documentation, contract comments, or PR description.
