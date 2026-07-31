# Prime-Side Detector Main-Pole Boundary

## Proved statement

For a finite real coefficient family supported on positive natural indices,
the detector value at `s = 1` is

```text
A(1) = sum_n a_n / n.
```

The Lean module proves the exact decomposition

```text
A(1) = positive weighted mass - negative weighted mass.
```

Consequently:

- nonnegative coefficients with at least one positive coefficient imply
  `A(1) > 0`;
- such a detector cannot vanish at `s = 1`;
- `A(1) = 0` is equivalent to equality of the positive and negative weighted
  masses;
- a nontrivial detector which vanishes at `s = 1` must have both positive and
  negative supported coefficients.

All five public theorems are proved without `sorry`, `admit`, or a
project-defined axiom. Their exact types are locked by
`Test/PrimeSideDetectorMainPoleContract.lean`.

## What this rules out

The naive detector strategy asks for a nonzero finite Dirichlet polynomial
whose coefficients remain nonnegative on the prime side while the detector
cancels the zeta pole at `s = 1`. The proved positivity theorem shows that
these two requirements are incompatible.

Thus any finite detector which cancels the main pole must introduce signed
coefficients. The negative weighted mass is not a technical artifact: at
`s = 1` it must exactly equal the positive weighted mass.

## Remaining analytic gate

The next step would require a signed detector which simultaneously:

1. vanishes at `s = 1` and at the selected already-used zero poles;
2. retains a quantitative prime-side response;
3. makes that response strictly larger than the cancellation loss caused by
   the negative coefficients.

The current theorem does not construct such a detector and does not establish
the third inequality. A viable continuation must provide the detector and a
strict, instantiable response-minus-cancellation bound; a conditional wrapper
would not close the gap.

## Claim boundary

This milestone is a finite-sum algebraic obstruction. It does not prove:

- a detector vanishing at prescribed zeta zeros;
- a repeatable Sharp lower bound after deleting old zero pairs;
- a new zeta zero or a Carlson contradiction;
- the Riemann hypothesis.
