# Actual target-amplitude full-tail conjugation design

## Scope

This stack upgrades the stack38 positive-ordinate outside-cluster theorem to
the complete finite outside-cluster zero tail.  It reuses the existing
conjugation decomposition and real-ordinate residual theorem.

It does not modify the complementary-zero module, any VK-edge module, or the
oscillation-cluster machinery.

## Existing decomposition

For a conjugation-invariant cluster `S`, the repository already proves

```text
full outside-cluster tail norm
  <= positive tail norm + positive tail norm + real-ordinate tail norm.
```

It also provides an abstract transfer:

```text
positive tail = o(amplitude)
real tail     = o(amplitude)
--------------------------------
full tail     = o(amplitude).
```

## New concrete inputs

The positive input is stack38:

```text
dynamicPositiveOutsideClusterPNTTailNorm (x ^ alpha) S
  / x ^ (beta - 1) -> 0.
```

The real-ordinate input is already available whenever every real-ordinate
nontrivial zero outside `S` has real part strictly below `beta`.

Since all three tail objects are norms, their absolute values simplify
without adding sign hypotheses.

## Output

The stack exports:

- a concrete `TargetAmplitudeNegligible` theorem for the complete
  outside-cluster tail;
- the equivalent direct limit
  `fullTail / targetZeroPowerAmplitude beta -> 0`.

## Claim boundary

This closes the finite zero-tail contribution relative to a selected target
zero amplitude under the stated cap and margin assumptions.  It does not yet
show that the explicit-formula contour remainder is negligible, nor does it
produce an unconditional Omega theorem.
