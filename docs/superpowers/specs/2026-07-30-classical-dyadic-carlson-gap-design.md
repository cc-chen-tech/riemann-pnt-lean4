# Classical Dyadic Carlson Gap Design

## Purpose

Close the two asymptotic inputs left explicit by the automatic dyadic
selected-height transfer:

- `IsCarlsonMovingDyadicLogPowerGap delta`;
- `IsSelectedHeightDynamicZeroFree H delta`.

The construction uses the proved classical zero-free region at the existing
subpolynomial selected good height

```text
H(x) = exp(O(sqrt(log x))).
```

At this height the classical width is of order `1 / sqrt(log x)`, not
`1 / log x`. This distinction is essential: a polynomial-height classical
width cannot pay the dynamic dyadic layer-count cost.

## Chosen Width

For `rate > 0`, define

```text
delta(m) = rate / (1 + sqrt(log m)).
```

The added `1` makes the width positive at every natural sample while
preserving its asymptotic scale.

The dyadic exponent margin has leading term

```text
(delta(m) / 2) * log m
  = Omega(rate * sqrt(log m)),
```

whereas the complete logarithmic cost is only

```text
3 * log(delta(m)^(-1)) + 4 * log(log m)
  = O(log log m).
```

Thus the exact `IsCarlsonMovingDyadicLogPowerGap` expression tends to
positive infinity.

## Zero-Free Adapter

Use `exists_classicalTruncationRightEdge_nontrivialZerosFinset` to obtain
`b > 0`. Let

```text
alpha = classicalAdmissibleBalancedRate b
rate  = alpha / 2.
```

The existing optimizer inequality gives `alpha^2 <= b`, hence
`rate * alpha < b`. The theorem
`dynamicHeight_classicalZeroFreeWidth_ge` then proves, at every sufficiently
large natural sample and every selected good height
`T <= exp(alpha * sqrt(log m))`,

```text
delta(m) <= rate / sqrt(log m) <= b / log(T + 6).
```

Every nontrivial zero visible below `T` therefore satisfies

```text
Re rho <= 1 - delta(m).
```

This is exactly `IsSelectedHeightDynamicZeroFree`.

## Public Surface

Create
`PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonGap.lean`
with:

- `classicalAdmissibleDyadicCarlsonGapWidth`;
- positivity and eventual `delta <= 1 / 8`;
- `isCarlsonMovingDyadicLogPowerGap_classicalAdmissible`;
- `isSelectedHeightDynamicZeroFree_selectedClassicalAdmissible`;
- `exists_selectedClassicalAdmissibleDyadicCarlsonZeroFreeGap`.

Add an exact contract and a standalone axiom audit.

## Scope Boundary

This module closes a real growth-rate and zero-free compatibility bridge. It
does not yet reassemble the complete PNT error at the classical selected
height. It does not modify or depend on the separately owned complementary
bound or VK-edge modules, and it does not claim a new zero-free region, a new
zero-density theorem, an unconditional oscillation theorem, or RH.
