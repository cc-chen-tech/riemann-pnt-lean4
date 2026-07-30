# Half-Sharp Classical Carlson Rate Design

## Objective

Close the strict `theta < 1 / 2` gap in the pointwise Carlson layer estimate.
The previous theta family proves every rate below one half of the gap rate.
This stack attains the endpoint exactly by retaining the bounded correction
that was discarded in the asymptotic comparison.

## Endpoint identity

Write

```text
s = sqrt(log m)
delta = rate / (1 + s).
```

The Carlson saving in the layered coarse exponent is

```text
delta * log m / 2 = rate * s^2 / (2 * (1 + s)).
```

At `theta = 1 / 2`, the exact difference is

```text
rate * s^2 / (2 * (1 + s))
  - (rate * s / 2 - rate / 2)
  = rate / (2 * (1 + s))
  >= 0.
```

Therefore

```text
rate * s / 2 - rate / 2
  <= delta * log m / 2.
```

The missing endpoint is recovered by multiplying the previous majorant by the
fixed factor `exp(rate / 2)`. No new zero-density input or change of layer
schedule is needed.

## Public result

Define

```text
classicalDyadicCarlsonHalfSqrtLogMajorant C rate
  = classicalDyadicCarlsonThetaSqrtLogMajorant
      (C * exp(rate / 2)) rate (1 / 2).
```

Prove:

1. the layered coarse mass is eventually bounded by this endpoint majorant;
2. the endpoint majorant has the exact polynomial-times-exponential form;
3. it tends to zero;
4. the actual multiplicity-aware fixed-anchor zeta mass is eventually bounded
   by it;
5. the balanced verified rate is exactly
   `classicalAdmissibleBalancedRate b / 4`, strictly improving the old
   `classicalAdmissibleBalancedRate b / 8`.

## Scope

This stack contains the endpoint mathematical improvement only. Propagation
through moving masses and the full explicit formula belongs in the next
stacked PR. Complementary-zero and VK-edge modules remain untouched.

## Audit

The main endpoint and rate identities must compile and depend only on
`propext`, `Classical.choice`, and `Quot.sound`.
