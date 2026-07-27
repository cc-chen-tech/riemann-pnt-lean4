# VK-edge fixed-proportion contradiction audit

## Verified conditional theorem

Let

```text
F_rho(y) =
  norm rho * (chebyshevPsi (exp y) - exp y) * exp (-re rho * y).
```

Assume `rho` is a zeta zero with `1 / 2 < re rho < 1`, and fix
`epsilon > 0`. The swept Gaussian theorem supplies a missing odd harmonic
`k` and an explicit constant

```text
c2 = centeredSharpenedSweptOrdinaryL2Constant epsilon rho k > 0
```

such that the local second moment is eventually larger than

```text
c2 * log Y.
```

The new fixed-proportion endpoint proves the following genuine conditional
implication. If `C4 > 0` and the true error additionally satisfies the
external fourth-moment hypothesis

```text
integral over [log Y, (1 + epsilon) log Y] of F_rho(y)^4
  <= C4 * log Y,
```

then eventually

```text
measure {
  y in [log Y, (1 + epsilon) log Y] |
  c2 / (2 * epsilon) < F_rho(y)^2
}
>
(c2^2 / (4 * C4)) * log Y.
```

The interval has measure `epsilon * log Y`, so the large-value set occupies
the explicit fixed fraction

```text
c2^2 / (4 * C4 * epsilon).
```

In the original `x = exp y` variable, the large-value condition is

```text
abs (chebyshevPsi x - x)
  >
sqrt (c2 / (2 * epsilon)) * x^(re rho) / norm rho.
```

The Lean endpoint is
`exists_eventually_fixedProportion_largeNormalizedPsiError_of_fourthMoment`.
The hypothesis named `hExternalFourthMoment` is not proved elsewhere in this
repository and is not discharged by the endpoint.

## Why the existing fourth-moment module does not instantiate it

`MathlibAux.ExponentialPolynomialFourthMoment` proves a fourth-moment bound
for a finite exponential polynomial. A truncated explicit formula has the
schematic decomposition

```text
F_rho = finite zero polynomial + complementary zero contribution
        + contour remainder + truncation error.
```

The finite-polynomial theorem controls only the first term. To transfer its
bound to `F_rho`, one still needs a uniform estimate such as

```text
integral over the epsilon window of abs remainder(y)^4 = O(log Y),
```

with the same estimate for the complementary zero and truncation terms.
Pointwise convergence of a centered Gaussian contour remainder at each fixed
center does not imply this swept `L4` estimate. The current repository has no
uniform-integrability or domination theorem that closes this passage.

Consequently, applying the finite-polynomial fourth moment and silently
discarding the remainder would be invalid.

## Why current unconditional PNT bounds are too weak

The available elementary pointwise estimate has the normalized size

```text
abs F_rho(y)
  <= constant(rho) * exp ((1 - re rho) * y).
```

On the epsilon window this gives a fourth-moment coefficient growing roughly
like

```text
Y^(4 * (1 - re rho) * (1 + epsilon)),
```

not a constant `C4`. Combining that bound with the L2 lower bound produces a
large-value proportion tending to zero. It does not prove the fixed-proportion
input and cannot contradict the off-line zero.

The classical zero-free-region PNT error is also much larger than
`x^(re rho)` for a fixed `re rho < 1`, so it does not improve the normalized
fourth moment to `O(log Y)`.

## Why the Selberg modules do not supply the input

The repository's Selberg fourth-moment and Paley--Zygmund infrastructure is
attached to finite or mollified Dirichlet polynomials and Hardy `Z`-function
windows. Those theorems support critical-line zero counting. They do not bound
the fourth moment of `F_rho`, whose normalization depends on a hypothetical
off-line zeta zero.

No existing theorem identifies the Selberg polynomial with the true
prime-counting error with an `L4`-controlled remainder.

## Why fixed proportion still does not contradict Carlson

Carlson zero density bounds the number of distinct zeta zeros in a
right-half-plane region. The fixed-proportion theorem counts values of `y`
where the prime-counting error is large. It does not construct a new zeta zero
from such a value, and many large values may all be caused by the same
hypothetical zero.

Therefore there is currently no injective map

```text
separated large-value windows -> distinct zeta zeros,
```

and no Carlson contradiction.

## The single-pair obstruction

There is a sharper structural reason why a fixed-proportion large-value
theorem cannot by itself create new zeros.  If the target zero

```text
rho = beta + i gamma
```

has analytic multiplicity `m`, then the target zero and its conjugate
contribute schematically

```text
-m * exp (rho * y) / rho
-m * exp (conj rho * y) / conj rho
```

to the explicit formula at `x = exp y`.  After normalizing by
`norm rho * exp (-beta * y)`, this pair is exactly a phase shift of

```text
-2 * m * cos (gamma * y - arg rho).
```

Consequently, for every threshold `a` with

```text
0 < a < 2 * m,
```

the one-frequency model already has a positive asymptotic large-value
fraction.  On each complete period that fraction is

```text
(2 / pi) * arccos (a / (2 * m)).
```

In particular, a guaranteed amplitude strictly larger than `pi / 2` but
not larger than `2 * m` is fully compatible with a single conjugate zero
pair.  Neither the number of late logarithmic windows nor the measure of
large values in those windows forces any additional frequency or any
additional zeta zero.

This also identifies the threshold needed by any future amplification
argument.  It must do at least one of the following:

1. annihilate the known target pair and prove a nontrivial large-value
   theorem for the residual error;
2. force a normalized amplitude strictly beyond the full `2 * m`
   contribution of the target pair;
3. introduce an independent arithmetic restriction which the
   one-frequency model cannot satisfy.

The present missing-harmonic theorem supplies a strict improvement over
`pi / 2`; it does not supply any of these three stronger inputs.

## Exact routes to a contradiction

Any one of the following would advance beyond the present theorem:

1. Prove an unconditional upper bound saying that, for every
   `beta > 1 / 2`, the measure of the displayed large-value set is
   `o(log Y)`. This directly contradicts the fixed-proportion lower bound.
2. Prove the stronger unconditional second-moment estimate
   `integral F_rho^2 = o(log Y)`. This already contradicts PR #23 and is an
   RH-strength estimate.
3. Construct and prove injective a map from sufficiently separated
   large-value windows to distinct zeros in a fixed right half-plane, with
   growth exceeding Carlson's upper bound.
4. Derive a zero-density-weighted explicit-formula upper bound for the same
   local fourth moment whose constant is incompatible with the explicit
   lower-bound constant.

Only if such a contradiction excludes every nontrivial zero with real part
greater than `1 / 2` does functional-equation symmetry yield RH.

## Claim boundary

This branch proves:

- a reusable scaled Paley--Zygmund theorem with explicit constants;
- a fixed-proportion large-PNT-error theorem conditional on one off-line zero
  and a matching true-error fourth-moment upper bound;
- the exact analytic input needed to remove the fourth-moment condition.

It does not prove:

- the required true-error fourth-moment upper bound;
- an unconditional fixed-proportion result;
- a zero-density contradiction;
- exclusion of any off-line zero;
- the Riemann Hypothesis.
