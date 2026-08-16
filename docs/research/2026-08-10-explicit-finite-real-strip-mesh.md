# Explicit finite real-strip mesh

## Purpose

The dynamic real-part envelope is continuous, but the actual Carlson theorem
is applied to finitely many strips.  This note gives a Lean-friendly equal
mesh of `[1/2,1]`, proves its exact coverage, and records the finite-strip
exponent loss.

The mesh depends on the fixed target zero and interval parameters, but not on
`X`.  Therefore summing over the strips changes only the multiplicative
constant and introduces no new power or logarithmic loss.

## Mesh data

Fix

```text
0 < deltaTarget.
```

Define

```text
N := ceil (1 / (2 * deltaTarget)),
w := 1 / (2 * N).
```

Here `ceil` is converted to a positive natural number.  Since
`deltaTarget > 0`,

```text
1 <= N,
0 < w,
w <= deltaTarget.
```

For `k = 0,...,N`, define the endpoints

```text
sigma(k) := 1/2 + k / (2*N).
```

For `k = 0,...,N-1`, define

```text
sigmaL(k) := sigma(k),
sigmaR(k) := sigma(k+1),
Strip(k)  := Set.Ioc (sigmaL(k)) (sigmaR(k)).
```

The first strip may be changed to `Icc` if the line `Re rho = 1/2` must be
included explicitly.  Since the zeta zero set on the critical line is handled
with analytic multiplicity, the endpoint convention must be fixed once and
used in both the shell mass and explicit zero partition.

The exact identities are

```text
sigma(0) = 1/2,
sigma(N) = 1,
sigmaR(k) - sigmaL(k) = w.
```

## Exact coverage and disjointness

With a consistent half-open convention,

```text
Set.Ioc (1/2) 1
  = union k : Fin N, Strip(k).
```

The strips are pairwise disjoint.  If the critical line is included in the
zero sum, use

```text
Set.Icc (1/2) 1
  = {1/2} union union k : Fin N, Strip(k),
```

or make only the first strip left-closed.

The proof should use the Archimedean floor/ceiling property for

```text
2*N*(sigma - 1/2)
```

and treat `sigma = 1` separately so that a floor value `N` is not coerced into
`Fin N`.

No zero may occur in two strips, and every zero in the declared real range
must occur in exactly one strip.

## Direct-L2 target width

Let the infinitesimal direct-L2 envelope satisfy

```text
Phi(sigma) <= -r
```

for every `sigma in [1/2,1]`, with

```text
0 < r,
1 < lambda.
```

The actual strip exponent is

```text
EStrip(k)
  := 2 * kappa_lambda(sigmaR(k) - beta)
       + gamma * (q(sigmaL(k)) - 2).
```

Compare it with the envelope at `sigmaL(k)`:

```text
Phi(sigmaL(k))
  = 2 * kappa_lambda(sigmaL(k) - beta)
      + gamma * (q(sigmaL(k)) - 2).
```

Because `kappa_lambda` is `lambda`-Lipschitz,

```text
EStrip(k)
  <= Phi(sigmaL(k)) + 2 * lambda * w
  <= -r + 2 * lambda * w.
```

Choose

```text
deltaTarget := r / (4 * lambda).
```

Then an equivalent explicit strip count is

```text
N := ceil (2 * lambda / r).
```

and

```text
w <= r / (4 * lambda).
```

Therefore every finite strip has the uniform strict exponent

```text
EStrip(k) <= -r / 2 < 0.
```

This is the finite dynamic-layer theorem consumed by the actual dyadic shell
energy bound.

## Polynomial and logarithmic ledger

For each strip and signed shell, the weighted direct-L2 estimate has the form

```text
Energy(k,sign)
  <= C(k,sign)
       * X^(-r/2)
       * (1 + log X)^5.
```

The number of real strips is `N`, and the number of signs is two.  Hence

```text
sum k,sign, Energy(k,sign)
  <= 2 * N * Cmax
       * X^(-r/2)
       * (1 + log X)^5.
```

Because `N` is independent of `X`, it is part of the explicit constant.  The
logarithmic loss remains exactly five.

After reserving half the polynomial margin to absorb the fixed log power,

```text
total middle energy = O(X^(-r/4)),
total middle RMS    = O(X^(-r/8)).
```

Neither the finite strip count nor the two signs changes these exponents.

## Critical equality

If the infinitesimal envelope has only

```text
Phi(sigma) <= 0
```

with equality at some point, finite discretization cannot improve it.  The
strip upper endpoint may instead add a positive amount `2*lambda*w`, and the
remaining `(log X)^5` grows.

Therefore:

- strict infinitesimal margin is required before constructing the mesh;
- equality is a critical obstruction, not decay;
- refining the mesh cannot convert a zero margin into a negative exponent.

## Shared L1/L2 mesh

If the same partition must also satisfy an `L1` envelope with margin `m1>0`,
the finite-strip cost is at most

```text
lambda * w.
```

Use

```text
deltaShared
  := min (m1 / (2*lambda)) (r / (4*lambda)),

NShared
  := ceil (1 / (2*deltaShared)).
```

Then every strip satisfies

```text
L1StripExponent <= -m1/2,
L2StripExponent <= -r/2.
```

This shared construction is optional.  The direct-L2 middle-tail route only
needs the `r/(4*lambda)` mesh and remains feasible for every `beta>1/2`.

## Actual zero partition interface

For a fixed signed dyadic shell, define

```text
ZeroStrip(k)
  := {rho |
       rho is a nontrivial zeta zero,
       sigmaL(k) < Re rho <= sigmaR(k),
       T <= sign * Im rho < 2*T}.
```

The production partition theorem should state:

```text
zeroShell
  = disjoint union k, ZeroStrip(k)
```

over the declared real range.  Analytic multiplicity is a weight on this set,
not part of the partition index.

Deleting a finite retained set `S` commutes with the partition:

```text
(zeroShell \ S) intersect Strip(k)
  = ZeroStrip(k) \ S.
```

All strip masses and weighted row masses decrease by nonnegative monotonicity.

## Proposed theorem chain

```text
realStripCount
one_le_realStripCount
realStripWidth
realStripWidth_pos
realStripWidth_le_target
realStripEndpoint
realStripEndpoint_zero
realStripEndpoint_last
realStripEndpoint_strictMono
realStrip_width_eq
exists_unique_realStrip
realStrips_pairwiseDisjoint
realStrips_iUnion_eq
directL2RealStripCount
directL2RealStripWidth_le
directL2FiniteStripExponent_le
directL2FiniteStripExponent_neg
directL2FiniteStripsEnergy_le
zeroShell_eq_disjointUnion_realStrips
zeroShellDelete_eq_disjointUnion_realStrips
```

Names are provisional.

## Audit rules

- Use a positive natural strip count.
- State the endpoint convention explicitly.
- Prove exact coverage and pairwise disjointness.
- Keep analytic multiplicity as a weight.
- Keep `N` independent of `X`.
- Charge no new logarithm for the finite strip count.
- Require a strict envelope margin before discretization.
- Preserve finite deletion by set algebra and nonnegative monotonicity.
- Do not import Sharp or half-isolated lower-bound modules.
