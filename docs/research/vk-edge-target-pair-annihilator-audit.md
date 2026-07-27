# VK-edge target-pair annihilator audit

## Scope

This branch tests whether a local prime-error signal remains after removing
the contribution of one selected zeta zero and its conjugate.  It formalizes
the detector algebra and the residual-energy transfer.  It does not assume or
prove that the remaining signal has positive energy.

For a real function `F`, step `h`, and selected ordinate `gamma`, define

```text
D_(h,gamma) F(y)
  = F(y+h) - 2 cos(gamma h) F(y) + F(y-h).
```

## Exact spectral action

For the real cosine package

```text
P_(m,lambda,phase)(y) = -2 m cos(lambda y - phase),
```

Lean proves

```text
D_(h,gamma) P_(m,lambda,phase)
  = 2 (cos(lambda h) - cos(gamma h))
      P_(m,lambda,phase).
```

The selected pair `lambda = gamma` is therefore annihilated pointwise.
At a point where the second cosine package is nonzero, it is also annihilated
if and only if

```text
cos(lambda h) = cos(gamma h).
```

Thus distinct ordinates are not automatically distinguishable for one fixed
step.  A later spectral converse must choose `h` outside finitely many
collision sets or average over `h`.

## Exact classical-prime identity

Let

```text
E(x) = chebyshevPsi(x) - x
rho = beta + i gamma.
```

The selected-pair-annihilated normalized PNT error is exactly

```text
norm rho * exp(-beta y) *
  ( exp(-beta h) E(exp(y+h))
    - 2 cos(gamma h) E(exp y)
    + exp(beta h) E(exp(y-h)) ).
```

It is also exactly the detector applied to
`normalizedPsiResidual rho`, the normalized error after subtracting the
selected conjugate pair.

This three-scale prime correlation is the arithmetic quantity that must be
bounded from below.  The existing lower bound for the unfiltered normalized
PNT error cannot supply such a bound because the selected pair alone can
account for that signal.

## Explicit local energy transfer

The detector satisfies the pointwise estimate

```text
|D_(h,gamma) F(y)|^2
  <= 12 (|F(y+h)|^2 + |F(y)|^2 + |F(y-h)|^2).
```

Consequently, if each shifted residual energy on a measurable set is at most
`E`, then

```text
integral |D_(h,gamma) residual|^2 <= 36 E.
```

Contrapositively, a detector lower bound `L` would force at least one of the
three shifted residual energies to be at least `L / 36`.  The theorem is a
transfer mechanism, not a source of the lower bound `L`.

## Formal no-go result

For every positive constant `C` and every nonempty interval,

```text
not (C * interval_length
  <= integral |D_(h,gamma) P_(m,gamma,phase)|^2).
```

The right-hand side is exactly zero.  Therefore the selected zero alone
cannot imply positive annihilated energy.  Any positive lower bound must use
additional arithmetic information about the true prime error.

## Remaining mathematical gate

The missing theorem has to lower-bound the true three-scale correlation,
uniformly on sufficiently late logarithmic windows, after selecting or
averaging the step `h` to avoid frequency collisions.  A useful endpoint
would have the form

```text
integral_window
  |annihilatedNormalizedPsiError rho h y|^2 dy
    >= c_rho * window_length
```

with `c_rho > 0`, together with a spectral converse assigning that energy to
a zero contribution distinct from the selected pair.

Only after those two facts are proved can the existing deduplicated
zero-layer and Carlson machinery be applied.

## Claim boundary

This branch proves:

- exact annihilation of one selected conjugate zero pair;
- exact multipliers for all cosine frequencies;
- the exact three-scale formula for the classical PNT error;
- an explicit local residual-energy transfer with constant `36`;
- pure-pair and frequency-collision no-go theorems.

It does not prove:

- a positive annihilated prime-error lower bound;
- the existence of an additional zeta zero;
- expanding or disjoint zero layers;
- a Carlson zero-density contradiction;
- the Riemann hypothesis.
