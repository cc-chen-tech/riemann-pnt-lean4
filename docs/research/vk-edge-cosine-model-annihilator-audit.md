# VK-edge cosine-model annihilator audit

## Scope

This branch formalizes a symmetric finite-difference detector and applies it
to the normalized prime-number-theorem error. The frequency and amplitude
parameters are taken from a complex number `rho`, but the cosine term remains
a model: this branch does not prove that it is the contribution of a zeta zero
in an explicit formula.

For a real function `F`, step `h`, and frequency `gamma`, define

```text
D_(h,gamma) F(y)
  = F(y+h) - 2 cos(gamma h) F(y) + F(y-h).
```

## Exact model action

For

```text
P_(m,lambda,phase)(y) = -2 m cos(lambda y - phase),
```

Lean proves

```text
D_(h,gamma) P_(m,lambda,phase)
  = 2 (cos(lambda h) - cos(gamma h))
      P_(m,lambda,phase).
```

The model with `lambda = gamma` is therefore annihilated pointwise. A second
frequency can also be annihilated when

```text
cos(lambda h) = cos(gamma h).
```

Thus a fixed detector step does not automatically separate distinct
frequencies.

## Arithmetic identity and interpretation boundary

The definition

```text
normalizedPsiModelResidual rho
  = normalizedPsiError rho - normalizedCosineModelPair rho
```

is a formal subtraction. Linearity and model annihilation give

```text
annihilatedNormalizedPsiError rho h
  = D_(h,rho.im) (normalizedPsiModelResidual rho).
```

This is a definitional model identity, not a zeta explicit-formula
decomposition. In particular, the right side is not proved to equal the sum
of other zeta zeros and contour remainders.

Independently, the detector on the actual normalized PNT error has the exact
three-scale arithmetic form

```text
norm rho * exp(-rho.re * y) *
  ( exp(-rho.re * h) * E(exp(y+h))
    - 2 cos(rho.im * h) * E(exp y)
    + exp(rho.re * h) * E(exp(y-h)) ),
```

where `E(x) = chebyshevPsi(x) - x`.

## Energy transfer

The pointwise estimate

```text
|D_(h,gamma) F(y)|^2
  <= 12 (|F(y+h)|^2 + |F(y)|^2 + |F(y-h)|^2)
```

implies the existing `36 E` integral stability bound.

This branch now also proves the missing inner-to-outer pointwise bridge. If
`a < b` and

```text
I = integral_[a,b] |D_(h,gamma) F(y)|^2 dy > 0,
```

then some

```text
z in [a - |h|, b + |h|]
```

satisfies

```text
F(z)^2 > I / (72 * (b - a)).
```

Specializing `F` to `normalizedPsiModelResidual rho` yields the corresponding
model-residual statement. The factor `72` comes from applying the pointwise
detector bound against half of the positive inner energy.

## No-go result

The detector energy of the pure tuned cosine model is exactly zero. Therefore
the model alone cannot provide a positive detector-energy lower bound.

## Remaining mathematical gate

To turn this module into a theorem about actual zeta-zero contributions, one
still needs a proved explicit-formula identification showing that the chosen
cosine model is the target conjugate-zero term, with correct phase,
multiplicity, and normalization, and that the formal residual contains the
remaining zero and contour terms with controlled errors.

This branch does not provide the positive detector-energy premise either.

## Claim boundary

This branch proves:

- exact finite-difference action on a cosine model;
- exact annihilation of the tuned model frequency;
- an exact three-scale identity for the real PNT error;
- integral detector stability;
- positive inner detector energy implies a pointwise model-residual lower
  bound on the expanded interval;
- pure-model and frequency-collision no-go theorems.

It does not prove:

- an explicit-formula identification of the model;
- positive detector energy for the zeta/PNT signal;
- another zeta zero or a zero-density contradiction;
- an unconditional PNT oscillation theorem;
- the Riemann hypothesis.
