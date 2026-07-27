# VK-edge cosine-model annihilator audit

## Scope

This branch formalizes a symmetric finite-difference detector and applies it
to the normalized prime-number-theorem error. The detector is first developed
for a cosine model. The companion module
`PrimeNumberTheorem.VKEdgeExplicitFormulaPairBridge` then proves that, when
`rho` is a positive-ordinate nontrivial zeta zero, this model is exactly the
normalized multiplicity-weighted residue contribution of `rho` and its
complex conjugate.

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

At the model layer, the definition

```text
normalizedPsiModelResidual rho
  = normalizedPsiError rho - normalizedCosineModelPair rho
```

is a formal subtraction. Linearity and model annihilation give

```text
annihilatedNormalizedPsiError rho h
  = D_(h,rho.im) (normalizedPsiModelResidual rho).
```

For a positive-ordinate nontrivial zeta zero and a finite height cutoff
containing it, the explicit-formula bridge proves that this formal residual
is exactly the normalized finite-height expression consisting of:

1. the `psi - psi0` jump correction;
2. all finite-height nontrivial-zero residues except `rho` and `conj rho`;
3. the closed-form explicit-formula terms;
4. the finite-height explicit-formula approximation error.

This is an exact identity. It is not an estimate for any of those four
components.

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

The exact explicit-formula identification is now proved. What remains is
quantitative: one must control the other finite zeros, the `psi - psi0`
correction, the closed-form terms, and the finite-height approximation error
strongly enough to prove a positive detector-energy lower bound.

This branch does not provide that positive detector-energy premise.

## Claim boundary

This branch proves:

- exact finite-difference action on a cosine model;
- exact annihilation of the tuned model frequency;
- exact identification of the cosine model with the genuine
  multiplicity-weighted residues of a nontrivial zero and its conjugate;
- exact identification of the model residual with the corresponding
  finite-height explicit-formula residual;
- an exact three-scale identity for the real PNT error;
- integral detector stability;
- positive inner detector energy implies a pointwise model-residual lower
  bound on the expanded interval;
- pure-model and frequency-collision no-go theorems.

It does not prove:

- a quantitative bound for the explicit-formula residual components;
- positive detector energy for the zeta/PNT signal;
- another zeta zero or a zero-density contradiction;
- an unconditional PNT oscillation theorem;
- the Riemann hypothesis.
