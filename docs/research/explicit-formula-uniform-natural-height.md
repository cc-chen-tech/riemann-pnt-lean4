# One good height for all natural samples

The cofinal contour machinery already selects one good height `T` in every
unit interval `[A, A + 1]` and proves a uniform finite-trivial-zero formula
for all natural samples `m >= 3`.

This milestone removes the finite trivial-zero cutoff without changing `T`.
For each `m`, the cutoff index may be chosen separately because both the left
edge and the finite trivial-zero tail converge while the selected contour
height stays fixed.

The intended endpoint is

```text
exists C >= 0, forall A >= 8,
  exists T in [A, A + 1], goodHeight T and
  forall natural m >= 3,
    norm (explicitFormulaApproxWithMultiplicity m T - psi0 m)
      <= C * m * (log(m)^2 + log(A)^2) / T.
```

This is still a natural-point theorem.  Moving it to every real point uses
`ExplicitFormulaSpatialVariation` and separate midpoint-jump control.
