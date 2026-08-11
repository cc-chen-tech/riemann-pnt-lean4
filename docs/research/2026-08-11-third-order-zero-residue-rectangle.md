# Explicit zero residue on the contour rectangle

This slice specializes the coefficient identification from the local
third-order Laurent expansion to the actual negative-left-edge contour
rectangle.

For `a < 0 < c` and `W > 0`, the closed rectangle

```text
uIcc a c x uIcc (-W) W
```

is a neighborhood of zero because it contains the open rectangle
`Ioo a c x Ioo (-W) W`. This supplies the punctured neighborhood required by
Laurent coefficient uniqueness.

The resulting boundary-residue theorem retains the established finite pole
set, multiplicities, cubic zero-pole coefficient, and boundary integral
identity, while additionally stating

```text
residue 0 = iteratedDeriv 2 (thirdOrderZeroCore x) 0 / 2.
```

No Omega theorem, RH consequence, or new zero-free region is claimed.
