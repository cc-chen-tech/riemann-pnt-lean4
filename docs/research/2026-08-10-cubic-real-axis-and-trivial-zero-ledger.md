# Real-axis and trivial-zero ledger for the cubic transfer

## Purpose

The direct-L2 Carlson argument controls nontrivial-zero blocks.  A complete
explicit-formula transfer also contains:

- the pole at `s = 1`;
- the higher-order residue at `s = 0` created by the cubic Perron denominator;
- the trivial zeros at negative even integers;
- the outer contour.

These terms have different mechanisms and must not be hidden inside a generic
"small remainder" assumption.

## Pole at s = 1

The pole residue supplies the continuous main term.  Before centered
differencing it is proportional to

```text
x.
```

After centered logarithmic second difference,

```text
Q_main(x,h)
  = x * (exp(h) - 2 + exp(-h)) / h^2
  = x * C_h(1).
```

This is exactly the triangle average of the continuous main function:

```text
Q_main(x,h)
  = integral_{-1}^1
      (1 - |u|) * x*exp(h*u) du.
```

It must be subtracted before point extraction.  Comparing `Q_main` with either
endpoint main term creates the unwanted `O(x*h)` desmoothing error described in
the exact-triangle note.

## Residue at s = 0

The third-order Perron denominator contains `s^3`.  Since the logarithmic
derivative of the classical zeta function is regular at `s = 0`, its residue
there is a polynomial in

```text
t = log x
```

of degree at most two:

```text
P0(t) = a0 + a1*t + a2*t^2.
```

The centered second difference is exact:

```text
(P0(t+h) - 2*P0(t) + P0(t-h)) / h^2
  = 2*a2.
```

Thus the `s = 0` contribution is bounded independently of `x` and `h`, once
the zeta-specific coefficients are fixed.  Relative to the target amplitude,

```text
x^beta / |rho0|,
```

it is `O(x^(-beta))` up to a fixed target-zero constant and therefore tends to
zero for `beta > 0`.

The production proof must derive the actual polynomial and coefficient bound
from the existing cubic residue theorem.  The degree statement should not be
replaced by an unspecified residual function.

## Trivial zeros

For a trivial zero

```text
s = -2*n,
n >= 1,
```

the centered cubic zero contribution has the shape

```text
x^(-2*n) / (-2*n) * C_h(-2*n).
```

For negative real `s`, the low-frequency bound used in the critical strip is
not uniform in `n`, because `exp(-h*s)` grows.  Use the numerator estimate
directly:

```text
|C_h(-2*n)|
  <= C * exp(2*n*h) / (h^2 * n^2).
```

Consequently

```text
|x^(-2*n) / (-2*n) * C_h(-2*n)|
  <= C' / h^2
     * (exp(h)/x)^(2*n) / n^3.
```

If

```text
x * exp(-h) >= 2,
```

the ratio `exp(h)/x` is at most `1/2`, and the series is bounded by

```text
C_triv * h^(-2) * x^(-2) * exp(2*h).
```

With

```text
h = x^(-d),
```

this has polynomial size

```text
x^(2*d - 2).
```

After target-amplitude normalization the exponent is

```text
2*d - 2 - beta,
```

which is strictly negative for the proposed `0 < d < 1/8` and
`beta > 2/3`.  This decay is much stronger than the Carlson middle-zero
margin and introduces no logarithmic loss.

## Pole-subtraction and elementary terms

Any remaining elementary explicit-formula term must be classified by its
dependence on `t = log x`:

```text
constant or affine in t:
  centered second difference is zero;

quadratic in t:
  centered second difference is constant;

bounded analytic term with two derivatives:
  bounded by its second derivative on [t-h,t+h].
```

The theorem should expose a concrete bound for each actual term.  A generic
assumption `realAxisRemainder -> 0` would recreate the abstract-kernel problem
that the cubic actual-zeta route is intended to remove.

## Outer contour

The contour contribution is logically separate.  The centered second
difference of the third-order integrand supplies the second-order multiplier,
leading to a bound of the schematic form

```text
C_contour
  * x * (1 + log x)^k
  / (h^2 * H^2).
```

At the right endpoint `x <= Y^lambda`, after normalization by the target
amplitude and with

```text
h = Y^(-d),
H = Y^alpha,
g = lambda*(1-beta),
```

the polynomial exponent is

```text
g + 2*d - 2*alpha.
```

For

```text
alpha = (1+g)/2,
d = (1-g)/8,
```

it equals

```text
-(3+g)/4 < 0.
```

Unlike the real-axis and trivial-zero pieces, this bound requires the actual
good-height contour theorem and its logarithmic constants.

## Complete normalized remainder decomposition

After removal of the finite low-zero main cluster, the smoothed error should be
written as

```text
Q_E
  = M_low
    + R_middleZeros
    + R_highOrContour
    + R_zeroResidue
    + R_trivialZeros.
```

The normalized losses are:

```text
M_low:
  strict lower-energy constant;

R_middleZeros:
  Carlson square multiplicity * Occupancy,
  exponent from the direct-L2 numerical core,
  log loss 5+r;

R_highOrContour:
  exponent g+2*d-2*alpha,
  explicit contour log loss;

R_zeroResidue:
  exponent -beta,
  no asymptotic log loss after centered differencing;

R_trivialZeros:
  exponent 2*d-2-beta,
  no asymptotic log loss.
```

Every exponent in the final facade should appear as a named field or theorem,
not be folded into a single opaque `remainderSmall` hypothesis.

## Lean-facing theorem chain

The real-axis slice should expose equivalents of:

```text
centeredDifference_quadraticPolynomial
cubicZeroResidue_centeredDifference_bound
centeredCubic_trivialZero_abs_le
summable_centeredCubic_trivialZeros
trivialZeroTail_le_hInvSq_mul_xInvSq
normalized_zeroResidue_tendsto_zero
normalized_trivialZeroTail_tendsto_zero
completeCubicRemainder_decomposition
```

The actual coefficients and existing residue names must be obtained from the
current production cubic explicit-formula modules before implementation.

## Nonclaims

This ledger does not claim:

- that the current cubic residue at `s = 0` has already been normalized into
  the displayed polynomial;
- that the trivial-zero sum is currently exposed as a separate production
  object;
- that the contour bound has already been proved with the required
  `h^(-2)*H^(-2)` dependence;
- that controlling these terms closes the Carlson middle-zero L2 tail;
- that the final point witness or its sign has been established.
