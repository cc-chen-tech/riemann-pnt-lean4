# VK-edge finite-spectrum gap: proof record

## Current mathematical status

This record proves an abstract finite-spectrum theorem. The separate
Mellin--Abel transfer in `vk-edge-pi-over-two-abel-transfer.md` applies it to
a global zeta/PNT `limsup`, modulo Bellotti's stated theorem. The
finite-pole argument in `vk-edge-pi-over-two-localized-transfer.md` proves
the power-interval transfer, and
`vk-edge-pi-over-two-carlson-transfer.md` combines it with Carlson
zero-density to cover every fixed zeta zero with real part greater than
`1/2`. Novelty relative to the harmonic-analysis and oscillation literature
has not been established.

The central preregistered finite-spectrum gate has an affirmative answer:

> For every fixed positive integer `M`, there is an explicit
> `delta_M > 0` such that every admissible polynomial in `E_M` has sup norm at
> least `pi / 2 + delta_M`.

The proof uses a missing odd harmonic of `sign(cos)`. It avoids compactness and
is uniform over rational relations, irrational frequencies, near collisions,
and arbitrarily large frequencies.

## Setup on the frequency-flow compact group

Let

```text
F(y) = 2 Re(sum_{j=0}^{r-1} a_j exp(i lambda_j y))
```

be admissible in the sense of
`vk-edge-pi-over-two-preregistration.md`. Thus:

```text
1 <= r <= M,
lambda_0 = 1,
a_0 = 1,
lambda_j > 0,
```

and the positive frequencies are pairwise distinct.

Let `G` be the closure in the `r`-torus of

```text
y |-> (exp(i lambda_0 y), ..., exp(i lambda_(r-1) y)).
```

Write `chi_j` for the restriction to `G` of the `j`th coordinate character.
The function `F` extends continuously to

```text
F_G(z) = 2 Re(sum_j a_j chi_j(z)).
```

The real line is dense in `G`, so

```text
sup_{y in R} |F(y)| = ||F_G||_infinity.
```

Let `mu` be normalized Haar measure on `G`. The distinguished character
`chi_0` has infinite order, and its pushforward of `mu` is normalized Haar
measure on the circle. Distinct positive real frequencies give distinct
characters on `G`; no inverse `chi_j^(-1)` can equal a positive power of
`chi_0`.

For a function `h` on `G`, use the convention

```text
hat h(chi) = integral_G h conjugate(chi) dmu.
```

The normalization gives

```text
hat F_G(chi_0) = 1.
```

## The explicit fixed-M gap

Put

```text
K = ||F_G||_infinity,
f = F_G / K,
u = Re(chi_0),
s = sign(u).
```

The set `u = 0` has Haar measure zero, so the value assigned to `s` there is
irrelevant. We have `|f| <= 1` and

```text
integral_G f u dmu = 1 / K.
```

Since `s u = |u|` and the circle average of `|cos|` is `2 / pi`, define the
nonnegative equality defect

```text
D
  = integral_G |u| |s - f| dmu
  = integral_G |u| (1 - s f) dmu
  = 2 / pi - 1 / K.                         (1)
```

The first equality uses `|s-f| = 1-sf`, valid because `s` is `+1` or `-1`
and `f` is real with `|f| <= 1`.

Consider the `M+1` distinct characters

```text
chi_0, chi_0^3, ..., chi_0^(2M+1).
```

The positive-frequency support of `f` contains at most `M` characters.
Negative-frequency characters cannot equal any positive odd power of
`chi_0`. Hence there is an odd integer `n`, with

```text
1 <= n <= 2M+1,
```

for which

```text
hat f(chi_0^n) = 0.
```

The Fourier series of `sign(cos)` gives

```text
|hat s(chi_0^n)| = 2 / (pi n).
```

Therefore, with

```text
E = integral_G |s-f| dmu,
b_M = 2 / (pi (2M+1)),
```

we have

```text
E
  >= |hat(s-f)(chi_0^n)|
  = 2 / (pi n)
  >= b_M.                                    (2)
```

For any `0 < eta < 1`, split `G` according to `|u| >= eta`. Equation (1),
the bound `|s-f| <= 2`, and the circle measure

```text
mu {|u| < eta} = (2 / pi) arcsin(eta)
```

give

```text
E <= D / eta + (4 / pi) arcsin(eta).         (3)
```

Choose

```text
eta_M = sin(pi b_M / 8)
      = sin(1 / (4(2M+1))).
```

Then the second term in (3) is exactly `b_M / 2`. Combining (2) and (3)
yields

```text
D >= d_M,

d_M
  = b_M eta_M / 2
  = sin(1 / (4(2M+1))) / (pi (2M+1)).        (4)
```

Equations (1) and (4) imply

```text
K >= L_M,

L_M
  = 1 / (2/pi - d_M)
  > pi / 2.
```

Thus one explicit admissible gap is

```text
delta_M = L_M - pi / 2 > 0.                  (5)
```

This proves the preregistered Gate F1. The bound is not asserted to be sharp.
As `M` grows it is of order `M^(-2)`.

## Exact solution for M = 1

For `M=1`,

```text
F(y) = 2 cos y,
```

so

```text
kappa_1 = 2.
```

## Exact solution for M = 2

The diagnostic search suggests, and the following argument proves,

```text
kappa_2 = sqrt(3).                            (6)
```

Write the second frequency as `lambda` and its coefficient as `a`.

### Irrational frequency ratio

If `lambda` is irrational, the flow

```text
y |-> (exp(iy), exp(i lambda y))
```

is dense in the two-torus. The two phases can therefore align independently,
and

```text
||F||_infinity = 2 (1 + |a|) >= 2 > sqrt(3).
```

### Nonintegral rational ratio

Let `lambda=p/q` in lowest terms with `q>1`. Put `y=qt` and average

```text
F(q(t+2pi k/q)),  k=0,...,q-1.
```

The distinguished term is unchanged by this averaging, while the second term
vanishes because `p` is coprime to `q`. The average is exactly

```text
2 cos(qt).
```

At `t=0`, the average equals `2`, so at least one summand has absolute value at
least `2`. Hence every nonintegral rational ratio has norm at least `2`.

### Integral ratio away from cubic resonance

It remains to take `lambda=p` with an integer `p>1`. On writing `z=exp(iy)`,

```text
F = z + z^(-1) + a z^p + conjugate(a) z^(-p).
```

Put `v = |a|^2`. Circle orthogonality gives

```text
mean(F^2) = 2 (1+v).
```

If `p != 3`, there is no fourth-moment resonance, and

```text
mean(F^4) = 6 + 24v + 6v^2.
```

Since `F^4 <= ||F||_infinity^2 F^2`,

```text
||F||_infinity^2
  >= mean(F^4) / mean(F^2)
  = 3 (1+4v+v^2) / (1+v)
  >= 3.
```

Thus `||F||_infinity >= sqrt(3)`.

### Resonance p = 3

Write `a=b+ic`. Then

```text
F(t)
  = A(t) + B(t),
A(t)
  = 2 cos t + 2b cos 3t,
B(t)
  = -2c sin 3t.
```

The function `A` is even and `B` is odd. Hence

```text
max(|F(t)|, |F(-t)|)
  = max(|A(t)+B(t)|, |A(t)-B(t)|)
  >= |A(t)|.
```

At `t=pi/6`, `cos(3t)=0`, so for every real `b`,

```text
|A(pi/6)| = sqrt(3).
```

Therefore `||F||_infinity >= sqrt(3)`. Equality is attained at

```text
a = -1/6.
```

Indeed, with `x=cos t`,

```text
F(t) = 3x - (4/3)x^3.
```

Its interior extrema occur at `x=+-sqrt(3)/2` and have values `+-sqrt(3)`;
the endpoint values are `+-5/3`. Thus its sup norm is exactly `sqrt(3)`.

Together the cases prove (6).

## There is no gap uniform in M

The fixed-`M` dependence is essential. Let `s(y)=sign(cos y)` and take its
Fejer mean of degree `2M-1`. This is a real trigonometric polynomial with
exactly the positive odd frequencies

```text
1, 3, ..., 2M-1
```

and norm at most `1`, because Fejer convolution is a positive contraction on
`L-infinity`. Its complex Fourier coefficient at frequency `1` is

```text
(2/pi) (1 - 1/(2M))
  = (2M-1)/(pi M).
```

After multiplying by `pi M/(2M-1)`, the distinguished coefficient is `1`.
Consequently,

```text
kappa_M <= pi M/(2M-1),
```

which tends to `pi/2`. Thus no positive `delta` can work simultaneously for
all finite term budgets.

## What is and is not closed

Closed:

1. `kappa_M > pi/2` for every fixed `M`, with the explicit bound (5).
2. `kappa_1 = 2`.
3. `kappa_2 = sqrt(3)`.
4. The Bellotti count to missing-odd-harmonic mapping for a global `limsup`.
5. A zeta/PNT global absolute-`limsup` constant strictly above `pi/2`,
   modulo Bellotti's stated zero-density theorem.
6. Occurrence in every sufficiently late interval `[Y,Y^7]`, using fixed
   finite-pole annihilating multipliers and Revesz's standard simultaneous
   contour lemmas.
7. The Carlson `o(T)` count to missing-odd-harmonic mapping for every fixed
   right-hand zeta zero.

Not closed:

1. Whether the abstract fixed-`M` inequality or the displayed constants are
   new in harmonic analysis.
2. Historical priority for the Bellotti-plus-missing-harmonic global and
   localized theorems.
3. External specialist review and formal Lean verification of the analytic
   transfer.

The detailed transfers are recorded separately in
`vk-edge-pi-over-two-abel-transfer.md` and
`vk-edge-pi-over-two-localized-transfer.md`, with the Carlson specialization
in `vk-edge-pi-over-two-carlson-transfer.md`. This proof record itself still
covers only the abstract Fourier gate.
