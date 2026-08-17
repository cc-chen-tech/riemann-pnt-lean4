# A height-independent localization exponent for sharp oscillation caused by a Vinogradov--Korobov-edge zero (manuscript)

## Status

This is the conventional theorem--lemma--proof manuscript form of
`vk-edge-zero-oscillation-paper-gates.md`.  It records a paper-level
argument, conditional on two cited external theorems.  No Lean theorem is
added by this note.  Priority and external review remain open: this
manuscript must not be cited as an established new theorem until the checks
listed in the final section are completed.

## Notation

Write

```text
g(t) = (log t)^(-2/3) (log log t)^(-1/3)
```

for the Vinogradov--Korobov scale, and let `A_0` be a constant for which the
asymptotic Vinogradov--Korobov zero-free region reads

```text
beta >= 1 - A_0 g(|gamma|).
```

`N(sigma, T)` counts the nontrivial zeros `rho = beta + i gamma` of the
Riemann zeta function with `beta >= sigma` and `0 < gamma <= T`, with
analytic multiplicity.

### External input 1 (Bellotti edge count)

**Bellotti (2025), Theorem 1.2** [*A new zero-density estimate for the
Riemann zeta function and the error term in the Prime Number Theorem*,
Bull. London Math. Soc.; arXiv:2508.02041].  Consequence used here:

> For every fixed `B > A_0` there are constants `T_B` and `M_B`, with `M_B`
> independent of `T` and `sigma`, such that
>
> ```text
> T >= T_B  and  sigma >= 1 - B g(T)
>   implies  N(sigma, T) <= M_B.
> ```

Zeros are understood with analytic multiplicity.

### External input 2 (Revesz residue polynomial)

**Revesz (2023), Theorem 6** [*Oscillation of the remainder term in the
prime number theorem of Beurling, caused by a given zeta-zero*, IMRN 2023;
arXiv:2202.01837].  The proof below uses the following components of
Revesz's proof verbatim:

* the shifted-contour construction with parameters

  ```text
  H = log Y,  m >= H,  M = 16 m,  mu = 12 m,
  q = exp(4 m),  Q = exp(28 m);
  ```

* the residue polynomial

  ```text
  P(m) =
    sum_{|Im rho - gamma_0| < 5}
      exp(m (rho - rho_0)^2 + 16 m (rho - rho_0))
    + conjugate terms,
  ```

  where the sum runs over the zeros selected by the shifted contour, with
  multiplicity; the terms belonging to `rho_0` and to its conjugate are both
  exactly `1`;

* the two evaluations of the weighted integral, giving the lower bound via
  `P(m)` and the upper bound

  ```text
  |S(m)| <= (4 K |rho_0| / pi) (1 + 4 / (sqrt(m) gamma_0)) + 4 exp(-2 m),
  ```

  where

  ```text
  K = sup_{Y <= x <= Y^C_A} |psi(x) - x| / x^beta_0;
  ```

* the modified Cassels power-sum theorem: for a nonzero Laurent polynomial
  with `R` terms, at least one of which has coefficient at least `1`, some
  integer `m` in `[H, (R+1) H]` attains value at least `1` in modulus at the
  doubling step; in the form used below, with `R` pure-power terms and two
  terms of size exactly `1`, some `m` in `[H, (2R+1) H]` has `|P_high(m)| >= 2`.

For a fixed zero

```text
rho_0 = beta_0 + i gamma_0,
```

the positive-ordinate part of `P` is the displayed sum; the conjugate copy
is adjoined with conjugate coefficients.

## Theorem

Fix `A > A_0`.  There exist constants `Gamma_A` and `C_A`, depending only on
`A`, with the following property.  If

```text
zeta(rho_0) = 0,  rho_0 = beta_0 + i gamma_0,
gamma_0 >= Gamma_A,  beta_0 >= 1 - A g(gamma_0),
```

then, for every `0 < epsilon < 1/10`, there is a `Y_0 = Y_0(rho_0, epsilon)`
such that every `Y >= Y_0` admits an `x` with

```text
Y <= x <= Y^C_A
```

and

```text
|psi(x) - x| > (pi / 2 - epsilon) x^beta_0 / |rho_0|.
```

One admissible choice is

```text
B = A + 2,
C_A = 28 (2 M_B + 1).
```

The significant assertion is that `C_A` is independent of `gamma_0`.  The
starting point `Y_0` is allowed to depend on `rho_0` and on `epsilon`.

## Proof

The proof has three lemmas, corresponding to the three gates of the
paper-gates note.

### Lemma 1 (decay of the lower-real-part local zeros)

Split the local residue polynomial at

```text
sigma_* = beta_0 - g(gamma_0),
```

writing `P = P_high + P_low`, where `P_high` contains the local zeros with
`beta > sigma_*` and `P_low` those with `beta <= sigma_*`.

*Proof.*  Take a term in `P_low` and write

```text
rho - rho_0 = -delta + i tau,   delta = beta_0 - beta,   |tau| < 5.
```

Then `delta >= g(gamma_0)`, and since nontrivial zeros and `rho_0` have real
parts in `(0,1)` one has `0 <= delta <= 1`.  A direct computation gives

```text
Re((rho - rho_0)^2 + 16 (rho - rho_0))
  = delta^2 - tau^2 - 16 delta
  <= delta^2 - 16 delta
  <= -15 delta.
```

Consequently

```text
|exp(m (rho - rho_0)^2 + 16 m (rho - rho_0))| <= exp(-15 m g(gamma_0)).
```

The Riemann--von Mangoldt local zero count gives, with multiplicity,

```text
#{rho : |Im rho - gamma_0| < 5} <= C log(gamma_0 + 5)
```

for an absolute `C` and sufficiently large `gamma_0`.  Including the
conjugate copy of `P` therefore gives

```text
|P_low(m)| <= 2 C log(gamma_0 + 5) exp(-15 m g(gamma_0)).
```

uniformly for `m >= H`.  It is thus enough to require

```text
H >= log(8 C log(gamma_0 + 5) / epsilon) / (15 g(gamma_0))
```

to obtain `|P_low(m)| <= epsilon / 4`.  This requirement changes
`Y_0 = exp(H_0)` but does not change the upper ratio between `m` and `H`;
in particular it cannot introduce a `gamma_0` dependence into `C_A`.  ∎

### Lemma 2 (Bellotti count for the high local package)

Set `B = A + 2` and `T = gamma_0 + 5`.  For `gamma_0 >= Gamma_A`
sufficiently large,

```text
(A + 1) g(gamma_0) <= (A + 2) g(gamma_0 + 5)
```

because `g(gamma_0) / g(gamma_0 + 5) -> 1`.  The hypothesis on `beta_0`
then gives

```text
sigma_* = beta_0 - g(gamma_0) >= 1 - (A + 1) g(gamma_0) >= 1 - B g(T).
```

Every zero in `P_high` has positive ordinate below `T` after passing to the
positive member of its conjugate pair.  Hence Bellotti's theorem gives

```text
#{P_high positive-ordinate zeros} <= N(sigma_*, T) <= M_B.
```

The count includes multiplicity and is independent of `gamma_0`.  The fact
that the Revesz residue polynomial only uses zeros to the right of the
shifted contour causes no problem: it makes `P_high` a subset of the zeros
counted by `N(sigma_*, T)`.  ∎

### Lemma 3 (Cassels length and the final `x` interval)

Let `R` be the number, with multiplicity, of positive-ordinate zeros
entering `P_high`; then `R <= M_B`.  After adjoining conjugates, `P_high`
consists of at most `2R` pure-power terms, and at least two of these terms,
those from `rho_0` and its conjugate, are exactly `1`.

The modified Cassels power-sum theorem therefore supplies an `m` satisfying

```text
H <= m <= (2 R + 1) H <= (2 M_B + 1) H
```

and `|P_high(m)| >= 2`.  Combining with Lemma 1 gives

```text
|P(m)| >= 2 - epsilon / 4.
```

The contour and far-zero estimates in the Revesz proof give

```text
|S(m)| >= |P(m)| - exp(-3 m beta_0)
```

once the original lower thresholds on `m` are met.  Since `beta_0 >= 1/2`
for sufficiently large `gamma_0`, this error is at most `exp(-3 H / 2)`.

The other evaluation of the same weighted integral gives

```text
|S(m)| <= (4 K |rho_0| / pi) (1 + 4 / (sqrt(m) gamma_0)) + 4 exp(-2 m).
```

Put

```text
L_H = 2 C log(gamma_0 + 5) exp(-15 H g(gamma_0)).
```

Since the selected Cassels parameter satisfies `m >= H`, the two estimates
imply

```text
K >= (pi / (4 |rho_0|))
        (2 - L_H - exp(-3 H beta_0) - 4 exp(-2 H))
        / (1 + 4 / (sqrt(H) gamma_0)).
```

For fixed `rho_0`, the right-hand side tends to `pi / (2 |rho_0|)` as
`H -> infinity`.  Every error displayed is decreasing after a fixed
threshold, so enlarging `Y_0` makes the conclusion valid for every
`Y >= Y_0`, not merely along a subsequence, and yields

```text
K > (pi / 2 - epsilon) / |rho_0|.
```

It remains to verify that the weighted interval lies inside the claimed
`x` interval.  From `m >= H`,

```text
q = exp(4 m) >= exp(4 H) >= Y,
```

and from the Cassels upper bound,

```text
Q = exp(28 m) <= exp(28 (2 M_B + 1) H) = Y^(28 (2 M_B + 1)).
```

Thus `[q, Q] ⊆ [Y, Y^C_A]` with

```text
C_A = 28 (2 M_B + 1),
```

which depends on `A` through `B = A + 2` and Bellotti's `M_B`, but not on
`gamma_0`.  ∎

The three lemmas assembled give the Theorem.  ∎

## What the argument improves

Revesz obtains the sharp amplitude in an interval whose exponent is of size
`log(gamma_0 + 5) / beta_0^2` in the classical zeta case; the `log gamma_0`
factor comes from applying Cassels to all locally relevant zeros using only
an `O(log gamma_0)` local count.  For a zero lying within a fixed multiple
of the Vinogradov--Korobov edge, Bellotti replaces that relevant
high-real-part count by `O_A(1)`.  Lower-real-part local zeros are removed
by the exponential estimate of Lemma 1.  The resulting exponent `C_A` is
therefore height-independent.

Schlage-Puchta [arXiv:1912.00853] obtains the shorter interval
`[X, X^(1+eta)]` for a zero with `beta_0 >= 1/2 + eta`, but with a lower
bound of size `x^beta_0 / gamma_0^(1+eta)` rather than the sharp
`(pi/2 - epsilon) x^beta_0 / |rho_0|`.  The theorem above has a different
tradeoff: it keeps the sharp amplitude and a height-independent power
interval, but only for zeros near the Vinogradov--Korobov edge.

## Source audits completed

1. Bellotti's disk-counting step is a sum over the zeros in the logarithmic
   derivative formula.  It therefore counts analytic multiplicity, as
   needed here.
2. In Revesz, the shifted contour is fixed by `b`, the Beurling continuation
   parameter, and the vertical shifts `0`, `gamma_0`, and `-gamma_0`.  It
   does not depend on the later Cassels variable `m`.  Hence the finite set
   of pure-power bases is fixed before Cassels is applied.

## Remaining publication checks

1. Check the literature for a prior theorem combining a sharp
   `pi/2 - epsilon` amplitude with a height-independent localization
   exponent for VK-edge zeros.
2. Ask Bellotti, Revesz, and Schlage-Puchta for a prior-art and
   proof-structure check after this manuscript proof exists.

These are priority checks, not missing estimates in the three lemmas.
No claim of novelty should be made until they are completed.

## Lean decision (unchanged)

Do not formalize this candidate theorem yet.  Only after independent
mathematical review should the Lean branch add the Gaussian Mellin
transform used by Revesz, the modified Cassels power-sum theorem, Bellotti's
VK-edge bounded zero count, and the final localized oscillation theorem.
