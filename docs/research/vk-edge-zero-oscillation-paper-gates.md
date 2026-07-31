# VK-edge zero oscillation: paper gates

## Status

This note records a paper-level argument only. It does not add a Lean theorem.
The argument is conditional on the zero-density theorem stated as Theorem 1.2
in Bellotti, *A new zero-density estimate for the Riemann zeta function and the
error term in the Prime Number Theorem*:

<https://arxiv.org/abs/2508.02041>

It modifies the proof of Theorem 6 in Revesz, *Oscillation of the remainder
term in the prime number theorem of Beurling, caused by a given zeta-zero*:

<https://arxiv.org/abs/2202.01837>

The purpose is to check whether Bellotti's bounded zero count at the
Vinogradov--Korobov edge removes the `log gamma_0` dependence from the
localization exponent in Revesz's theorem, while retaining the
`pi / 2 - epsilon` amplitude.

The calculation below says that it does.

## Notation and external inputs

Put

```text
g(t) = (log t)^(-2/3) (log log t)^(-1/3).
```

Let `A_0` be a constant for which the asymptotic VK zero-free region is

```text
beta >= 1 - A_0 g(|gamma|).
```

Bellotti's edge theorem has the following consequence.

### Bellotti edge count

For every fixed `B > A_0`, there are constants `T_B` and `M_B`, with `M_B`
independent of `T` and `sigma`, such that

```text
T >= T_B and sigma >= 1 - B g(T)
  implies
N(sigma, T) <= M_B.
```

Zeros are understood with multiplicity, as in the standard definition of
`N(sigma, T)`.

The Revesz proof uses the parameters

```text
H = log Y,
m >= H,
M = 16 m,
mu = 12 m,
q = exp(4 m),
Q = exp(28 m).
```

For a fixed zero

```text
rho_0 = beta_0 + i gamma_0,
```

the residue polynomial in that proof is

```text
P(m) =
  sum_{|Im rho - gamma_0| < 5}
    exp(m (rho - rho_0)^2 + 16 m (rho - rho_0))
  + conjugate terms.
```

The sum is over the zeros selected by the shifted contour and includes
multiplicity. The terms belonging to `rho_0` and its conjugate are both
exactly `1`.

## Candidate theorem

Fix `A > A_0`. There should exist constants `Gamma_A` and `C_A`, depending
only on `A`, with the following property.

If

```text
zeta(rho_0) = 0,
rho_0 = beta_0 + i gamma_0,
gamma_0 >= Gamma_A,
beta_0 >= 1 - A g(gamma_0),
```

then, for every `0 < epsilon < 1/10`, there is a
`Y_0 = Y_0(rho_0, epsilon)` such that every `Y >= Y_0` admits an `x` with

```text
Y <= x <= Y ^ C_A
```

and

```text
|psi(x) - x|
  > (pi / 2 - epsilon) x ^ beta_0 / |rho_0|.
```

One admissible paper-level choice is

```text
B = A + 2,
C_A = 28 (2 M_B + 1).
```

The significant assertion is that `C_A` is independent of `gamma_0`.
The starting point `Y_0` is allowed to depend on `rho_0` and `epsilon`.

## Gate 1: decay of the lower-real-part local zeros

Split the local residue polynomial at

```text
sigma_* = beta_0 - g(gamma_0).
```

Write

```text
P = P_high + P_low,
```

where `P_high` contains the local zeros with `beta > sigma_*`, and `P_low`
contains those with `beta <= sigma_*`.

Take a term in `P_low` and write

```text
rho - rho_0 = -delta + i tau.
```

Then

```text
delta = beta_0 - beta >= g(gamma_0),
|tau| < 5.
```

Since nontrivial zeta zeros and `rho_0` have real parts in `(0, 1)`, one has
`0 <= delta <= 1`. Direct calculation gives

```text
Re((rho - rho_0)^2 + 16 (rho - rho_0))
  = delta^2 - tau^2 - 16 delta
  <= delta^2 - 16 delta
  <= -15 delta.
```

Consequently,

```text
|exp(m (rho - rho_0)^2 + 16 m (rho - rho_0))|
  <= exp(-15 m delta)
  <= exp(-15 m g(gamma_0)).
```

The Riemann--von Mangoldt local zero count gives, with multiplicity,

```text
# {rho : |Im rho - gamma_0| < 5} <= C log(gamma_0 + 5)
```

for an absolute `C` and sufficiently large `gamma_0`. Including the conjugate
copy in `P` therefore gives

```text
|P_low(m)|
  <= 2 C log(gamma_0 + 5)
       exp(-15 m g(gamma_0)).
```

This is uniform for every `m >= H`. Thus it is enough to require

```text
H >=
  log(8 C log(gamma_0 + 5) / epsilon)
    / (15 g(gamma_0))
```

to obtain

```text
|P_low(m)| <= epsilon / 4.
```

This requirement changes `Y_0 = exp(H_0)`, but it does not change the upper
ratio between `m` and `H`. In particular, it cannot introduce a
`gamma_0` dependence into `C_A`.

This closes the first paper gate.

## Gate 2: Bellotti count for the high local package

Set `B = A + 2` and `T = gamma_0 + 5`. Since

```text
g(gamma_0) / g(gamma_0 + 5) -> 1,
```

there is a `Gamma_A` such that, for `gamma_0 >= Gamma_A`,

```text
(A + 1) g(gamma_0)
  <= (A + 2) g(gamma_0 + 5).
```

The hypothesis on `beta_0` then gives

```text
sigma_*
  = beta_0 - g(gamma_0)
  >= 1 - (A + 1) g(gamma_0)
  >= 1 - B g(T).
```

Every zero in `P_high` has positive ordinate below `T` after passing to the
positive member of its conjugate pair. Hence Bellotti's theorem gives

```text
# P_high positive-ordinate zeros
  <= N(sigma_*, T)
  <= M_B.
```

This count includes multiplicity and is independent of `gamma_0`.

The fact that the Revesz residue polynomial only uses zeros to the right of
the shifted contour causes no problem: it makes `P_high` a subset of the
zeros counted by `N(sigma_*, T)`.

This closes the second paper gate.

## Gate 3: Cassels length and the final x interval

Let `R` be the number, with multiplicity, of positive-ordinate zeros entering
`P_high`. Then

```text
R <= M_B.
```

After adjoining conjugates, `P_high` consists of at most `2 R` pure-power
terms. At least two of these terms, those from `rho_0` and its conjugate, are
exactly `1`.

The modified Cassels power-sum theorem used by Revesz therefore supplies an
`m` satisfying

```text
H <= m <= (2 R + 1) H <= (2 M_B + 1) H
```

and

```text
|P_high(m)| >= 2.
```

Combining this with Gate 1 gives

```text
|P(m)| >= 2 - epsilon / 4.
```

The contour and far-zero estimates in the Revesz proof give

```text
|S(m)| >= |P(m)| - exp(-3 m beta_0)
```

once the original lower thresholds on `m` are met. In the classical case,
`beta_0 >= 1/2` for sufficiently large `gamma_0`, so this error is at most
`exp(-3 H / 2)`.

The other evaluation of the same weighted integral gives

```text
|S(m)|
  <= (4 K |rho_0| / pi)
       (1 + 4 / (sqrt(m) gamma_0))
     + 4 exp(-2 m),
```

where

```text
K = sup_{Y <= x <= Y ^ C_A}
      |psi(x) - x| / x ^ beta_0.
```

More explicitly, put

```text
L_H =
  2 C log(gamma_0 + 5)
    exp(-15 H g(gamma_0)).
```

Since the selected Cassels parameter always satisfies `m >= H`, the two
estimates for `S` imply

```text
K >=
  (pi / (4 |rho_0|))
  (2 - L_H - exp(-3 H beta_0) - 4 exp(-2 H))
  / (1 + 4 / (sqrt(H) gamma_0)).
```

For fixed `rho_0`, the right-hand side tends to

```text
pi / (2 |rho_0|)
```

as `H -> infinity`. Every error displayed here is decreasing after a fixed
threshold. Enlarging `Y_0` therefore makes the conclusion valid for every
`Y >= Y_0`, not merely along a subsequence, and yields

```text
K > (pi / 2 - epsilon) / |rho_0|.
```

It remains to verify that the weighted interval lies inside the claimed
`x` interval. From `m >= H`,

```text
q = exp(4 m) >= exp(4 H) >= Y.
```

From the Cassels upper bound,

```text
Q = exp(28 m)
  <= exp(28 (2 M_B + 1) H)
  = Y ^ (28 (2 M_B + 1)).
```

Thus

```text
[q, Q] subset [Y, Y ^ C_A]
```

with

```text
C_A = 28 (2 M_B + 1),
```

which depends on `A` through `B = A + 2` and Bellotti's `M_B`, but not on
`gamma_0`.

This closes the third paper gate.

## What the argument improves

Revesz obtains the sharp amplitude in an interval whose exponent is of size

```text
log(gamma_0 + 5) / beta_0^2
```

in the classical zeta case. The `log gamma_0` factor comes from applying
Cassels to all locally relevant zeros using only an `O(log gamma_0)` local
count.

For a zero lying within a fixed multiple of the VK edge, Bellotti replaces
that relevant high-real-part count by `O_A(1)`. Lower-real-part local zeros
are removed by the exponential estimate in Gate 1. The resulting exponent
`C_A` is therefore height-independent.

Schlage-Puchta obtains the shorter interval `[X, X^(1+eta)]` for a zero with
`beta_0 >= 1/2 + eta`, but with a lower bound of size
`x^beta_0 / gamma_0^(1+eta)` rather than the sharp
`(pi/2 - epsilon) x^beta_0 / |rho_0|`. The candidate theorem has a different
tradeoff: it keeps the sharp amplitude and a height-independent power
interval, but only for zeros near the VK edge.

Reference:

<https://arxiv.org/abs/1912.00853>

## Source audits completed

The following two points were checked directly against the cited source
proofs.

1. Bellotti's disk-counting step is a sum over the zeros in the logarithmic
   derivative formula. It therefore counts analytic multiplicity, as needed
   here.
2. In Revesz, the shifted contour is fixed by `b`, the Beurling continuation
   parameter, and the vertical shifts `0`, `gamma_0`, and `-gamma_0`. It does
   not depend on the later Cassels variable `m`. Hence the finite set of
   pure-power bases is fixed before Cassels is applied.

Bellotti's currently available arXiv source is version 1, submitted
2025-08-04. The result should therefore be cited explicitly as an external
preprint input unless a refereed version appears.

## Remaining publication checks

The three parameter gates are closed at paper level, conditional on the cited
Bellotti and Revesz theorems. The remaining checks concern priority and
external review:

1. Check the literature for a prior theorem combining a sharp
   `pi/2 - epsilon` amplitude with a height-independent localization exponent
   for VK-edge zeros.
2. Ask Bellotti, Revesz, and Schlage-Puchta for a prior-art and proof-structure
   check after a complete manuscript proof exists.

Targeted searches of the modern papers and their cited classical chain did
not locate this combined statement. That negative search is not sufficient
to establish priority.

These are priority checks, not missing estimates in the three gates.
No claim of novelty should be made until they are completed.

## Lean decision

Do not formalize this candidate theorem yet.

The next artifact should be a conventional manuscript proof that imports the
two external results with exact theorem numbers and reproduces the modified
Revesz residue split. Only after independent mathematical review should the
Lean branch add:

1. the Gaussian Mellin transform used by Revesz;
2. the modified Cassels power-sum theorem;
3. Bellotti's VK-edge bounded zero count;
4. the final localized oscillation theorem.

The existing Carlson and finite mean-square modules remain useful
infrastructure, but they are not the source of the height-independent sharp
localization proved in this note.
