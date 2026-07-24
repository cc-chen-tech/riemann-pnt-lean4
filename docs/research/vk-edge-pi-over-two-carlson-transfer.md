# Carlson transfer: a strict `pi / 2` gap for every right-hand zeta zero

## Status

This note records a stronger specialization of
`vk-edge-pi-over-two-localized-transfer.md`. It removes the Bellotti VK-edge
hypothesis and uses the classical fixed-line Carlson zero-density estimate
already proved in Lean on `main`.

The mathematical implication proved below is:

> Every nontrivial zeta zero `rho_0=beta_0+i gamma_0` with
> `beta_0>1/2` and `gamma_0>0` has a constant `delta_(rho_0)>0` such
> that, for every `epsilon>0` and every sufficiently large `Y`, some
> `x in [Y,Y^7]` satisfies
>
> ```text
> |psi(x)-x|
>   >= (pi/2+delta_(rho_0)-epsilon)
>        x^beta_0/|rho_0|.
> ```

This is an unconditional implication about the Riemann zeta function. It
does not assert that a zero with `beta_0>1/2` exists. Historical priority and
external specialist review remain open, so the result is still a candidate
new theorem rather than an established novelty claim.

## 1. Carlson input

Fix a nontrivial zero

```text
rho_0 = beta_0+i gamma_0,
1/2 < beta_0 < 1,
gamma_0 > 0.
```

Choose, for definiteness,

```text
sigma = (beta_0+1/2)/2.
```

Then

```text
1/2 < sigma < beta_0 < 1.
```

The theorem

```lean
PrimeNumberTheorem.CarlsonZeroDensity.carlson_zeroDensity_isBigO
```

proved in `PrimeNumberTheorem/CarlsonAsymptotic.lean` states, with analytic
multiplicity,

```text
N(sigma,T)
  = O(T^alpha (log T)^4),

alpha = 4 sigma (1-sigma).                       (1)
```

Here `N(sigma,T)` counts zeros with

```text
0 < Im(rho) <= T,
sigma < Re(rho).
```

The exponent is strictly sublinear:

```text
alpha
  = 1-(2sigma-1)^2
  < 1.                                           (2)
```

Since every fixed power of `log T` is `o(T^(1-alpha))`, (1)--(2) give

```text
N(sigma,T) = o(T).                               (3)
```

Only (3), not the precise Carlson exponent, is needed below.

## 2. A missing odd multiple

For a positive integer `M`, put

```text
T_M = (2M+2) gamma_0.
```

Equation (3) gives

```text
N(sigma,T_M)/(M+1) -> 0                          (4)
```

because `T_M/(M+1)=2 gamma_0` is fixed. Choose one integer
`M=M(rho_0)>=1` large enough that

```text
N(sigma,T_M) <= M.                               (5)
```

Consider the `M+1` distinct points

```text
beta_0+i gamma_0,
beta_0+3i gamma_0,
...,
beta_0+i(2M+1)gamma_0.                           (6)
```

Every point in (6) lies below `T_M`. If it is a zeta zero, then its real
part is greater than `sigma`, so it contributes at least one to the
multiplicity-counted quantity in (5). Therefore not all points in (6) can be
zeros. There is an odd integer

```text
1 <= n <= 2M+1
```

such that

```text
zeta(beta_0+i n gamma_0) != 0.                   (7)
```

The positivity of each contribution is the project theorem
`ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero`: an actual zero
away from the pole at `1` has analytic multiplicity at least one.

This pigeonhole step is the exact place where Carlson's sublinear density
improves on the general Beurling situation. A merely linear `O(T)` count
does not imply (4).

## 3. Localized oscillation

Apply Sections 3--6 of
`vk-edge-pi-over-two-localized-transfer.md` to `rho_0` and the missing odd
multiple (7). The finite target and empty-center annihilators give

```text
liminf_(m->infinity)
  |rho_0| sup_(exp(4m)<=x<=exp(28m))
    |psi(x)-x|/x^beta_0
  >= m(rho_0)/mu_n,                              (8)
```

where

```text
mu_n
  <= 2/pi-sin(1/(4n))/(pi n)
  < 2/pi.                                        (9)
```

Define the explicit positive gap attached to the chosen `M` by

```text
L_M
  = 1 /
    (2/pi
      - sin(1/(4(2M+1)))/(pi(2M+1))),

delta_(rho_0) = L_M-pi/2 > 0.                   (10)
```

For completeness, the comparison used here is elementary. If `1<=n<=N`,
then

```text
0 < 1/(4N) <= 1/(4n) < pi/2,
```

so monotonicity and positivity of `sin` on this interval give

```text
sin(1/(4N))/N <= sin(1/(4n))/n.                 (10a)
```

Moreover `sin(1/(4n))/n<1`, hence the denominator defining `L_M` is
strictly larger than `1/pi`. The mean `mu_n` is positive because the
continuous trigonometric polynomial `q_n` is not identically zero (its
frequency-one Fourier coefficient is nonzero). Thus all reciprocals used in
(8)--(10) are legitimate.

Taking `N=2M+1` in (10a), and using `n<=2M+1` and
`m(rho_0)>=1`, equations (8)--(10) imply

```text
liminf_(m->infinity)
  |rho_0| sup_(exp(4m)<=x<=exp(28m))
    |psi(x)-x|/x^beta_0
  >= pi/2+delta_(rho_0).                         (11)
```

Finally set `m=(log Y)/4`. Then

```text
[exp(4m),exp(28m)] = [Y,Y^7],
```

and (11) gives the theorem stated at the beginning of this note.

The exponent `7` is absolute. The threshold `Y_0` and the positive gap
`delta_(rho_0)` may depend on the target zero and on the finite local zero
configurations used by the annihilating filters.

## 4. Consequence if RH fails

If the Riemann Hypothesis is false, first use the classical real-axis fact
that `zeta(sigma)<0` for real `0<sigma<1`; hence an off-critical-line
nontrivial zero cannot be real. The functional equation reflects a zero from
the left half of the critical strip to the right half, and conjugation changes
a negative ordinate to a positive one. Therefore there is a nontrivial zero
with

```text
Re(rho_0)>1/2,
Im(rho_0)>0.
```

Hence RH failure implies the existence of a zeta zero whose normalized
contribution forces a strict `pi/2` oscillation gap in every sufficiently late
interval `[Y,Y^7]`.

This is not a proof that RH fails. It is a stronger consequence of any
hypothetical off-critical-line zero.

## 5. Prior-art boundary

Revesz (1988, Section 5) already introduced a sublinear zero-density
condition and explained why the linearly dense odd-harmonic configuration
behind the `pi/2` obstruction is then impossible. Revesz (2023, discussion
around the finite-sum construction) again makes this qualitative point.
Those sources also show that no positive gap can be uniform over all
finite-support sizes: finite sine polynomials can approach `pi/2` as their
number of frequencies grows.

The candidate contribution here is narrower:

```text
Carlson N(sigma,T)=o(T)
  -> a missing odd multiple for each fixed right-hand zeta zero
  -> an explicit positive gap depending on that zero
  -> occurrence in every [Y,Y^7].
```

A targeted search has not yet located this exact strict, localized
conclusion. That absence is not a proof of priority. In particular, the
general coefficient theorems of Anderson--Stark and the full statements of
Revesz (1988) must be checked before any novelty claim.

The closest located statements are Revesz (1988), Corollary 2, which retains
`pi/2-epsilon` in intervals whose exponent grows like `log |rho_0|`, and
Revesz (2023), Theorem 5, whose localization exponent likewise depends on
the target zero. Anderson--Stark can produce finite-frequency gains under
stronger integer-independence hypotheses, but a single missing odd harmonic
does not meet those hypotheses. The potential new content is therefore the
combination of the strict missing-harmonic dual gap with the absolute
localization exponent `7`, not Carlson's pigeonhole observation by itself.

## 6. Verification obligations

Before this result is described as new mathematics:

1. obtain an external analytic-number-theory review of the
   polynomial-weighted contour shift and the every-`m` passage;
2. complete a primary-source comparison with Revesz (1988),
   Anderson--Stark, Pintz, and Schlage-Puchta;
3. rewrite the argument as a conventional theorem-lemma-proof manuscript;
4. only then create a separate Lean formalization branch for the
   Carlson-to-missing-harmonic bridge and the localized transform.

At present Lean verifies the Carlson Big-O input and the multiplicity
infrastructure only. The `o(T)` specialization, missing-harmonic argument,
annihilating filters, and final interval theorem in this note remain a paper
proof candidate.
