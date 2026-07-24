# VK-edge `pi / 2` gap: Mellin--Abel transfer

## Status

This note gives a complete proof, modulo the stated Bellotti zero-density
theorem, of a global `limsup` oscillation constant strictly larger than
`pi / 2` for a zeta zero near the Vinogradov--Korobov boundary.

This Abel argument alone does not localize the large value. The separate
finite-pole annihilation proof in
`vk-edge-pi-over-two-localized-transfer.md` gives occurrence in every
sufficiently late interval `[Y,Y^7]`.

Historical priority is not asserted. The Abel-coefficient argument is close
to classical Ingham and Anderson--Stark oscillation methods. The potentially
new point is the combination of:

1. Bellotti's bounded zero count at the VK edge;
2. a missing odd multiple of the target ordinate;
3. the quantitative missing-harmonic gap from
   `vk-edge-pi-over-two-proof-record.md`.

## Notation

Put

```text
Delta(x) = psi(x) - x
```

and, for sufficiently large `t`,

```text
g(t) = (log t)^(-2/3) (log log t)^(-1/3).
```

Zeros are counted with analytic multiplicity. Write

```text
rho = beta + i gamma,
m(rho) = multiplicity of rho.
```

The Mellin identity used below is

```text
integral_1^infinity Delta(x) x^(-s-1) dx
  = -zeta'(s) / (s zeta(s)) - 1 / (s-1),     (1)
```

initially for `Re(s)>1`. Its right-hand side is meromorphic. The apparent
pole at `s=1` cancels.

## Bellotti input

We use the following consequence of Bellotti's Theorem 1.2.

For every fixed `B>A_0`, there are constants `C_B` and `T_B` such that

```text
N(sigma,T) <= C_B                              (2)
```

whenever

```text
T >= T_B,
sigma >= 1 - B g(T).
```

Here `N(sigma,T)` counts, with multiplicity, zeros satisfying

```text
0 < gamma < T,
beta > sigma.
```

Only the existence of `C_B` is needed. Bellotti also gives a route to an
effective value.

## Abstract Abel missing-harmonic lemma

### Statement

Let `h` be a real, locally integrable function on `[0,infinity)`, and suppose

```text
K = limsup_(y -> infinity) |h(y)| < infinity.
```

Let `lambda>0`. Suppose the following Abel coefficients exist:

```text
c_k =
  lim_(a -> 0+) a integral_0^infinity
    h(y) exp(-a y) exp(-i k lambda y) dy.
```

Assume

```text
|c_1| = Q > 0
```

and, for some odd integer `n` with `1 <= n <= 2M+1`,

```text
c_n = 0.
```

Then

```text
K / Q >= L_M,                                  (3)

L_M =
  1 /
  (2/pi
    - sin(1/(4(2M+1))) / (pi(2M+1)))
  > pi/2.
```

### Linear dual certificate

The strict gap has a linear form that is useful for localization. For odd
`n`, let

```text
epsilon_n =
  sign(mean(sign(cos theta) cos(n theta))),

t_n = sin(1/(4n)),

q_n(theta) =
  cos(theta) - epsilon_n t_n cos(n theta).
```

The standard Fourier coefficient gives

```text
|mean(sign(cos theta) cos(n theta))|
  = 2/(pi n).
```

On the set `|cos theta|>t_n`, adding the second term does not change the
sign, so the absolute value is exactly linear there. On the complementary
set, the failure of linearity is at most `2t_n`. Since

```text
measure {|cos theta|<=t_n}
  = (2/pi) arcsin(t_n)
  = 1/(2pi n),
```

we obtain

```text
mean |q_n|
  <= 2/pi - 2t_n/(pi n) + t_n/(pi n)
  = 2/pi - t_n/(pi n).                         (D)
```

After the phase normalization below, the missing coefficient gives

```text
Q
  = AbelMean(h cos(lambda y))
  = AbelMean(h q_n(lambda y)).
```

Thus (D) directly implies

```text
K/Q >= 1/(2/pi-t_n/(pi n)).
```

For `n<=2M+1`, this is at least `L_M`. This is equivalent in strength to the
defect proof below, but it exhibits the two-frequency dual kernel explicitly.

### Phase normalization

Choose `tau>=0` such that

```text
exp(i lambda tau) c_1 = Q.
```

Replacing `h(y)` by `h(y+tau)` multiplies `c_k` by
`exp(i k lambda tau)`. This follows after changing variables; the omitted
finite interval has zero Abel mass. Thus `c_1=Q` may be assumed real and
positive, while `c_n=0` is preserved.

Fix `epsilon>0`. After changing `h` on a bounded interval, which does not
change any Abel coefficient, we may assume

```text
|h(y)| <= K+epsilon
```

for all `y>=0`. Put

```text
f(y) = h(y)/(K+epsilon),
u(y) = cos(lambda y),
s(y) = sign(u(y)).
```

Then `f` is real and `|f|<=1`.

### Equality defect

Let

```text
d mu_a(y) = a exp(-a y) dy.
```

Abel averages of periodic functions converge to their period averages.
Consequently,

```text
lim_(a -> 0+) integral |u| d mu_a = 2/pi.
```

Also,

```text
lim_(a -> 0+) integral f u d mu_a
  = Q/(K+epsilon).
```

Since `s u=|u|` and `|s-f|=1-sf`, define

```text
D =
  lim_(a -> 0+) integral |u| |s-f| d mu_a
  = 2/pi - Q/(K+epsilon).                      (4)
```

The integrands are nonnegative.

### Missing harmonic

For odd `n`, the complex Fourier coefficient of `sign(cos)` at frequency
`n` has magnitude

```text
2/(pi n).
```

The hypothesis `c_n=0` therefore gives

```text
liminf_(a -> 0+)
  integral |s-f| d mu_a
    >= 2/(pi n)
    >= b_M,                                    (5)

b_M = 2/(pi(2M+1)).
```

Indeed, the integral of the absolute value dominates the absolute value of
the `n`th Abel coefficient.

For `0<eta<1`, split according to `|u|>=eta`. Since `|s-f|<=2`,

```text
limsup_(a -> 0+)
  integral |s-f| d mu_a
    <= D/eta + (4/pi) arcsin(eta).              (6)
```

Choose

```text
eta = sin(pi b_M/8)
    = sin(1/(4(2M+1))).
```

The second term in (6) is `b_M/2`. Equations (5) and (6) imply

```text
D >=
  sin(1/(4(2M+1))) / (pi(2M+1))
  = d_M.                                       (7)
```

Combining (4) and (7), then letting `epsilon` decrease to zero, proves (3).

## Abel coefficients of the PNT error

Fix a nontrivial zero

```text
rho_0 = beta_0 + i gamma_0,
gamma_0 > 0,
m_0 = m(rho_0).
```

Define

```text
h(y) = |rho_0| exp(-beta_0 y) Delta(exp y).     (8)
```

If

```text
limsup_(x -> infinity)
  |Delta(x)| |rho_0| / x^beta_0
```

is infinite, the desired conclusion is immediate. Assume it is finite.
Then `h` is eventually bounded, so its Laplace transform is holomorphic for
`Re(z)>0`.

By (1),

```text
H(z)
  = integral_0^infinity h(y) exp(-z y) dy
  = |rho_0|
    (-zeta'(beta_0+z) /
       ((beta_0+z) zeta(beta_0+z))
     - 1/(beta_0+z-1)).                         (9)
```

The identity initially holds for `Re(beta_0+z)>1` and continues
meromorphically.

### No zero lies to the right

The left side of (9) is holomorphic in `Re(z)>0`. A zero
`rho=beta+i gamma` with `beta>beta_0` would give the right side a pole at

```text
z = (beta-beta_0) + i gamma,
```

which lies in that half-plane. No other term cancels this pole. Hence

```text
zeta(rho) = 0 implies Re(rho) <= beta_0.        (10)
```

This is the standard Mellin converse step.

### Boundary coefficients

At a zero

```text
rho = beta_0 + i gamma
```

of multiplicity `m(rho)`, the residue of (9) at `z=i gamma` is

```text
-m(rho) |rho_0| / rho.
```

Therefore

```text
lim_(a -> 0+) a integral_0^infinity
  h(y) exp(-a y) exp(-i gamma y) dy
    = -m(rho) |rho_0| / rho.                   (11)
```

If `beta_0+i gamma` is not a zero, the right side of (9) is holomorphic in a
neighborhood of `i gamma`, and the same Abel coefficient is zero.

At the distinguished ordinate,

```text
|c_1| = m_0.                                   (12)
```

Thus the multiplicity strengthens rather than weakens the final estimate.

## Bellotti supplies a missing odd multiple

The argument first gives the following general finite-count criterion.

> Let `rho_0=beta_0+i gamma_0` be a zeta zero. If, for some integer `M>=1`,
> there are at most `M` distinct zeros on `Re(s)=beta_0` with
> `0<Im(s)<(2M+2)gamma_0`, then
>
> ```text
> limsup_(x -> infinity)
>   |psi(x)-x| |rho_0| / x^beta_0
>     >= m(rho_0) L_M.                         (13)
> ```

Indeed, among the `M+1` odd multiples

```text
gamma_0, 3 gamma_0, ..., (2M+1)gamma_0
```

one is absent from the boundary zero set. If the left side of (13) is finite,
the Mellin argument first excludes every zero to the right of `beta_0`; the
Abel missing-harmonic lemma then proves (13). If the left side is infinite,
the conclusion is immediate.

Bellotti makes `M` uniform for zeros in a fixed VK-edge band.

Fix `A>A_0`, and choose one constant

```text
B>A.
```

Let `C_B` be as in (2), and choose an integer

```text
M_A >= max(1, C_B).
```

Put

```text
R_A = 2M_A+2.
```

Since

```text
g(R_A t)/g(t) -> 1
```

as `t` tends to infinity and `B>A`, there is `Gamma_A` such that

```text
B g(R_A t) > A g(t)                            (14)
```

for `t>=Gamma_A`. Increase `Gamma_A` so that Bellotti's theorem applies at
`T=R_A t`.

Now suppose

```text
gamma_0 >= Gamma_A,
beta_0 >= 1 - A g(gamma_0).                    (15)
```

Take

```text
T = R_A gamma_0,
sigma = 1 - B g(T).
```

Equations (14) and (15) give

```text
sigma < beta_0.
```

Hence every zero on the line `Re(s)=beta_0` with ordinate in `(0,T)` is
counted by `N(sigma,T)`, and there are at most `M_A` of them.

Consider the `M_A+1` distinct odd ordinates

```text
gamma_0, 3 gamma_0, ..., (2M_A+1) gamma_0.
```

All lie below `T`. At least one of the points

```text
beta_0 + i n gamma_0
```

is not a zero. For this odd `n`, the Abel coefficient in (11) is zero.

## Main theorem

For every `A>A_0`, define

```text
delta_A = L_(M_A) - pi/2 > 0.                  (16)
```

Then every sufficiently high zeta zero

```text
rho_0 = beta_0+i gamma_0,
beta_0 >= 1-A g(gamma_0),
```

satisfies

```text
limsup_(x -> infinity)
  |psi(x)-x| |rho_0| / x^beta_0
    >= m(rho_0) L_(M_A)
    >= pi/2 + delta_A.                         (17)
```

Proof: if the left side is infinite there is nothing to prove. Otherwise
(10) holds, (11)--(15) provide a missing odd Abel coefficient, and the
abstract Abel missing-harmonic lemma applies to (8), with
`Q=m(rho_0)`.

Equation (17) is a strict global improvement over the `pi/2` given-zero
constant for zeros in the VK-edge band.

## Exact scope

Closed by this argument:

1. a strict, non-explicit `delta_A>0`;
2. analytic multiplicities;
3. all infinitely many other zeta frequencies;
4. the global absolute `limsup` conclusion.

Not closed by this Abel argument:

1. occurrence in every interval `[Y,Y^C_A]`, which is handled separately in
   `vk-edge-pi-over-two-localized-transfer.md`;
2. an effective numerical value of `delta_A`, since a numerical Bellotti
   constant has not been inserted;
3. one-sided `Omega_+` and `Omega_-` constants;
4. historical priority.

The earlier envelope-local finite-package requirement was sufficient but not
necessary for either the global theorem or the pole-annihilation
localization.
