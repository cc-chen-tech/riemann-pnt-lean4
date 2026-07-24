# VK-edge `pi / 2` gap: localized pole-annihilation transfer

## Status

This note records a complete derivation, modulo Bellotti's stated zero count
and Revesz's standard simultaneous zero-avoiding contour lemmas, from the
missing-harmonic gap to an occurrence in every sufficiently late power
interval. It replaces the
weighted Cassels--Turan step proposed in
`vk-edge-pi-over-two-zeta-bridge.md` by finite-pole annihilation.

The argument has passed two internal adversarial audits. Historical priority
and an external specialist review remain open. Until those checks are
complete, this note must not be cited as an established new theorem in the
literature.

The proposed conclusion is stronger than the preregistered localization:
the power exponent can be taken to be `7`, independently of the target zero
and of the Bellotti cardinality constant. The starting point remains
ineffective and may depend on the complete finite zero configuration used by
the filters.

## 1. Classical transform

Put

```text
Delta(x) = psi(x) - x
```

and

```text
D(s)
  = -zeta'(s)/zeta(s) - s/(s-1)
  = s integral_1^infinity Delta(x) x^(-s-1) dx.
```

The pole at `s=1` is canceled. In the half-plane used below, the remaining
poles of `D` are the zeta zeros, each a simple pole whose residue is its
negative analytic multiplicity:

```text
Res_(s=rho) D(s) = -m(rho).
```

For a polynomial `A` and a center `w=u+iv`, define

```text
U_A(w;m)
  = (1/(2 pi i)) integral_(Re(s)=2)
      D(s+w) A(s) exp(m s^2 + 16m s) ds.       (1)
```

The ordinary Revesz transform is the case `A=1`.

Define the normalized Gaussian

```text
G_m(t)
  = (1/(2 sqrt(pi m))) exp(-t^2/(4m)).
```

If

```text
A(s) = sum_(k=0)^d a_k s^k,
```

put

```text
G_(A,m)(t) = sum_(k=0)^d a_k G_m^(k)(t).       (2)
```

Mellin inversion and the identity for `D` give the exact real-variable form

```text
U_A(w;m)
  = integral_1^infinity
      Delta(x) x^(-w-1)
      (w G_(A,m)(16m-log x)
        + G_(A,m)'(16m-log x)) dx.             (3)
```

No integration-by-parts remainder is hidden in (3).

## 2. Polynomial Gaussian stability

For every fixed integer `k>=0`,

```text
integral_R |G_m^(k)(t)| dt = C_k m^(-k/2),     (4)
```

where `C_k` is the corresponding absolute Hermite moment. Consequently, if
`A(0)=1`, then

```text
||G_(A,m)-G_m||_1 = O_A(m^(-1/2)),
||G_(A,m)'||_1    = O_A(m^(-1/2)).             (5)
```

The constants may be arbitrarily large; they are fixed once the target zero
and the finite annihilated pole sets are fixed.

The same Hermite formula gives, for fixed `A`,

```text
|G_(A,m)(t)| + |G_(A,m)'(t)|
  <= C_A (1+|t|)^(d+1) G_m(t)                 (6)
```

after harmlessly enlarging `C_A`, for `m>=1`.

For the classical PNT error,

```text
|Delta(x)| <= C x(1+log x).
```

If `u>0`, equations (3) and (6), followed by completing the square, show that
the parts outside

```text
q = exp(4m),  Q = exp(28m)                    (7)
```

satisfy

```text
U_A(w;m; x<q) + U_A(w;m; x>Q) = O_(A,w)(e^(-c_u m)).
                                                               (8)
```

Indeed, with `t=16m-log x`, the exponential part is

```text
exp((1-u)(16m-t)-t^2/(4m)).
```

On `t>=12m` it is at most `exp(-32m)`, and on `t<=-12m` it
is at most `exp(-8m)` for `u>0`. Fixed polynomial factors are absorbed by
slightly reducing the positive decay constant.

## 3. Finite-pole annihilation

Fix the target real part `u>0`, then choose one auxiliary Axiom-A parameter

```text
0 < theta < u.
```

For the ordinary integers the counting remainder is `O(1)`, so every such
positive `theta` is available. Put

```text
b = (u+theta)/2,
a = (b+theta)/2 = (u+3theta)/4.                (9)
```

Before defining any filter or sending `m` to infinity, construct one standard
zero-avoiding Revesz contour `Gamma_b` for the fixed symmetric translation
set

```text
{0, +-gamma_0, +-n gamma_0}.                  (10)
```

Its real coordinate lies in `[a,b]`. This order of choices is essential: the
contour, the local zero sets, and the filter coefficients remain fixed while
`m` grows.

For a center `w=u+iv`, let `Z_w` be the finite multiset of zeta zeros in

```text
Re(rho) >= a,
|Im(rho)-v| < 5.                              (11)
```

Only distinct zero locations are needed in the product below, because a
logarithmic derivative has a simple pole even when its residue is a larger
multiplicity.

### Target filter

If `w` itself is a zeta zero, define

```text
A_w(s)
  = product_(rho in distinct(Z_w), rho != w)
      (1 - s/(rho-w)).                         (12)
```

Then

```text
A_w(0)=1,
A_w(rho-w)=0  for every other local zero.      (13)
```

### Empty-center filter

If `w` is not a zeta zero, define

```text
B_w(s)
  = product_(rho in distinct(Z_w))
      (1 - s/(rho-w)).                         (14)
```

Again `B_w(0)=1`, and now every local zero residue is killed.

For the conjugate center use

```text
A_(conj w)(s) = conjugate(A_w(conjugate(s))),
```

and similarly for `B`. This makes the paired transform real.

Shift the contour in (1) from `Re(s)=2` to `Gamma_b-u`. The residue formula is

```text
U_A(w;m)
  = contour_A(w;m)
    - sum_(crossed rho)
        m(rho) A(rho-w)
        exp(m(rho-w)^2+16m(rho-w)).            (15)
```

Equations (12)--(14) remove every unwanted term with
`|Im(rho)-v|<5`.

The remaining residue terms have `|Im(rho)-v|>=5`. Every crossed zero lies
to the right of a contour whose real coordinate is at least `a`, so

```text
a <= Re(rho) <= 1.
```

Thus `delta=Re(rho)-u` lies in `(-1,1)`, where
`delta^2+16delta` is increasing. Since `0<u<1`,

```text
Re((rho-w)^2+16(rho-w))
  <= -25 + (1-u)^2 + 16(1-u)
  < -8.                                       (16)
```

The standard `O(log T)` zero count in unit-height strips, together with the
fixed polynomial growth of `A`, therefore gives

```text
sum_(far crossed rho) ... = O_(A,w)(e^(-c m)).
                                                               (17)
```

### Polynomial-weighted simultaneous contour lemma

On `Gamma_b`, Revesz's translated logarithmic-derivative estimate is uniform
for every translate in (10):

```text
|D(s+iv)|
  <= C_(u,theta,n)
      (1+log(|Im(s)|+n gamma_0+5))^2.          (18)
```

If `A` has degree `d`, then on the shifted contour

```text
|A(s)| <= C_A (1+|Im(s)|)^d.                  (19)
```

The real exponential factor is bounded by

```text
exp(m((u-a)^2+16(b-u)))
  = exp(m(9(u-theta)^2/16-8(u-theta)))
  <= exp(-119(u-theta)m/16).                  (20)
```

The contour consists of vertical segments plus horizontal segments of
uniformly bounded length at heights separated by at least one. Equations
(18)--(20) therefore reduce its absolute value to a fixed multiple of

```text
exp(-119(u-theta)m/16)
  * (
      integral_R
        (1+|t|)^d(1+log(|t|+n gamma_0+5))^2
        exp(-m t^2) dt
      +
      sum_(k>=1)
        (1+t_k)^d(1+log(t_k+n gamma_0+5))^2
        exp(-m t_k^2)
    ).
```

The parenthesis is `O_(A,w)(1)` for `m>=1`. Thus the same simultaneous
contour proves, for every fixed filter,

```text
contour_A(w;m)
  = O_(A,w,theta)(e^(-c_(u-theta) m)).         (21)
```

The identical unit-strip zero count used by Revesz proves (17): the extra
factor `(1+|gamma-v|)^d` from `A` is summable against
`exp(-m|gamma-v|^2)`. This proves the required polynomial-weighted contour
extension rather than assuming it.

Equations (15)--(21) prove the filter identities

```text
U_(A_w)(w;m) = -m(w) + o(1)      if zeta(w)=0,
U_(B_w)(w;m) = o(1)              if zeta(w)!=0.                 (22)
```

The same statements hold at the conjugate centers.

## 4. The missing-harmonic dual kernel

Let

```text
rho_0 = beta_0+i gamma_0
```

be a zeta zero with `gamma_0>0`. Suppose an odd integer `n` satisfies

```text
w_n = beta_0+i n gamma_0,
zeta(w_n) != 0.                                (23)
```

Put

```text
epsilon_n
  = sign(mean(sign(cos theta) cos(n theta))),
t_n = sin(1/(4n)),

q_n(theta)
  = cos(theta)-epsilon_n t_n cos(n theta).     (24)
```

The dual-certificate calculation in
`vk-edge-pi-over-two-abel-transfer.md` gives

```text
mu_n := mean |q_n|
  <= 2/pi - t_n/(pi n)
  < 2/pi.                                      (25)
```

Let `A_0` be the target filter (12) at `rho_0`, and let `B_n` be the
empty-center filter (14) at `w_n`. Set

```text
c_n
  = -epsilon_n t_n |rho_0|
      exp(i n arg(rho_0)) / w_n.               (26)
```

Define the real paired combination

```text
V_m
  = U_(A_0)(rho_0;m)
    + U_(A_0^*)(conjugate(rho_0);m)
    + c_n U_(B_n)(w_n;m)
    + conjugate(c_n)
        U_(B_n^*)(conjugate(w_n);m),           (27)

A_0^*(s) = conjugate(A_0(conjugate(s))),
B_n^*(s) = conjugate(B_n(conjugate(s))).
```

Because `Delta` and the Gaussian are real, the second term is the conjugate
of the first and the fourth is the conjugate of the third. Thus `V_m` is
real.

By (22),

```text
V_m = -2 m(rho_0)+o(1),
|V_m| = 2 m(rho_0)+o(1).                       (28)
```

In the real-variable representation (3), the leading Gaussian kernel in
(27) is exactly

```text
2 |rho_0| G_m(16m-log x)
  q_n(gamma_0 log x-arg(rho_0)).               (29)
```

All differences caused by replacing `G_(A,m)` and `G_(B,m)` by `G_m`, and
all derivative terms in (3), have total `L1` norm

```text
O_(rho_0,A_0,B_n)(m^(-1/2))                    (30)
```

by (5).

## 5. Main-interval upper bound

Define

```text
K_m
  = sup_(exp(4m)<=x<=exp(28m))
      |Delta(x)| / x^beta_0.                   (31)
```

Equations (3), (5), (8), (27), and (29) give

```text
|V_m|
  <= 2 K_m |rho_0|
      integral_R G_m(16m-y)
        |q_n(gamma_0 y-arg(rho_0))| dy
    + K_m O_(rho_0,A_0,B_n)(m^(-1/2))
    + O_(rho_0,A_0,B_n)(e^(-c m)).             (32)
```

For every continuous `2pi`-periodic function `phi`,

```text
integral_R G_m(t) phi(c-gamma_0 t) dt
  -> mean(phi)                                 (33)
```

as `m` tends to infinity, uniformly in `c`. More explicitly, the `k`th
Fourier mode is multiplied by

```text
exp(-m k^2 gamma_0^2).
```

To justify the assertion for an arbitrary continuous `phi`, approximate it
uniformly by a trigonometric polynomial. Every nonzero mode of that finite
polynomial vanishes under the displayed Gaussian multiplier, while the
uniform approximation error is unchanged because `G_m` has mass one. This
proves (33), uniformly in `c`, and applies in particular to
`phi(theta)=|q_n(theta)|`.

Apply (33) to `phi(theta)=|q_n(theta)|`. From (28) and (32),

```text
2m(rho_0)
  <= 2 K_m |rho_0| (mu_n+o(1))+o(1).
```

This inequality is valid term by term; no boundedness assumption on the
sequence `K_m` is needed, since its entire error is absorbed into the
coefficient `mu_n+o(1)`.

Therefore

```text
liminf_(m->infinity) K_m |rho_0|
  >= m(rho_0)/mu_n
  >= m(rho_0) /
      (2/pi-sin(1/(4n))/(pi n)).               (34)
```

This step uses no power-sum lemma and no recurrence theorem.

## 6. Every power interval

Take

```text
m = (log Y)/4.
```

Then (7) becomes exactly

```text
[q,Q] = [Y,Y^7].                               (35)
```

Thus, for every `epsilon>0` and every sufficiently large `Y` depending on the
fixed zero and the finite filters, there is an

```text
x in [Y,Y^7]
```

such that

```text
|psi(x)-x|
  >= (m(rho_0)/mu_n-epsilon)
       x^beta_0/|rho_0|.                       (36)
```

## 7. Bellotti specialization

Use the notation and the Bellotti count `M_A` from
`vk-edge-pi-over-two-abel-transfer.md`. For every sufficiently high zero in
the fixed VK-edge band, one of

```text
gamma_0, 3gamma_0, ..., (2M_A+1)gamma_0
```

is missing on `Re(s)=beta_0`. Therefore (23) holds for an odd
`n<=2M_A+1`.

Define

```text
L_(M_A)
  = 1 /
    (2/pi
      - sin(1/(4(2M_A+1)))/(pi(2M_A+1))),

delta_A = L_(M_A)-pi/2 > 0.                    (37)
```

Since the right side of (34) is at least `m(rho_0)L_(M_A)`, equations
(35)--(37) yield the candidate theorem:

> For every fixed `A>A_0`, every sufficiently high zeta zero
>
> ```text
> rho_0=beta_0+i gamma_0,
> beta_0 >= 1-A g(gamma_0),
> ```
>
> and every `epsilon>0`, there is a
> `Y_0=Y_0(rho_0,epsilon)` such that every `Y>=Y_0` admits
> `x in [Y,Y^7]` with
>
> ```text
> |psi(x)-x|
>   >= (pi/2+delta_A-epsilon)
>        x^beta_0/|rho_0|.
> ```

Multiplicity only strengthens the displayed conclusion.

## 8. Remaining release gates

The two internal audits checked the transform identity, residue sign,
simultaneous contour parameters, polynomial-weighted contour and far-residue
estimates, conjugate phase, relative main-interval error, periodization, and
the every-`m` quantifier.

Before claiming a new theorem in the literature:

1. search Ingham, Anderson--Stark, Pintz, Revesz, and later effective
   oscillation work for finite-pole annihilating kernels;
2. obtain an external analytic-number-theory or Fourier-analysis review;
3. rewrite the argument in conventional theorem-lemma-proof form with exact
   citations to the two imported results.

No Lean target should be added until these gates are closed.
