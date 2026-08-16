# Direct-L2 energy assembly and strict-constant preservation

## Purpose

This note specifies the assembly theorem between the protected low-zero energy
result, the Carlson square-multiplicity capacity, and the half-isolated
Occupancy estimate.  It does not prove a new Gram or separation theorem.

The key bookkeeping rule is that Carlson supplies a coefficient square mass,
while oscillation is concluded from an L2 norm.  Energy exponents, norm
exponents, and pointwise constants must not be conflated.

## Abstract weighted-L2 transfer

Let `mu` be a finite nonnegative measure on an observation interval `I`, and
write

```text
W = mu(I),
0 < W < infinity.
```

Let `A > 0` be the target amplitude, let `M` be the low-zero main packet, and
let `R` be the complementary zero and contour contribution.  Assume

```text
||M||_L2(mu) >= c_main * A * sqrt(W),
||R||_L2(mu) <= c_tail * A * sqrt(W),
c_tail < c_main - pi/2.
```

The reverse triangle inequality gives

```text
||M + R||_L2(mu)
  >= (c_main - c_tail) * A * sqrt(W)
  >  (pi/2) * A * sqrt(W).
```

Consequently the weighted essential supremum of `|M+R|` is strictly larger
than `(pi/2)*A`.  A point witness follows once the measure/support theorem used
by the low-energy module provides an actual point rather than only an
almost-everywhere class.

This proves an absolute-value witness.  It does not distinguish signs.

## Gram/Schur interface

For one real-part and dyadic-height block, write

```text
R_B(t) = sum_{rho in B} a(rho) * exp(i * Im(rho) * t).
```

Expanding the weighted energy gives

```text
integral_I w(t) * |R_B(t)|^2 dt
  = sum_{rho,rho' in B}
      a(rho) * conj(a(rho'))
      * K(Im(rho) - Im(rho')),
```

where `K` is the Fourier transform of the observation weight.  The
half-isolated side supplies a Schur/Occupancy theorem of the form

```text
energy(B) <= C_gram * Occ(B) * sum_{rho in B} |a(rho)|^2.
```

The Carlson side supplies only the last square sum.  No Carlson theorem should
mention the Gram kernel, and no Gram theorem should restate zero density.

## One-block exponent ledger

For a zero in a strip

```text
sigma <= Re rho < sigma + eta
```

and a dyadic shell `T <= |Im rho| < 2*T`, the middle-range centered-cubic
multiplier is bounded by a fixed constant.  The coefficient square mass is
therefore bounded by

```text
C * x^(2*(sigma+eta))
  * T^(q(sigma)-2+theta)
  * (1 + log T)^(5+r).
```

Here:

```text
q(sigma) = 4*sigma*(1-sigma),
Carlson + multiplicity log loss = 5,
Occupancy log loss = r,
Occupancy polynomial loss = theta.
```

After division by the squared target amplitude, the right-end energy exponent
at `x <= Y^lambda`, `T = Y^gamma`, is

```text
F_right
  = 2*lambda*(sigma + eta - beta)
    + gamma*(q(sigma)-2+theta).
```

For a strip strictly to the left of the target, the maximum normalization is
at the left endpoint and the corresponding exponent is

```text
F_left
  = 2*(sigma + eta - beta)
    + gamma*(q(sigma)-2+theta).
```

The numerical module must prove `F <= -delta` with `delta > 0`.  A statement
with `F <= 0` is insufficient.

## Energy versus norm exponents

Suppose one block satisfies

```text
energy_k
  <= C * A^2 * W
     * T_k^a * (1 + log T_k)^p,

a <= -delta < 0.
```

Taking square roots gives the norm bound

```text
||R_k||_L2
  <= sqrt(C) * A * sqrt(W)
     * T_k^(a/2) * (1 + log T_k)^(p/2).
```

The division by two is intrinsic when converting energy to norm.  It is not an
arbitrary weakening of the numerical margin.

For `T_k = 2^k*T0`, Minkowski gives

```text
||sum_k R_k||_L2 <= sum_k ||R_k||_L2.
```

Since `a/2 < 0`, the dyadic norm series converges with the exact norm exponent
`a/2` and exact log exponent `p/2`:

```text
sum_k T_k^(a/2) * (1 + log T_k)^(p/2)
  <= C_dyadic(delta,p)
     * T0^(a/2) * (1 + log T0)^(p/2).
```

Squaring the resulting norm estimate returns

```text
energy(total)
  <= C_total * A^2 * W
     * T0^a * (1 + log T0)^p.
```

Thus cross-shell assembly preserves the original energy exponent `a` and log
power `p`.  It does not replace `a` by `a/2` in the final energy statement,
nor does it add an arbitrary logarithm.

At `a = 0`, the norm series does not decay and this assembly fails.  The
critical equality case must remain explicit in the numerical theorem.

## Combining finitely many real-part strips

Let the fixed real grid contain `J` strips, where `J` is independent of `Y`.
For strip contributions `R_j`, either Minkowski or finite Cauchy-Schwarz gives

```text
||sum_j R_j||_L2 <= sum_j ||R_j||_L2,

||sum_j R_j||_L2^2 <= J * sum_j ||R_j||_L2^2.
```

The factor `J` is a genuine constant.  It changes neither a polynomial
exponent nor a logarithmic exponent.  A moving grid whose size grows with
`log Y` would add a loss and is not the proposed interface.

If strip `j` has margin `delta_j > 0`, finiteness gives

```text
delta_grid = min_j delta_j > 0.
```

The Lean theorem should expose either the individual margins or the proof that
the computed finite minimum is positive.

## Low-height/main-set boundary

The Carlson theorem begins at a supplied height `T_min`.  Zeros below
`T_min` cannot be silently discarded: a zero with the same real part as the
target has the same `x^beta` growth and does not become a small remainder merely
because `Y` grows.

The assembly theorem should therefore accept a main set `S` from the protected
low-energy/half-isolated side and require a set identity of the form

```text
all relevant zeros
  = S disjoint_union complement_below_Tmin disjoint_union tail_above_Tmin.
```

One of the following must then be supplied externally:

- `S` contains every relevant zero below `T_min`;
- the below-`T_min` complement has its own strict L2-smallness theorem;
- the low-energy theorem already handles that complement as part of its packet.

The Carlson module must not design how `S` grows with `Y`.  It only proves that
deleting the supplied finite `S` cannot increase nonnegative square mass.

## Four-part strict-constant budget

Let

```text
margin = c_main - pi/2 > 0.
```

A convenient explicit allocation is to choose positive numbers

```text
eta_kernel,
eta_middle,
eta_contour,
eta_point
```

with

```text
eta_kernel + eta_middle + eta_contour + eta_point < margin.
```

Their roles are:

```text
eta_kernel:  C_h differs from 1 on the finite main cluster;
eta_middle:  Carlson/Occupancy L2 complement;
eta_contour: smoothed outer contour and omitted high zeros;
eta_point:   triangle-average scale conversion to x_point^beta.
```

The theorem chain should never replace the strict sum by `<= margin`.

For a symmetric allocation one may take

```text
eta_each = margin / 5,
```

so the four losses total `4*margin/5 < margin`.  The unused fifth provides a
strictness buffer and avoids repeated `epsilon/4` boundary equalities.

## Point extraction after triangle smoothing

Suppose the assembled smoothed quantity satisfies

```text
|triangleAverage E at x| > (pi/2 + eta_point) * A(x).
```

Because the triangle kernel is nonnegative with mass one, there exists
`x_point` in `[x*exp(-h), x*exp(h)]` such that

```text
|E(x_point)| > (pi/2 + eta_point) * A(x).
```

If

```text
A(x) = x^beta / |rho0|,
```

then

```text
A(x) >= exp(-beta*h) * A(x_point).
```

For sufficiently small `h`, the factor `exp(-beta*h)` consumes less than the
allocated `eta_point`, leaving a strict constant greater than `pi/2` at the
actual point.

## Proposed assembly statements

The transfer layer should expose theorem families equivalent to:

```text
l2_reverse_triangle_lower
l2_lower_implies_exists_point
finite_strips_l2_sum_le
dyadic_block_norm_summable_of_energyExponent_neg
dyadic_tail_energy_preserves_exponent
strictPiOverTwo_survives_l2Tail
strictPiOverTwo_survives_fourLosses
triangleWitness_preserves_targetScale
```

The final actual-zeta facade should take, rather than reprove:

```text
lowEnergy:
  ||M_S||_L2 >= c_main * A * sqrt(W),
  c_main > pi/2;

occupancy:
  block Gram/Schur bound;

carlsonCapacity:
  block multiplicity-square mass with exponent and log ledger;

explicitFormula:
  E = M_S + R_middle + R_contour after centered-cubic smoothing.
```

It should return an absolute-value point witness only after every loss has been
instantiated.

## Nonclaims

This assembly theorem does not:

- prove the protected low-zero energy result;
- prove half-isolated frequency separation or Occupancy;
- select or grow the main set `S`;
- establish the actual explicit formula decomposition;
- prove both signs;
- turn a critical zero exponent into decay;
- establish novelty merely from short-interval localization.
