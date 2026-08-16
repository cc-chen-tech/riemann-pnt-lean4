# Actual complex-triangle dyadic L2 theorem chain

## Scope

This note fixes the production-facing interface for the actual zeta
middle/high zero tail.  It is deliberately narrower than a general Carlson
framework.  The output is the `L2` energy budget needed by the direct Gate B
route.

Ownership is fixed as follows:

- this slice supplies signed dyadic shell mass, analytic-multiplicity weighted
  occupancy, the complex triangle-Laplace kernel, finite-set deletion, and the
  middle/high tail energy bound;
- half-isolated supplies Gram/Schur separation or Occupancy for the retained
  low cluster;
- Sharp supplies the retained-cluster lower energy and the sharp oscillation
  surplus.

This slice must not restate or reprove either of the latter two inputs.

## Actual normalized tail

Fix a target real part `beta0`, an observation interval

```text
[uMin, uMax] = [log X, lambda * log X],
```

and put

```text
u0 := (uMin + uMax) / 2,
L  := (uMax - uMin) / 2.
```

For a finite set `I` of distinct nontrivial zeta zeros, use one index per
distinct zero and put the analytic order into the coefficient:

```text
R_I(v)
  := sum rho in I,
       multiplicity(rho) / rho
         * exp ((rho - beta0) * (u0 + v)).
```

Zeros must not be repeated `multiplicity(rho)` times while also carrying the
multiplicity coefficient.

The normalized triangle weight is

```text
W_L(v) := (1 / L) * max (1 - |v| / L) 0.
```

For `L > 0`, it is nonnegative, supported on `[-L,L]`, and has integral one.
The shell energy is

```text
Energy(I) := integral v, W_L(v) * |R_I(v)|^2.
```

## Complex triangle-Laplace kernel

Define

```text
K_L(z) := integral v, W_L(v) * exp (z * v).
```

The exact identity is

```text
K_L(0) = 1,

K_L(z) = (exp (L*z) - 2 + exp (-L*z)) / (L^2 * z^2)
  for z != 0.
```

For `z = a + i*delta`, the two elementary bounds combine to

```text
|K_L(a + i*delta)|
  <= exp (|a| * L)
       * min 1 (4 / (L^2 * (a^2 + delta^2)))

  <= exp (|a| * L)
       * min 1 (4 / (L^2 * delta^2)),
```

where the last `min` is interpreted as `1` when `delta = 0`.

For actual energy cross terms, the kernel argument is

```text
z_ij
  := (Re rho_i + Re rho_j - 2 * beta0)
       + i * (Im rho_i - Im rho_j).
```

It is not merely `i * (Im rho_i - Im rho_j)`.  Replacing it by a pure sinc
kernel would silently assume equal real parts and is invalid for an actual
off-critical strip.

## Endpoint support factor

Set

```text
kappa_lambda(r) := r          if r <= 0,
                   lambda * r if 0 <= r.
```

For `r_i := Re rho_i - beta0` and `r_j := Re rho_j - beta0`,

```text
exp ((r_i + r_j) * u0) * exp (|r_i + r_j| * L)
  <= X^(kappa_lambda(r_i) + kappa_lambda(r_j)).
```

Therefore, if both zeros lie in a real-part strip with upper endpoint
`sigmaR`,

```text
exp ((r_i + r_j) * u0) * |K_L(z_ij)|
  <= X^(2 * kappa_lambda(sigmaR - beta0)) * A_L(i,j),
```

where

```text
A_L(i,j)
  := min 1 (4 / (L^2 * (Im rho_i - Im rho_j)^2))
```

with value `1` when the ordinate difference is zero.

The matrix `A_L` is symmetric and nonnegative.  Positive-semidefiniteness is
not needed for the upper bound.

## Signed dyadic shells

Use separate positive and negative shells:

```text
Shell(sign, T)
  := {rho : T <= sign * Im rho and sign * Im rho < 2*T}.
```

This avoids folding opposite signs into one local-frequency window.  The two
signs are combined only after each shell estimate, at the cost of an explicit
factor two.

For one real strip `[sigmaL,sigmaR]`, define

```text
I := zetaZeros
       intersect realStrip(sigmaL,sigmaR)
       intersect Shell(sign,T).
```

The actual Carlson input is linear analytic-multiplicity mass:

```text
sum rho in I, multiplicity(rho)
  <= Cdensity * T^(q(sigmaL)) * (1 + log T)^4,

q(sigma) := 4 * sigma * (1 - sigma).
```

No distinct-zero cardinality is substituted for this quantity.

## Weighted local row mass

Assume the actual local multiplicity theorem gives, uniformly in each signed
unit ordinate interval inside the shell,

```text
sum rho in localWindow, multiplicity(rho)
  <= Clocal * (1 + log T).
```

For `L >= 1`, partition the row around `Im rho_i` into:

- a near interval `|delta| < 1/L`, with mass at most `2*U(T)`;
- two annular intervals for each integer `k >= 1`, each with mass at most
  `U(T)` and kernel weight at most `4/k^2`.

Using

```text
sum k >= 1, 1 / k^2 <= 2,
```

one obtains the explicit row bound

```text
sum rho_j in I, multiplicity(rho_j) * A_L(i,j)
  <= 18 * U(T),

U(T) := Clocal * (1 + log T).
```

The constant `18` comes from

```text
2 + 2 * 4 * 2.
```

This argument permits several distinct zeros with the same ordinate; their
analytic multiplicities are consumed by `U(T)`.

## Multiplicity-weighted Schur step

For nonnegative weights `m_i`, a symmetric nonnegative envelope `A_ij`, and

```text
sum j, m_j * A_ij <= Occupancy
```

for every row, the elementary inequality

```text
2 * |a_i| * |a_j| <= |a_i|^2 + |a_j|^2
```

gives

```text
|sum i,j, m_i * m_j * a_i * conj(a_j) * K_ij|
  <= Occupancy * sum i, m_i * |a_i|^2
```

whenever `|K_ij| <= A_ij`.

Applied to the actual zero coefficients, and using

```text
|rho| >= |Im rho| >= T,
```

this yields

```text
Energy(I)
  <= 18 * U(T)
       * X^(2 * kappa_lambda(sigmaR - beta0))
       / T^2
       * sum rho in I, multiplicity(rho).
```

After Carlson:

```text
Energy(I)
  <= Cshell
       * X^(2 * kappa_lambda(sigmaR - beta0))
       * T^(q(sigmaL) - 2)
       * (1 + log T)^5.
```

Thus `multiplicity^2` in the expanded energy is controlled by the linear
Carlson mass without a separate maximum-multiplicity loss:

```text
log loss = 4 + 1 = 5,
```

not `4 + 1 + 1 = 6`.

## Finite deletion

For an arbitrary finite retained set `S`, replace `I` by `I \ S` before the
row-mass and Carlson steps.  Because all masses and the envelope `A_L` are
nonnegative,

```text
rowMass(I \ S) <= rowMass(I),
linearMass(I \ S) <= linearMass(I).
```

The same shell bound follows with the same constants.  No new zero-density or
local-multiplicity theorem is proved for `S`.

This is the only deletion mechanism required from the Carlson side.

## Dyadic middle/high tail

Let the lower tail height be

```text
H = X^gamma
```

and let the cubic contour truncate at `X^alpha`.  Decompose each sign into
shells

```text
T_n = 2^n * H,
```

stopping when `T_n` reaches the contour height.

Since `q(sigmaL) <= 1` on `1/2 <= sigmaL <= 1`,

```text
q(sigmaL) - 2 <= -1.
```

The geometric decay absorbs the polynomial growth of the logarithm:

```text
sum n,
  T_n^(q(sigmaL)-2) * (1 + log T_n)^5
  <= Cdyadic
       * H^(q(sigmaL)-2) * (1 + log H)^5.
```

This constant can be made completely explicit.  If `H >= 1` and
`q(sigmaL) <= 1`, then

```text
(2^n * H)^(q(sigmaL)-2) <= 2^(-n) * H^(q(sigmaL)-2),

1 + log (2^n * H)
  <= (1 + log H) * (n + 1).
```

The exact geometric moment is

```text
sum n >= 0, 2^(-n) * (n + 1)^5 = 2164.
```

Hence every finite initial dyadic sum, and therefore the infinite majorant,
satisfies

```text
sum n,
  (2^n * H)^(q(sigmaL)-2)
    * (1 + log (2^n * H))^5
  <= 2164 * H^(q(sigmaL)-2) * (1 + log H)^5.
```

Combining positive and negative signed shells costs exactly one further factor
two, so the sign-combined dyadic constant is `4328` before multiplying the
row-mass and Carlson constants.  This avoids an opaque summability constant in
the production statement.

Consequently the energy exponent of one finite real strip is

```text
Estrip
  := 2 * kappa_lambda(sigmaR - beta0)
       + gamma * (q(sigmaL) - 2).
```

The full output is

```text
MiddleHighEnergy(strip, sign, S)
  <= Ctail * X^Estrip * (1 + log X)^5.
```

The polynomial and logarithmic conclusions must be reported separately:

- `Estrip < 0`: the energy decays after absorbing the fixed log power;
- `Estrip = 0`: the remaining `(log X)^5` grows, so there is no decay;
- `Estrip > 0`: this estimate cannot make the shell negligible.

If the finite-strip construction gives `Estrip <= -eta`, then one may record

```text
energy = O(X^(-eta/2))
```

after reserving half the polynomial margin for `(log X)^5`.  The corresponding
root-mean-square amplitude is only

```text
RMS = O(X^(-eta/4)).
```

Energy and RMS exponents must not be conflated.

## Output consumed by the lower-bound side

The Carlson slice should expose only an energy budget of the form

```text
triangleEnergy (middleHighTail S) <= TailBudget X.
```

It should not assert pointwise smallness.  The integration layer combines it
with a retained-cluster statement supplied elsewhere, for example:

```text
triangleEnergy retainedCluster >= MainBudget X,
TailBudget X < MainBudget X.
```

Any deduction of a common witness point, a signed witness, or a sharp
`pi/2`-surplus belongs to that integration layer and requires the exact
lower-bound hypotheses.  Absolute `L2` smallness alone does not prove
`Omega_+` or `Omega_-`.

## Production theorem chain

The next implementation should be split into a deterministic kernel slice and
an actual-zeta adapter slice.

### Deterministic kernel slice

```text
complexTriangleLaplaceKernel_zero
complexTriangleLaplaceKernel_ne_zero
norm_complexTriangleLaplaceKernel_le
endpointSupport_pair_le
weightedSchur_of_rowMass
weightedTriangleEnergy_le
weightedRowMass_le_eighteen
```

### Actual-zeta adapter slice

```text
actualSignedDyadicShell
actualSignedDyadicShell_linearMultiplicity_le
actualSignedDyadicShell_rowMass_le
actualSignedDyadicShell_energy_le_linearMass
actualSignedDyadicShell_energy_le_carlson
actualSignedDyadicShell_energy_delete_le
dyadic_log_fifth_moment_eq
dyadic_power_log_fifth_sum_le
actualDyadicMiddleHighEnergy_le
actualDyadicMiddleHighEnergy_delete_le
actualDyadicMiddleHighEnergy_decay
```

Names are provisional.  Public theorem statements should quantify the
constants and thresholds explicitly instead of hiding them in an opaque
`hkernel` or an untyped asymptotic facade.

## Contract and axiom audit requirements

For every public definition, use a typed Contract example.  For every public
theorem, use both a typed Contract example and `#print axioms`.  The production
slice must contain no `sorry`, `admit`, or new project axiom.

The audit should confirm:

1. one index per distinct zero, with analytic multiplicity in the coefficient;
2. signed shells are estimated separately;
3. the kernel argument includes the sum of real offsets;
4. Carlson is applied to linear analytic-multiplicity mass;
5. weighted occupancy contributes one logarithm;
6. finite deletion uses monotonicity only;
7. the shell energy has reciprocal height squared;
8. `(log X)^5` is attached to energy, not RMS;
9. equality of the polynomial exponent is not called decay;
10. no Sharp, half-isolated, RH, or final oscillation conclusion is claimed.
