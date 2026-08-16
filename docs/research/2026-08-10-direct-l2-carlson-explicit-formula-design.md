# Direct L2 Carlson Tail and Centered Cubic Explicit Formula

## Status and scope

This document fixes the next implementation boundary for the
Pintz-Carlson-explicit-formula route. It is a design artifact only. During the
current repository freeze it does not authorize a Lean build, push, or pull
request.

The implementation owns only new `ZeroDensityLayerBudget*` modules,
`ZeroForcingUnifiedTransfer.lean`, and their Contract/AxiomAudit files. It must
not modify or reprove:

- the Sharp pi-over-two lower bound;
- half-isolated Gram/Schur or frequency-separation theorems;
- final exceptional-set growth;
- `ZeroForcedOscillationComplementaryBound.lean`;
- VK-edge production modules.

The half-isolated side supplies an Occupancy or Schur estimate. This work
supplies actual zeta dyadic capacity, multiplicity control, parameter
feasibility, and the explicit-formula high-tail transfer.

## 1. Parameters that must remain distinct

The following exponents have different meanings and must not be identified by
notation or theorem statements.

- `gammaLow`: the existing low-layer detection height.
- `gammaHigh`: the existing balanced Carlson cut in the L1 two-height route.
- `gammaL2Left`: the direct-L2 cutoff for zeros with real part at most `beta`.
- `gammaL2Right`: the direct-L2 cutoff for zeros with real part at least
  `beta`.
- `alpha`: the outer contour height exponent, so `H = X^alpha`.
- `d`: the inverse smoothing-scale exponent, so `h = X^(-d)`.

The intrinsic direct-L2 parameter theorem uses an outer exponent independent
of the existing L1 theorem. A later compatibility theorem may share `alpha`,
but only under the resulting stronger numerical hypothesis. That stronger
hypothesis must not be presented as an intrinsic obstruction to direct L2.

More precisely, if a consumer insists on the existing L1 outer cap

```text
alpha < 2 * beta - 1,
```

then it must also fit the direct-L2 critical height below that cap. Under
`beta > 1/2` and `theta < 2`, this is the exact additional condition

```text
gammaStar(beta, lambda, theta) < 2 * beta - 1
iff
theta < 2 - 2 * lambda * (1 - beta) / (2 * beta - 1).
```

This condition is not implied by `theta < 4 * beta - 2` for every
`2/3 < beta < 1` and `1 <= lambda < 2`. For example, even at `theta = 0`, a
large `lambda` and `beta` close to `2/3` can violate the shared-cap condition.
Therefore the first direct-L2 theorem must use its own `alphaL2`. A theorem
that shares the existing L1 `alpha` must have a separate name and expose the
stronger assumption in its public signature.

For the short-interval specialization `lambda = 1 + epsilon` and polylogarithmic
Occupancy `theta = 0`, the shared-cap condition simplifies to

```text
epsilon < (3 * beta - 2) / (1 - beta).
```

The right side is positive exactly when `beta > 2/3`. Thus shortening the
oscillation interval from a fixed large power to `[Y, Y^(1+epsilon)]` is not
only cosmetic: it creates a quantitative range in which the L1 two-height
contour and the direct-L2 tail can use one outer height. For general `theta`,
the corresponding condition is

```text
epsilon <
  (2 - theta) * (2 * beta - 1) / (2 * (1 - beta)) - 1.
```

The implementation should expose both the independent-`alphaL2` theorem and
this optional shared-`alpha` short-interval corollary. It must not use the
corollary to weaken the intrinsic direct-L2 criterion.

Equivalently, the largest admissible short-interval increment is

```text
epsilonMax(beta, theta)
  = (2 * (3 * beta - 2) - theta * (2 * beta - 1))
      / (2 * (1 - beta)).
```

For `1/2 < beta < 1`, a positive shared-outer interval exists exactly when

```text
theta < 2 * (3 * beta - 2) / (2 * beta - 1).
```

The final shared-outer feasibility region is the intersection of this
condition with the intrinsic direct-L2 condition
`theta < 4 * beta - 2`. The two upper bounds agree at `beta = 3/4`; below that
point the positive-short-interval condition is stronger, while above it the
intrinsic direct-L2 condition is stronger. This comparison must be reported
explicitly rather than summarized as a generic Carlson impossibility.

## 2. Numerical core

For real `sigma`, define the Carlson density exponent

```text
q(sigma) = 4 * sigma * (1 - sigma).
```

For an interval `[X, X^lambda]`, Occupancy power `theta`, and a dyadic cutoff
`X^gamma`, define

```text
F_R(beta, lambda, theta, gamma, sigma)
  = 2 * lambda * (sigma - beta)
    + gamma * (q(sigma) - 2 + theta),

F_L(beta, theta, gamma, sigma)
  = 2 * (sigma - beta)
    + gamma * (q(sigma) - 2 + theta).
```

The right endpoint identity is

```text
F_R(..., 1) - F_R(..., sigma)
  = 2 * (1 - sigma) * (lambda - 2 * gamma * sigma).
```

Consequently, if `0 <= sigma <= 1` and `0 <= gamma < lambda / 2`, then the
worst right-strip exponent is attained at `sigma = 1`.

Define the critical right height

```text
gammaStar(beta, lambda, theta)
  = 2 * lambda * (1 - beta) / (2 - theta).
```

Under `lambda > 0`, `beta < 1`, and `theta < 2`, the endpoint exponent factors
as

```text
F_R(beta, lambda, theta, gamma, 1)
  = (2 - theta) * (gammaStar(beta, lambda, theta) - gamma).
```

The core theorem must prove the exact feasibility criterion

```text
exists gamma, 0 <= gamma and gamma < lambda / 2
  and F_R(beta, lambda, theta, gamma, 1) < 0
iff
theta < 4 * beta - 2.
```

This is both a sufficiency theorem and a necessity theorem. It prevents the
formal development from silently assuming that every Occupancy exponent can be
absorbed by choosing a larger height.

Let

```text
Delta = 4 * beta - 2 - theta,
gammaL2Right = (gammaStar + lambda / 2) / 2.
```

When `Delta > 0`, this witness satisfies

```text
0 < gammaL2Right < lambda / 2,
F_R(..., gammaL2Right, sigma) <= -lambda * Delta / 4
```

for every `sigma` in `[beta, 1]`.

For the left side, take

```text
gammaL2Left = 1 / 8,
etaLeft = (4 * (1 - beta)^2 + Delta) / 8.
```

The identity

```text
F_L(..., beta) - F_L(..., sigma)
  = 2 * (beta - sigma)
    * (1 + 2 * gammaL2Left * (1 - beta - sigma))
```

shows that, for `1/2 <= sigma <= beta < 1`,

```text
F_L(..., gammaL2Left, sigma) <= -etaLeft < 0.
```

### Critical boundary theorem

At `theta = 4 * beta - 2`, the implementation must expose both facts:

```text
gammaStar = lambda / 2,
F_R(beta, lambda, theta, lambda / 2, 1) = 0.
```

Moreover every `gamma < lambda / 2` has a positive endpoint exponent. Thus the
boundary cannot yield decay, and a logarithmic factor cannot repair it. No
downstream theorem may label this equality case as strictly feasible.

## 3. Fixed-grid specialization for polylogarithmic Occupancy

The first actual-zeta consumer uses

```text
theta = 0,
2/3 < beta < 1,
1 <= lambda < 2.
```

Set

```text
g = lambda * (1 - beta),
alpha = (1 + g) / 2,
gammaL2Right = (g + lambda / 2) / 2,
gammaL2Left = 1 / 8,
d = (1 - g) / 8.
```

Then

```text
0 < g < gammaL2Right < alpha < 1,
gammaL2Right < lambda / 2,
0 < d < alpha,
alpha - gammaL2Right = (2 - lambda) / 4,
F_R(..., gammaL2Right, 1) = -lambda * (beta - 1/2).
```

Use the fixed thresholds `j / 100` for `j = 52, ..., 99`. The bin containing
`beta` is split by a filter, not by introducing a moving Carlson certificate.
All Carlson certificates are therefore evaluated at a fixed finite set of real
parameters. Their eventual thresholds and constants can be synchronized by a
finite maximum and finite sum.

For a strip `(sigma, sigma + 1/100]`, replacing the real part by its upper
endpoint costs at most

```text
2 * lambda / 100 < 1 / 25
```

on the right and

```text
2 / 100 = 1 / 50
```

on the left. Before this strip loss, the right margin is greater than `1/6`
and the left margin is at least `5/36`. Zeros with real part at most `13/25`
are handled by the global zero-count layer, whose power margin is greater than
`2/5` in absolute value. Hence all three regions admit the common safe bound

```text
power exponent <= -1 / 20.
```

The fixed grid introduces no extra logarithmic factor.

## 4. Capacity input and multiplicity loss

For each fixed real threshold `sigma > 1/2`, the actual Carlson square-capacity
input has the form

```text
sum over a positive dyadic shell and a real strip of
  multiplicity(rho)^2 / |rho|^2
<= C_sigma * T^(q(sigma) - 2) * (1 + log T)^5.
```

The fifth logarithm has a fixed provenance:

- four logarithms from the classical Carlson density input;
- one logarithm from converting linear analytic multiplicity to square
  multiplicity using a local maximum-multiplicity bound.

Deleting a finite zero set `S` must use nonnegative-mass monotonicity. It must
not create a new density theorem or a new `S`-dependent Carlson certificate.

The half-isolated Occupancy input is allowed to have the form

```text
Occupancy(T) <= D * T^theta * (1 + log T)^r.
```

Multiplying capacity and Occupancy produces

```text
T^(q(sigma) - 2 + theta) * (1 + log T)^(5 + r).
```

For the coarse global layer, Riemann-von Mangoldt linear count plus local
maximum multiplicity gives instead

```text
T^(theta - 1) * (1 + log T)^(2 + r).
```

This smaller logarithmic power may be weakened to the common `5 + r` output.

## 5. Absolute-height blocks and positive Carlson shells

The explicit formula naturally groups zeros by absolute ordinate, while the
Carlson capacity is stated for positive shells. The bridge must:

- pair nonreal zeros using conjugation and multiplicity symmetry;
- send a zero strictly above the lower dyadic boundary to the current positive
  shell;
- send a zero exactly on the lower boundary to the preceding shell when the
  source convention requires it;
- absorb the preceding-shell rescaling and conjugate-pair square bound into one
  numerical constant smaller than `20`;
- preserve the polynomial exponent and logarithmic power exactly;
- preserve deletion of `S` by monotonicity.

This bridge belongs to the Carlson/transfer side. It must not introduce a new
Gram theorem.

## 6. Dyadic height summation

If a block exponent `e` is strictly negative, use the exact estimate

```text
sum over ell >= 0 of
  2^(ell * e) * (K + ell + 1)^p
<= (K + 1)^p
   * sum over ell >= 0 of 2^(ell * e) * (ell + 1)^p.
```

This keeps the complete negative exponent. The implementation must not replace
`e` by `e / 2` and must not add a dyadic-shell logarithm. In the fixed-grid
specialization, all strips use `e <= -1/20`, so a single summability constant
works for the finite family.

The resulting actual high-zero Gram tail has the target shape

```text
GramTail(X)
  <= C * X^(-1/20) * (1 + log X)^(5 + r).
```

This theorem consumes the half-isolated Occupancy interface but does not own
its proof.

## 7. Centered cubic explicit formula

The explicit-formula transfer must use the centered cubic multiplier

```text
C_h(s)
  = (exp(h*s) - 2 + exp(-h*s)) / (h^2 * s^2)
  = exp(-h*s) * ((exp(h*s) - 1) / (h*s))^2.
```

Existing cubic factorization and near-one modules should be reused rather than
defining a competing kernel. The required two-regime estimate is

```text
|C_h(s)| <= K * min(1, (h * |s|)^(-2)).
```

It has three separate uses:

- for each fixed target zero, `C_h(rho) -> 1`, preserving the scale
  `X^(Re rho) / |rho|`;
- for high zeros, the reciprocal-square Carlson capacity remains applicable;
- on the horizontal contour, the additional `(h*T)^(-2)` factor retains the
  cubic high-frequency gain.

The current facade requiring `h * (c + T) <= 1` is incompatible with the needed
regime `h*T -> infinity`. The implementation must use the raw third-order
contour theorem and expose a fixed-height wrapper. One selected good height
`T_X` must work simultaneously for every `x` in `[X, X^lambda]`, for
`x*exp(h)`, `x`, and `x*exp(-h)`, and for every contour edge used by the
centered difference.

With the polylogarithmic parameters above,

```text
h = X^(-d),
h*T = X^(alpha - d) -> infinity,
h*|rho_target| -> 0,
lambda*(1-beta) + 2*d - 2*alpha
  = -(3 + g) / 4 < 0.
```

Thus target preservation and contour decay are compatible in the same
parameter choice.

## 8. Exact triangle-average transfer

For

```text
F(x) = sum_n Lambda(n) * max(log(x/n), 0)^2 / 2,
```

the centered second difference must be proved exactly:

```text
(F(x*exp(h)) - 2*F(x) + F(x*exp(-h))) / h^2
  = integral from -1 to 1 of
      (1 - |u|) * psi(x*exp(h*u)) du.
```

The corresponding main term is

```text
x * C_h(1)
  = integral from -1 to 1 of
      (1 - |u|) * x*exp(h*u) du.
```

This exact identity avoids a sandwich bias. If the centered normalized average
has absolute value greater than `A`, nonnegative averaging gives a point
`z` in `[x*exp(-h), x*exp(h)]` with

```text
|psi(z) - z| / z^beta >= A * exp(-beta*h).
```

Since `h -> 0`, any strict constant greater than `pi/2` is retained. This gives
an absolute-value Omega conclusion only. An `Omega_+/-` conclusion requires a
separate sign or phase argument and must not be claimed here.

## 9. Constant-preserving L2 anti-cancellation

Let `w >= 0`, `W = integral w`, and `E = M + R`. The unified transfer layer
should expose the following assembly theorem:

```text
integral |M|^2 w > A^2 * W,
integral |R|^2 w < delta^2 * W,
C + delta < A
implies
exists t, |E(t)| > C.
```

Weighted Cauchy-Schwarz controls the L1 norm of `R` by `delta * W`. This avoids
losing the strict pi-over-two constant by replacing the lower bound with a
coarse square-root estimate. The theorem belongs in
`ZeroForcingUnifiedTransfer.lean` only after the actual high-tail theorem is
available.

## 10. Implementation and review slices

After the build and publication freeze is lifted, use the following order.

1. Add `ZeroDensityLayerBudgetDirectL2NumericalCore.lean` together with the
   first actual-zeta tail consumer. Do not publish the numerical core as an
   unconsumed facade.
2. Add the absolute-height-to-positive-shell bridge and fixed-grid actual
   Carlson/Occupancy tail theorem. Import half-isolated results read-only.
3. Add the centered cubic multiplier and fixed-uniform-good-height explicit
   formula wrapper.
4. Add the exact triangle-average identity and witness transfer.
5. Add the constant-preserving L2 assembly theorem to the unified transfer
   module.

Each review slice must include typed Contract examples for every public
definition and theorem, `#print axioms` for every public theorem, the project
allowlist update, a placeholder/diff audit, focused builds, and the complete
baseline on a fixed current-main base. No slice may claim an unconditional
Omega theorem until the external finite main-cluster decomposition is supplied
and the complete actual explicit-formula chain is connected.

## 11. Completion evidence

The direct-L2 high-tail stage is complete only when all of the following are
machine-checked on the same fixed head:

- the exact criterion `theta < 4*beta - 2`, including the equality failure;
- independent left and right strict exponent bounds;
- fixed-grid synchronization with no moving Carlson parameter;
- actual zeta square-multiplicity capacity after finite-set deletion;
- absolute-height shell conversion;
- Occupancy multiplication and dyadic summation with output log power `5+r`;
- the `X^(-1/20)` polylogarithmic specialization;
- centered cubic target preservation and contour decay;
- exact triangle averaging and strict-constant witness transfer;
- complete Contract, AxiomAudit, allowlist, and baseline evidence.

Until these items are connected, the work is a verified collection of
prerequisites rather than a completed unconditional Omega theorem.

## 12. Primary-source boundary audit

This is a scoped prior-art audit, not an exhaustive novelty claim.

- Johnston, *Zero-density estimates and the optimality of the error term in the
  prime number theorem*, arXiv:2411.13791v2, proves a generic
  zero-free-region plus zero-density upper transfer. Its proof truncates the
  explicit formula, applies the triangle inequality, and estimates the
  first-power zero mass `x^(Re rho - 1) / |Im rho|`. It does not use a
  multiplicity-square Gaussian high-tail estimate.
- Bellotti, *A new zero-density estimate for zeta(s) and the error term in the
  Prime Number Theorem*, arXiv:2508.02041v1, derives the optimal VK PNT upper
  error from a stronger near-edge density estimate. Its PNT application again
  begins with the absolute first-power zero sum and then uses
  Riemann-Stieltjes integration by parts. The paper's internal density proof has
  a quadratic form in selected zeros, but it is not an explicit-formula L2
  complement theorem with analytic multiplicity-square weights.
- Han, *The Error in a Smooth Weighted Prime Number Formula and Zero-free
  Regions for the Riemann Zeta Function*, arXiv:2505.23795v1, supplies a genuine
  reverse direction. It localizes a narrow zero rectangle with a Gaussian and
  applies Turan's power-sum method. The resulting lower contribution loses a
  factor of the form `exp(-epsilon * omega)` and is not a sharp pi-over-two
  short-interval theorem.
- Guth and Maynard, *New large value estimates for Dirichlet polynomials*,
  arXiv:2405.20552v2, improves the zero-count exponent through large-value
  estimates. Its zeta consequence is an unweighted zero-density bound; it does
  not itself supply the analytic-multiplicity-square explicit-formula tail
  required here.

The candidate new contribution is therefore not another implication
`zero-free region + zero density -> PNT upper bound`. It is the machine-checked
combination

```text
actual multiplicity^2 / |rho|^2 dyadic capacity
  + half-isolated Occupancy/Schur
  + centered cubic explicit formula
  + strict-constant L2 anti-cancellation
  -> a short-interval oscillation witness retaining a constant above pi/2.
```

The exact threshold `theta < 4 * beta - 2` and the shared-outer short-interval
threshold should be presented as consequences of this direct-L2 architecture,
not as claims that the underlying zero-density estimates are new. A broader
literature search is still required before claiming theorem-level novelty.
