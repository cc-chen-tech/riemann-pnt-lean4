# Direct-L2 actual-zeta soundness and gap certificate

Status: static theorem design.  This document is not build evidence and does
not assert that the final theorem has been formalized.

## Intended terminal theorem

The final lower-transfer theorem should have the following mathematical shape.
Fix an actual nontrivial zeta zero

```text
rho0 = beta0 + i*gamma0,     1/2 < beta0 < 1,
```

a requested interval exponent `epsilon > 0`, and a strict surplus `delta > 0`.
Assume the retained finite zero cluster has normalized Sharp main contribution
strictly larger than

```text
pi/2 + delta.
```

After choosing the cubic smoothing, two heights, finite real strips, and finite
dyadic shells, prove that there is an explicit threshold `Y0` such that every
`Y >= Y0` has a witness

```text
exists x in Set.Icc Y (Y^(1+epsilon)),
  abs (PNTError x) > (pi/2) * x^beta0 / abs rho0.
```

This is an absolute oscillation witness.  It is not, without additional sign
selection, an `Omega_plus` or `Omega_minus` theorem.

## Exact normalized decomposition

At logarithmic center `U = log X`, normalize the smoothed explicit formula by

```text
N(X) = abs rho0 * X^(-beta0).
```

The proof must establish an identity, not only an inequality,

```text
N(X) * SmoothedError(X,v)
  = RetainedMain(X,v)
  + MiddleZeros(X,v)
  + HighZeros(X,v)
  + ContourResidual(X,v)
  + RealAxisResidual(X,v)
  + TrivialZeroResidual(X,v).
```

The retained cluster is deleted from every residual zero sum.  The same cubic
kernel and the same deletion predicate must occur on both sides of the
identity.  A bound for a differently truncated or differently smoothed sum does
not prove this decomposition.

## Cross-term identity required by direct L2

For a middle zero `rho_j = beta_j + i*gamma_j`, put its center coefficient in
the form

```text
a_j(X) = multiplicity(rho_j) * X^(rho_j-beta0) * B_eta(rho_j),
```

with any fixed normalization factors made explicit.  The triangular average of
the squared middle sum has cross term

```text
a_i(X) * conj(a_j(X))
  * K_L((beta_i + beta_j - 2*beta0)
        + i*(gamma_i-gamma_j)).
```

Consequently the actual observation kernel is complex.  Replacing it by the
pure sinc-squared kernel is valid only when both real displacements vanish.
The required pointwise majorant is

```text
abs (K_L(a+i*d))
  <= exp(abs(a)*L) * min(1, 4/(L^2*(a^2+d^2))).
```

This identity is the soundness boundary between the actual-zeta L2 argument and
an abstract frequency model.

## Premise ledger

Each row is independently necessary.  `Existing input` means that the final
adapter may import the result after rechecking its exact current-main theorem
signature.  `Designed` means only that a proof and interface have been worked
out statically.  `External owner` means this task must consume the interface and
must not reprove it.

| ID | Premise | Owner/status | What it proves |
| --- | --- | --- | --- |
| P0 | Actual zeta zero and analytic multiplicity | Existing input | Every coefficient and deletion is attached to a genuine zeta zero |
| P1 | Finite zero collection in each bounded dyadic shell | Existing input | All shell sums and Schur matrices are finite |
| P2 | Carlson linear multiplicity shell capacity | Existing input; shell-mass integration reported merged | `sum multiplicity <= C*T^q*(log T)^4` in the required narrow strip |
| P3 | Local weighted occupancy | External owner: half-isolated | Uniform row mass after frequency localization |
| P4 | Multiplicity-weighted Schur inequality | Designed | Converts P2 and P3 into quadratic energy without a maximum-multiplicity factor |
| P5 | Complex triangular observation bound | Designed | Controls actual off-critical cross terms |
| P6 | Cubic low/high kernel bounds | Designed | Gives low-cluster fidelity and cubic high-tail decay |
| P7 | Dynamic real-strip and dyadic covers | Designed | Converts stripwise estimates into a finite actual range bound |
| P8 | Two-height strict exponent certificate | Designed | Gives strict decay for every `beta0 > 1/2` at the arithmetic level |
| P9 | Actual smoothed explicit-formula identity at outer height `X^alpha` | Missing production bridge | Identifies the PNT error with retained, middle, high, contour, real-axis, and trivial-zero terms |
| P10 | Actual contour/real-axis/trivial-zero normalized bounds for the cubic kernel | Missing production bridge | Makes every nonzero residual fit the threshold compiler |
| P11 | Retained-cluster Sharp surplus above `pi/2` | External owner: Sharp | Supplies the lower main term that Carlson alone cannot create |
| P12 | Explicit residual threshold compiler | Designed | Turns strict polynomial margins and log losses into one concrete `Y0` |
| P13 | Logarithmic-window to short-power-interval map | Designed | Places the witness inside `[Y,Y^(1+epsilon)]` |

The final theorem is unavailable until P9 and P10 are proved for the same
kernel used by P6 and the same truncation used by P7-P8.  Parameter feasibility
P8 alone says nothing about whether zeta has or lacks zeros with real part above
`1/2`.

## Norm and exponent ledger

The proof must retain the following distinctions.

### Middle zero range

For one real strip `[sigmaL,sigmaR]` and one dyadic height exponent `gamma`, the
energy exponent is

```text
E2 = 2*kappa*lambda*(sigmaR-beta0)
     + gamma*(q(sigmaL)-2),
q(sigma) = 4*sigma*(1-sigma).
```

The density contributes log-four and local weighted occupancy contributes one
additional logarithm.  Thus the energy loss is exactly log-five.  Taking a
square root changes both quantities:

```text
energy:  C_E * X^(-etaE) * (1+log X)^5,
norm:    sqrt(C_E) * X^(-etaE/2) * (1+log X)^(5/2).
```

For an integer-log compiler one may safely majorize the norm by log-three, but
must record that this is a deliberate rounding loss.  After the compiler, a
finite-strip envelope margin `rMiddle` yields the conservative norm rate
`rMiddle/8`.

### High zero range

The cubic kernel supplies height power three and smoothing cost `eta^(-2)`.
The strip exponent is

```text
EHigh = kappa*lambda*(sigmaR-beta0)
        + 2*d + gammaHigh*(q(sigmaL)-3),
```

with log-four from Carlson.  This is an L1 mass estimate, not an L2 energy
estimate.  It must never be square-rooted.

### Equality cases

An exponent equal to zero leaves log-four or log-five growth and therefore does
not imply decay.  Every residual routed to the threshold compiler must carry a
strictly positive polynomial rate.

## Multiplicity accounting

The middle energy begins with multiplicity squared on diagonal terms.  The
permitted reduction is weighted Schur:

```text
abs (sum i,j, m_i*m_j*a_i*conj(a_j)*K_ij)
  <= O * sum i, m_i*abs(a_i)^2,
```

where the row hypothesis already has linear multiplicity,

```text
sum j, m_j*A_ij <= O.
```

This consumes the Carlson linear-multiplicity mass directly.  The final ledger
may lose the occupancy logarithm, but must not insert

```text
max_j multiplicity(rho_j)
```

or a second density theorem.  Such a factor would change the advertised log
loss and could destroy a critical exponent calculation.

Deleting the retained finite cluster is harmless because all capacities and
majorants are nonnegative.  The deleted sum is bounded by the undeleted sum by
monotonicity; no density estimate may be reproved specifically for the finite
set.

## Explicit budget closure

Let the Sharp surplus be `delta`.  A valid fixed allocation is

```text
kernel distortion       <= delta/4
middle-zero L2 norm     <= delta/8
high-zero L1 mass       <= delta/8
contour residual        <= delta/8
real-axis residual      <= delta/8
trivial-zero residual   <= delta/8.
```

The total is `7*delta/8`, leaving strict final surplus `delta/8`.

For a term

```text
C * X^(-eta) * (1+log X)^ell,
```

with `eta > 0`, define

```text
K(eta,ell) = (1 + 2*(ell+1)/eta)^ell,
threshold(C,eta,ell,budget)
  = max 1 ((C*K(eta,ell)/budget)^(2/eta)).
```

The compiled threshold is the maximum of every term threshold and all
structural thresholds.  The final theorem must expose this maximum or a
definitionally equivalent quantity; an unspecified phrase such as
"for sufficiently large X" does not meet the explicit-transfer objective.

## Legal conclusion chain

Once P0-P13 are instantiated, the only permitted chain is:

```text
actual smoothed explicit-formula identity
  -> exact retained/residual decomposition
  -> retained normalized main > pi/2 + delta
  -> normalized residual <= 7*delta/8
  -> normalized actual error > pi/2 + delta/8
  -> normalized actual error > pi/2
  -> actual x-witness in [Y,Y^(1+epsilon)].
```

Carlson capacity enters only in the residual upper bound.  It does not prove
the main-term surplus and does not by itself rule out cancellation among the
retained zeros.

## Prohibited inference shortcuts

1. `beta0 > 1/2` plus arithmetic feasibility does not prove RH or exclude such
   a zero.
2. A finite cluster is not automatically noncancelling; P11 is essential.
3. A vanishing unnormalized residual is not enough; it must vanish after
   multiplication by `abs rho0 * X^(-beta0)`.
4. A reciprocal-height contour error leaving
   `X^(1-beta0)*(1+log X)^2` diverges after normalization and cannot be hidden
   inside P10.
5. A pure `1/abs(rho)^2` bound does not repair that contour error.  The cubic
   kernel or an equally strong smoothed contour estimate is required.
6. A pure sinc-squared Gram estimate is not the actual off-critical observation
   kernel unless the real displacements are zero.
7. An L1 square-half-height obstruction is not a general impossibility result
   for the direct-L2 route.
8. An absolute witness does not imply both signs.

## Next production proof obligation

The next genuinely central implementation is P9-P10, but it should begin only
after the deterministic PR1-PR3 interfaces are merged and their exact theorem
signatures are fixed.  Its proof must start from the production explicit
formula and derive the cubic second-difference identity term by term.  The
first review checkpoint is the identity itself; no residual estimate should be
accepted before the main, zero, real-axis, trivial-zero, and contour terms have
all been matched to that identity.

