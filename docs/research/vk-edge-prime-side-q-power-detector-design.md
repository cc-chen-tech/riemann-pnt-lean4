# Prime-Side Q-Power Detector Design

## Status and scope

The algebraic detector and its coefficient-mass layer are now proved in Lean:

- `PrimeNumberTheorem/QPowerDetectorAlgebra.lean` constructs a real finite
  q-power detector, cancels the main node and prescribed real/conjugate-pair
  nodes, and normalizes its target response to `1`;
- `PrimeNumberTheorem/QPowerDetectorMass.lean` proves the exact half-weighted
  `L1` negative-mass identity and a factorized weighted-loss bound.

Both exact contracts and the dedicated/central axiom audits pass.  This still
does not close the repeatable Sharp lower bound required by Gate B.

The focused source, contract, dedicated audit, central audit, allowlist, and
static placeholder checks pass.  A final no-target `verify-baseline.sh` run did
not finish its full repository rebuild: it stopped with status `1` during
normal build progress near target `8515/9191`, without a reported Lean theorem
error in the captured tail.  This branch therefore does not claim a completed
full-repository baseline run.

The purpose is to construct a finite real Dirichlet polynomial that cancels
the zeta main pole and a prescribed finite set of already-used zero poles,
while retaining a normalized response at a new target zero.  The construction
must also expose the negative coefficient mass quantitatively.  Exact
annihilation without a strict response-minus-loss inequality is not success.

## Input data

Fix:

- a finite set `P` of complex points, closed under conjugation;
- a target point `s0` with `s0 != 1` and `s0` not in `P`;
- an integer base `q >= 2` such that
  `q^(-s0) != q^(-rho)` for every `rho` in `P`.

For the intended zeta application, `P` is the finite set of already-used zero
poles and `s0` is a new target zero.  Analytic multiplicity belongs to the
residue coefficient.  A single zero of the detector at `rho` kills the full
simple pole of `zeta'/zeta`, whose residue already records that multiplicity.

Write

```text
z_q(s) = exp (-s * log q).
```

Since a nontrivial zeta zero has real part different from `1`, the target node
cannot equal `q^(-1)`.  The remaining collision condition concerns points in
`P` with the same real part as `s0` and resonant imaginary difference.

## Algebraic construction

Define the annihilating polynomial

```text
D_q(z) = (z - q^(-1)) * product (rho in P) (z - z_q(rho)).
```

Conjugation closure of `P` implies that `D_q` has real coefficients.  It
satisfies

```text
D_q(q^(-1)) = 0,
D_q(z_q(rho)) = 0  for rho in P,
D_q(z_q(s0)) != 0.
```

Let `z0 = z_q(s0)` and `w = 1 / D_q(z0)`.  Choose a real polynomial of degree
at most one,

```text
R_q(z) = a + b z,
```

such that `R_q(z0) = w`:

- if `im z0 != 0`, take
  `b = im(w) / im(z0)` and `a = re(w) - b * re(z0)`;
- if `im z0 = 0`, real coefficients of `D_q` imply `w` is real, so take
  `a = w` and `b = 0`.

Then

```text
H_q(z) = D_q(z) * R_q(z)
A_q(s) = H_q(z_q(s))
```

has real coefficients and obeys

```text
A_q(1) = 0,
A_q(rho) = 0  for rho in P,
A_q(s0) = 1.
```

If `H_q(z) = sum_k c_k z^k`, then

```text
A_q(s) = sum_k c_k (q^k)^(-s).
```

Thus the support is the finite natural-number set
`{1, q, q^2, ..., q^degree(H_q)}`.

## Choosing a collision-free base

The first algebraic API will accept `q` together with the explicit
noncollision hypotheses.  The arbitrary-finite-set endpoint must additionally
prove that such an integer base can be chosen.

A finite candidate argument is available.  For a fixed forbidden point
`u != s0`, resonance at two distinct prime bases `p` and `r` would imply an
integer relation between `log p` and `log r`.  Unique factorization rules this
out.  Hence each forbidden point excludes at most one prime base.  More prime
candidates than forbidden points leave a valid base.

This prime-selection lemma is a separate theorem.  The detector construction
must not hide base noncollision inside an unproved choice.

### Mathematical base-selection result

The finite avoidance claim has now been proved on paper.  Let

```text
E = {rho in P | re rho = re s0},
M = card E.
```

Then any `M + 1` distinct prime candidates contain a prime `q` for which

```text
z_q(s0) != z_q(rho)  for every rho in P.
```

Indeed, different real parts already give different node moduli.  For a fixed
`rho` with the same real part, collision at two distinct primes would give

```text
(im rho - im s0) * log p = 2 * pi * k,
(im rho - im s0) * log r = 2 * pi * l
```

with nonzero integers `k,l`.  After making their signs positive this implies
`p^|l| = r^|k|`, contradicting uniqueness of prime powers.  Thus each old
point excludes at most one prime, and finite pigeonhole gives the result.

The candidate count `M + 1` is uniformly sharp without further information
about `P`.  This is a mathematical proof checkpoint, not yet a compiled Lean
theorem.  The Lean bottleneck is the conversion of the signed periodicity
witness from `Complex.exp_eq_exp_iff_exists_int` into positive natural
exponents for the prime-power argument.

## Negative mass and explicit bound

For `H_q(z) = sum_k c_k z^k`, define

```text
negativeMass(q, H_q) = sum_k max (-c_k) 0 / q^k,
weightedL1(q, H_q)   = sum_k |c_k| / q^k.
```

Because `A_q(1) = 0`, the existing main-pole identity gives the exact formula

```text
negativeMass(q, H_q) = weightedL1(q, H_q) / 2.
```

The compiled factorized estimate is

```text
polynomialWeightedL1At r H_q
  <= polynomialWeightedL1At r R_q
     * (r + q^(-1))
     * product (u in realNodes) (r + |u|)
     * product (z in pairNodes) (r + |z|)^2.
```

At the main node take `r = q^(-1)`, so the main factor contributes `2 / q`.
The conjugate-pair factor is bounded by `(r + |z|)^2`.  The interpolation
factor remains explicit on the right: a fully numerical bound additionally
requires a lower bound for `|D_q(z0)|` and an upper bound for the real linear
interpolator.  The exact finite negative mass remains the primary quantity;
the product theorem is a factorized certificate, not yet a strict
response-minus-loss result.

## Mathematical success gate

Normalization gives target response exactly `1`.  The later prime-side
contour argument must produce an explicit loss multiplier `L(P, s0, q)` such
that the signed contribution is bounded below by

```text
1 - L(P, s0, q) * negativeMass(q, H_q).
```

The route succeeds only after proving

```text
L(P, s0, q) * negativeMass(q, H_q) < 1.
```

Neither exact pole cancellation nor finiteness of the negative mass implies
this inequality.  If the coarse product estimate cannot establish it, the
next admissible refinement is to replace the linear normalizer by a bounded
degree real polynomial and minimize the weighted coefficient norm under the
same interpolation constraints.  A conditional theorem assuming the strict
inequality is not a completed Sharp result.

### No-free-shift audit

Multiplying the detector by a high power of `z` and renormalizing at `s0`
does make the algebraic negative mass decay like

```text
q^(-N * (1 - re s0)).
```

This does not improve the analytic response-to-loss ratio.  If
`H_N(z) = lambda_N z^N H(z)`, the exact Perron-side identity is

```text
P_(H_N)(q^N * X) = lambda_N * P_H(X).
```

At the same support-compatible scale,

```text
(q^N * X)^(1 - beta) * negativeMass(H_N)
  = X^(1 - beta) * negativeMass(H).
```

Thus the Perron multiplier exactly cancels the apparent mass improvement.
At a fixed observation scale the shifted prime-side detector eventually
vanishes, forcing the normalized target residue to be cancelled by other
residues or contour terms.  High degree alone is therefore not an admissible
optimization argument.

The future response theorem must be scale-aware.  For a concrete projected
detected quantity it must prove an inequality of the form

```text
Detected_H(x)
  >= kappa * x^beta
       - (log 4 + 4) * x * negativeMass(H)
       - E_H(x),
```

where `kappa > 0` comes from an explicit phase window and `E_H(x)` names every
remaining zero residue, trivial-zero term, horizontal/left-edge integral, and
truncation error.  The strict gate is

```text
kappa
  > (log 4 + 4) * x^(1 - beta) * negativeMass(H)
      + x^(-beta) * E_H(x).
```

A genuine gain must therefore come from signed prime correlation, a kernel
whose loss grows more slowly under dilation, contour cancellation, or an
already-effective bounded-support detector.  It cannot come from shifting the
support to larger q-powers.

## Planned theorem layers

The implementation should be split into independently auditable layers.

1. `QPowerDetectorAlgebra` -- **proved and audited**
   - define `z_q`, `D_q`, the real normalizer, `H_q`, and `A_q`;
   - prove real coefficients and exact vanishing/normalization;
   - prove the finite q-power Dirichlet expansion.

2. `QPowerDetectorMass` -- **proved and audited**
   - identify detector mass at `s = 1` with coefficient mass;
   - prove the exact half-weighted-L1 identity;
   - prove the explicit product bound.

3. `QPowerDetectorBaseSelection` -- **paper proof only**
   - prove finite prime-base avoidance;
   - remove the parameterized noncollision assumption.

4. `QPowerDetectorPrimeResponse` -- **not proved**
   - instantiate the detector in the real zeta contour formula;
   - state the actual loss multiplier, with every remainder term visible;
   - prove the strict response-minus-loss inequality or record its exact
     numerical/analytic failure.

Every compiled public endpoint has an exact contract and axiom audit.  The
generic algebra deliberately accepts every natural `q`; for `q = 1` the node
map is constant and target normalization cannot satisfy its nonvanishing
premise.  The real prime-side entry point must therefore require `1 < q` or
`Nat.Prime q`.  Only the fourth layer can supply the repeatable Sharp input
requested by Gate B.

## Failure rules

Stop and record a blocker if any of the following occurs:

- collision-free integer bases cannot be obtained with a quantitative bound;
- normalization forces an unbounded coefficient norm that makes the strict
  margin impossible;
- the real prime-side contour loss cannot be expressed in terms of the
  detector's negative mass;
- the best rigorous estimate gives
  `L * negativeMass >= 1` for the required zero configurations.

Do not replace a failed strict inequality with a new class, Prop wrapper, or
external hypothesis and present it as progress.

## Claim boundary

Even a completed algebraic detector would not by itself prove:

- a positive full-complement Gaussian energy after deleting arbitrary old
  zeros;
- a new zeta zero, a Carlson contradiction, or any iterative growth theorem;
- the Riemann hypothesis.

Gate B remains responsible for witness extraction, finite-set growth, and
Carlson stitching.  This branch owns only the detector construction and the
analytic response-minus-cancellation estimate.

The next Sharp endpoint is more specific than the detector algebra: for a
fixed true zeta zero with `beta > 2 / 3`, first prove a cofinal lower bound for
the genuine finite-zero complement energy with `S = empty`, keeping the outer
explicit-formula height `H = x^alpha` separate from the low detector height
`Y = x^gammaLow`.  Only after that should it be upgraded to arbitrary finite
`S`, with the dependence of the positive constant on `S` made explicit and
controlled.
