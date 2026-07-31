# Prime-Side Q-Power Detector Design

## Status and scope

This document fixes the design for the next Sharp-oscillation experiment.  It
does not assert that the detector exists in Lean yet, and it does not close the
repeatable Sharp lower bound required by Gate B.

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

The polynomial product gives the explicit coarse estimate

```text
weightedL1(q, H_q)
  <= (|a| + |b| / q)
     * (2 / q)
     * product (rho in P) (1 / q + |z_q(rho)|).
```

Here the factor `2 / q` comes from the main-pole factor
`z - q^(-1)`.  All quantities on the right are determined by `P`, `s0`, and
`q`.  The exact finite negative mass is retained as the primary quantity; the
product bound is only a closed-form certificate.

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

## Planned theorem layers

The implementation should be split into independently auditable layers.

1. `QPowerDetectorAlgebra`
   - define `z_q`, `D_q`, the real normalizer, `H_q`, and `A_q`;
   - prove real coefficients and exact vanishing/normalization;
   - prove the finite q-power Dirichlet expansion.

2. `QPowerDetectorMass`
   - identify detector mass at `s = 1` with coefficient mass;
   - prove the exact half-weighted-L1 identity;
   - prove the explicit product bound.

3. `QPowerDetectorBaseSelection`
   - prove finite prime-base avoidance;
   - remove the parameterized noncollision assumption.

4. `QPowerDetectorPrimeResponse`
   - instantiate the detector in the real zeta contour formula;
   - state the actual loss multiplier, with every remainder term visible;
   - prove the strict response-minus-loss inequality or record its exact
     numerical/analytic failure.

Every public endpoint requires an exact contract and axiom audit.  The first
three layers are algebraic infrastructure.  Only the fourth layer can supply
the repeatable Sharp input requested by Gate B.

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
