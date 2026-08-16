# Johnston, Bellotti, and Han novelty boundary

## Purpose

This note records what the named 2024--2025 papers already prove and narrows
the legitimate novelty claim for the Pintz--Carlson--explicit-formula project.

Primary sources:

- Daniel R. Johnston, *Zero-density estimates and the optimality of the error
  term in the prime number theorem*, arXiv:2411.13791v2:
  https://arxiv.org/abs/2411.13791
- Chiara Bellotti, *A new zero-density estimate for zeta(s) and the error term
  in the Prime Number Theorem*, arXiv:2508.02041v1:
  https://arxiv.org/abs/2508.02041
- Songlin Han, *The Error in a Smooth Weighted Prime Number Formula and
  Zero-free Regions for the Riemann Zeta Function*, arXiv:2505.23795v1:
  https://arxiv.org/abs/2505.23795
- Frederik Broucke, *On the connection between zero-free regions and the error
  term in the Prime Number Theorem*, arXiv:2507.13780v1:
  https://arxiv.org/abs/2507.13780

The statements below describe these versions.  Later revisions must be
checked before making a publication claim.

## Johnston: generic upper transfer is prior art

Johnston's Theorem 2.1 assumes:

```text
zero-free region:
  Re rho <= 1 - eta(|Im rho|),

zero density:
  N(sigma,t) << t^(A*(1-sigma)^B) * (log t)^C,

unique minimizer t0 of
  f_x(t) = eta(t) * log x + log t.
```

Writing

```text
omega(x) := f_x(t0),
```

the theorem gives a generic upper PNT error of the form

```text
Delta_i(x)
  << exp(-omega(x))
       * exp(2*A*omega(x)*(omega(x)/log x)^B)
       * omega(x)^C.
```

For the Vinogradov--Korobov region, the paper obtains

```text
Delta_i(x)
  << exp(-omega(x)) * (log x)^9 / (log log x)^3.
```

The proof uses the standard truncated explicit formula

```text
psi(x)
  = x - sum_{|Im rho| <= T} x^rho/rho
      + O(x*(log x)^2/T),
```

sets

```text
T = exp(2*omega(x)),
```

and applies the triangle inequality to the `L1` zero sum

```text
sum x^(Re rho - 1) / |Im rho|.
```

The zeros are split into three real-part ranges.  The near-one range is
estimated by the zero-free boundary and zero density through integration by
parts.

### Consequence for novelty

The following are not new by themselves:

- a generic zero-free-region plus zero-density upper transfer;
- minimizing `eta(t)*log x + log t`;
- a dynamically selected truncation height;
- real-part splitting of the zero sum;
- an essentially optimal VK-scale upper PNT error.

The present budget compiler may formalize and generalize the bookkeeping, but
it must treat Johnston's upper theorem as prior art and compare constants and
hypotheses explicitly.

## Bellotti: VK-edge density is an input, not our new estimate

Bellotti's Theorem 1.1 proves, in a strip

```text
sigma >= 1
  - K(T) / ((log T)^(2/3) * (log log T)^(1/3)),
```

with `K(T)` growing slower than a fixed power of `log log T`, that

```text
N(sigma,T)
  << exp(B*(log log T)^alpha) * K(T)
  = o(log T).
```

Theorem 1.2 specializes this to

```text
N(sigma,T) = O(1)
```

inside any fixed constant enlargement of the VK zero-free edge.  Theorem 1.3
makes the dependence exponential in that fixed enlargement parameter.  The
PNT consequence, Theorem 1.5, is

```text
Delta(x) << exp(55*A0) * exp(-omega(x)),
```

so the epsilon loss is removed.

The zero-density proof itself contains diagonal and off-diagonal quadratic
forms over a selected zero set.  This is part of the proof of the density
input; it is not a direct `L2` estimate for the actual PNT zero complement
after deleting a retained cluster.

### Consequence for novelty

The following are not available novelty claims:

- a new VK-edge zero-density estimate, unless one actually improves
  Bellotti's theorem;
- removal of epsilon from the optimal VK PNT upper error;
- bounded zero count in a fixed VK-edge strip.

Bellotti's density theorem should instead be an optional stronger instance of
the linear analytic-multiplicity mass consumed by the upper-layer compiler.
The Carlson power-density instance remains useful away from the VK edge and in
the direct-L2 complement.

## Han: bidirectionality and smooth weighting are prior art

Han studies the exponentially smoothed error

```text
Delta(x) := sum_n (Lambda(n) - 1) * exp(-n/x).
```

The explicit formula is

```text
Psi(x)
  = x - sum_rho Gamma(rho) * x^rho
      - log(2*pi) + O(1/x).
```

Han's Theorem 1.1 is already bidirectional:

- a zero-free region implies a smooth weighted PNT error upper bound;
- a sufficiently strong smooth weighted PNT error bound implies the
  corresponding zero-free region.

The upper rate is governed by the same infimum shape

```text
inf_t (eta(t) * log x + log t).
```

For the reverse/lower direction, Han fixes a zero

```text
rho0 = beta0 + i*gamma0
```

and uses a Mellin transform, Gaussian smoothing, a contributing zero
rectangle, and Turan's power-sum method.  Lemma 2.3 gives an averaged lower
bound with principal scale

```text
x^beta0 / gamma0
```

but with an epsilon-dependent loss.  In the proof this appears through a
short multiplicative average of `|Delta(u)|` and a factor of the form

```text
(x^delta0 * gamma0)^(-epsilon).
```

Theorem 1.1 then uses this lower mechanism to recover a zero-free region from
the assumed smooth error rate.

### Consequence for novelty

The following are not new by themselves:

- a smooth weighted explicit formula;
- a bidirectional error/ZFR theorem;
- a zero-driven lower bound for a smooth PNT error;
- use of a localized contributing zero rectangle;
- use of an averaged error norm to obtain a reverse implication.

Han's theorem does not supply the specific production interface currently
targeted here:

- the cubic centered second-difference kernel used for both the retained
  cluster and its actual complement;
- analytic-multiplicity weighted Schur control of a direct PNT `L2` tail;
- deletion of the same arbitrary finite retained set without redoing density;
- a finite real-strip/dyadic energy ledger with explicit log losses;
- preservation of a strict constant greater than `pi/2` at the exact
  `x^beta0/|rho0|` scale;
- a machine-checked primal/dual height certificate.

These differences are potential contribution boundaries, not proof that no
other paper contains them.

## Broucke: unified upper/lower sharpness exists in the Beurling setting

Broucke works with general Beurling zeta functions satisfying an Axiom A type
integer-counting hypothesis.  The paper explicitly builds on Pintz, Johnston,
and Revesz.

Theorem 1.5 refines the upper Pintz--Revesz transfer for broad regularly or
slowly varying zero-free contours.  Its optimizer is again the unique minimum
of

```text
h(u,x) := f(u) * log x + u.
```

Thus the general connection

```text
zero-free contour -> near-optimal PNT upper remainder
```

and its refined secondary term are already treated beyond the ordinary
Riemann zeta function.

Theorem 1.6 constructs Beurling systems whose zeta functions have infinitely
many zeros on a prescribed contour, none to its right, and whose PNT error has
a matching `Omega_+-` lower order up to the secondary term.  The construction
arranges zeros for constructive interference on a selected sequence.  The
paper also notes that zeros can instead be arranged destructively and proves
that the epsilon in the general lower Pintz--Revesz theorem cannot simply be
removed.

### Consequence for novelty

The following broad claims are already unavailable:

- the first framework containing both upper and lower transfer directions;
- the first sharpness comparison between a zero-free contour and PNT error;
- the first construction showing that a boundary zero configuration can force
  PNT oscillation;
- the first recognition that zero-cluster cancellation is a genuine obstacle;
- a universal epsilon-free lower transfer for arbitrary zeta-like systems.

The current target is materially different only if it remains specific and
stronger in its own direction:

- actual Riemann zeta zeros, not a constructed Beurling system;
- an arbitrary finite retained maximal-real-part cluster inside one exact
  explicit formula;
- a multiplicity-weighted direct `L2` bound for the actual complement;
- exact finite deletion and log-loss accounting;
- a strict `pi/2` surplus at `x^beta0/|rho0|`;
- machine-checked kernel and height certificates.

Broucke's destructive-interference examples reinforce the rule that a generic
transfer layer cannot manufacture a sharp surplus.  That surplus must be an
explicit hypothesis supplied by the actual retained-cluster theorem.

## Exact comparison table

```text
feature                    Johnston Bellotti Han Broucke present target
----------------------------------------------------------------------------
generic upper transfer      yes      input/PNT yes yes   yes
VK epsilon-free optimum     no       yes       no  no    consume, not claim
smooth PNT <-> ZFR          no       no        yes no    consume/compare
zero-driven lower route     cited    no        yes yes*  yes
matching sharpness example  no       no        no  yes*  not claim
same cubic kernel low/high  no       no        no* no    target
direct actual-PNT L2 tail   no       no        no  no    target
analytic multiplicity Schur no       no        no  no    target
finite retained deletion    no       no        no  no    target
strict pi/2 surplus         no       no        no  no    target input/output
exact x^beta/|rho| no eps   no       no        no  no    target
machine-checked dual        no       no        no  no    target
```

`no*` means Han uses a different exponential/Gamma smoothing kernel; it is not
a claim that Han has no low/high decomposition of any kind.

`yes*` means Broucke's lower route and sharpness construction are for Beurling
systems and do not themselves give the actual-zeta direct-L2 complement sought
here.

## Defensible contribution statement

A defensible future statement, after formal completion and a broader
literature check, is:

> We give a machine-checked, norm-typed transfer architecture in which actual
> explicit-formula kernels instantiate a common dynamic layer budget.  The
> upper assembler recovers zero-free-region/density PNT bounds, while the lower
> assembler combines a retained finite zero-cluster energy lower bound with an
> analytic-multiplicity weighted direct-L2 Carlson complement and a cubic
> high-frequency tail.  Finite deletion, logarithmic losses, optimal-height
> certificates, kernel distortion, and the strict oscillation surplus remain
> explicit throughout.

This statement must not be strengthened to "first bidirectional theorem",
"first optimal PNT error", "new VK density", or "proof of RH".

## Remaining literature audit

Before any novelty claim, compare the completed theorem against:

- Pintz's original upper and lower transfer theorems;
- Revesz's sharp and generalized-system results;
- Schlage-Puchta's short-interval oscillation theorem;
- Brent--Platt--Trudgian mean-square zero-tail estimates;
- Zhao's off-critical PNT mean square;
- later revisions and citations of the three papers above.

The theorem statement, not the architecture diagram, is the unit of novelty.
