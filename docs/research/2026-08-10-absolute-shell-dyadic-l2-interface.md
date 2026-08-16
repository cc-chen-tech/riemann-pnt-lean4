# Absolute-height Carlson shells for the direct-L2 tail

## Scope and ownership

This note fixes the interface between the Carlson capacity side and the
half-isolated Gram/Schur side.  It is deliberately narrower than a complete
oscillation theorem.

The Carlson side provides:

- a positive-height dyadic shell count with analytic multiplicity;
- a local maximum multiplicity bound;
- a square-multiplicity weighted shell mass;
- an absolute-height shell version;
- monotonicity after deleting a finite set;
- a dyadic summation theorem that preserves the polynomial exponent.

The half-isolated side provides:

- frequency separation or a Schur row bound;
- Occupancy;
- the conversion from coefficient square mass to high-zero L2 energy.

No Gram matrix statement belongs in the Carlson module, and no zero-density
statement should be reproved in the half-isolated module.

## Endpoint conventions

For `T > 0`, use the following mathematical sets:

```text
A(T) = {rho : T <= |Im rho| and |Im rho| < 2*T},
P(T) = {rho : T < Im rho and Im rho <= 2*T}.
```

The asymmetric endpoints are intentional.  If `rho` is in the positive half
of `A(T)`, then either

```text
T < Im rho <= 2*T,
```

so `rho` is in `P(T)`, or `Im rho = T`, in which case `rho` is in
`P(T/2)`.  Hence

```text
A(T) intersect {Im rho > 0} subset P(T) union P(T/2).
```

This removes any hidden assumption that zeros do not occur exactly at dyadic
boundaries.

The abstract bridge theorem should accept a conjugation involution `conjZero`
such that

```text
Im(conjZero rho) = -Im rho,
multiplicity(conjZero rho) = multiplicity(rho),
weight(conjZero rho) = weight(rho).
```

For nontrivial zeta zeros, the real-axis case is separately empty.  Then the
absolute-height mass satisfies

```text
mass(A(T))
  <= 2 * (mass(P(T)) + mass(P(T/2))).
```

The proof uses only a partition by the sign of the ordinate, conjugation, and
nonnegativity.  It must not invoke a new density estimate.

## Linear analytic multiplicity to square multiplicity

Let `m(rho)` be analytic multiplicity and `w(rho) >= 0`.  The elementary
capacity lemma is

```text
(forall rho in B, m(rho) <= M)
  -> sum_{rho in B} m(rho)^2 * w(rho)
     <= M * sum_{rho in B} m(rho) * w(rho).
```

Its pointwise proof is exactly

```text
m(rho)^2 * w(rho) <= M * m(rho) * w(rho).
```

No cardinality interpretation of analytic multiplicity is required.

For a positive shell `P(T)` and `w(rho) = 1 / |rho|^2`, the height condition
gives

```text
w(rho) <= 1 / T^2.
```

Therefore

```text
sum_{rho in P(T)} m(rho)^2 / |rho|^2
  <= M(T) / T^2 * sum_{rho in P(T)} m(rho).
```

The actual zeta specialization should consume precisely these two inputs:

```text
sum_{rho in P(T), Re rho >= sigma} m(rho)
  <= C_count * T^q(sigma) * (1 + log T)^4,

max_{rho in P(T)} m(rho)
  <= C_mult * (1 + log T),

q(sigma) = 4 * sigma * (1 - sigma).
```

It then returns

```text
sum_{rho in P(T), Re rho >= sigma} m(rho)^2 / |rho|^2
  <= C_count * C_mult
     * T^(q(sigma) - 2)
     * (1 + log T)^5.
```

The audit ledger is:

```text
polynomial exponent: q(sigma) - 2
Carlson log loss:    4
multiplicity loss:   1
total log loss:      5
```

## Removing a finite main cluster

For every finite set `S`, define the complementary shell by set difference.
Since every summand is nonnegative,

```text
sum_{rho in A(T) \ S} m(rho)^2 * w(rho)
  <= sum_{rho in A(T)} m(rho)^2 * w(rho).
```

The theorem should be stated for an arbitrary finite `S`, without any
separation, closure under conjugation, or density assumption on `S`.

This is the only deletion theorem needed by the Carlson layer.  Any special
structure of the low-zero cluster belongs to the low-energy theorem.

## Explicit constant for the absolute-shell bridge

Write

```text
a = q(sigma) - 2.
```

For `1/2 <= sigma <= 1`, one has

```text
0 <= q(sigma) <= 1,
-2 <= a <= -1.
```

Assume `T >= 2` and

```text
mass(P(U)) <= C * U^a * (1 + log U)^5
```

at both `U = T` and `U = T/2`.  Then

```text
(T/2)^a = 2^(-a) * T^a <= 4 * T^a,
1 + log(T/2) <= 1 + log T.
```

The endpoint and conjugation bridge gives

```text
mass(A(T))
  <= 2 * C * (1 + 4) * T^a * (1 + log T)^5
  = 10 * C * T^a * (1 + log T)^5.
```

Using `20*C` is acceptable if the actual-zeta facade needs one additional
boundary split, but that factor must be justified explicitly.  The bridge is
not allowed to change `a` or the logarithmic power `5`.

After a nonnegative Occupancy bound

```text
Occ(T) <= C_occ * T^theta * (1 + log T)^r,
```

the L2 block contribution is at most

```text
10 * C * C_occ
  * T^(q(sigma) - 2 + theta)
  * (1 + log T)^(5 + r).
```

Thus the exact polynomial exponent delivered to the numerical feasibility
module is

```text
a_L2(sigma) = q(sigma) - 2 + theta.
```

## Dyadic summation without exponent loss

Let

```text
T_k = 2^k * T0,
a <= -delta < 0,
p in Nat,
L0 = 1 + log T0,
T0 >= 1.
```

Then

```text
T_k^a * (1 + log T_k)^p
  = T0^a * 2^(a*k) * (L0 + k*log 2)^p.
```

Since `L0 >= 1`,

```text
(L0 + k*log 2)^p
  <= L0^p * (1 + k*log 2)^p,
```

and since `a <= -delta`,

```text
2^(a*k) <= 2^(-delta*k).
```

Consequently

```text
sum_{k >= 0} T_k^a * (1 + log T_k)^p
  <= C(delta,p) * T0^a * (1 + log T0)^p,

C(delta,p)
  = sum_{k >= 0} 2^(-delta*k) * (1 + k*log 2)^p.
```

The constant is finite because a polynomial times a geometric sequence is
summable.  This preserves the exact exponent `a`; there is no replacement of
`a` by `a/2` and no extra logarithm.

At `delta = 0`, this argument fails and the series does not decay.  Every
caller must therefore supply a strict negative margin, not merely `a <= 0`.
For a finite dyadic range the equality case can at best accumulate an extra
number-of-shells factor; it does not prove a normalized `o(1)` tail.

## Fixed-grid caller contract

For a real-part strip

```text
sigma <= Re rho < sigma + eta,
```

the explicit-formula numerator is bounded at the right strip endpoint, while
Carlson is invoked at the left endpoint.  The caller therefore supplies the
strict normalized exponent

```text
2 * lambda * (sigma + eta - beta)
  + gamma * (q(sigma) - 2 + theta)
  <= -delta.
```

The shell module must not hide the width `eta`.  For the intended fixed grid,
`eta = 1/100`; the numerical core owns the proof that a common `delta > 0`
survives all strips.

The coarse layer `Re rho <= 13/25` should use a separate global zero-count
bound, with exponent

```text
theta - 1
```

and logarithmic power `2 + r`.  It should not be forced through a Carlson
strip theorem whose hypotheses are designed for `sigma > 1/2`.

## Lean-facing theorem signatures

The implementation should expose theorem families equivalent to:

```text
linear_to_square_mass
  (h_nonneg : forall rho in B, 0 <= w rho)
  (h_mult : forall rho in B, m rho <= M) :
  squareMass B m w <= M * linearMass B m w

positive_shell_square_mass_actual
  (hT : 2 <= T) (hsigma : 1/2 <= sigma) (hsigma1 : sigma <= 1) :
  squareMass (P T sigma) multiplicity reciprocalSquare
    <= C * T^(q sigma - 2) * (1 + log T)^5

absolute_shell_square_mass_actual
  (hT : 2 <= T) (hsigma : 1/2 <= sigma) (hsigma1 : sigma <= 1) :
  squareMass (A T sigma) multiplicity reciprocalSquare
    <= 10*C * T^(q sigma - 2) * (1 + log T)^5

absolute_shell_square_mass_delete
  (S : Finset Zero) :
  squareMass (A T sigma \ S) multiplicity reciprocalSquare
    <= squareMass (A T sigma) multiplicity reciprocalSquare

dyadic_tail_preserves_exponent
  (hdelta : 0 < delta) (ha : a <= -delta) :
  sum' (fun k => (2^k*T0)^a * (1 + log (2^k*T0))^p)
    <= C delta p * T0^a * (1 + log T0)^p.
```

Names and concrete zero-set types may follow the repository conventions, but
the assumptions and conclusions must remain visible.  In particular, a caller
must be able to audit `q(sigma)-2`, `+theta`, log `5+r`, and the strict margin
without unfolding an opaque facade.

## Nonclaims

This interface does not prove:

- Occupancy or frequency separation;
- a sharp low-zero energy lower bound;
- a pointwise explicit formula;
- the existence of a target zero;
- the final short-interval witness;
- impossibility of all Carlson-based L1 or L2 methods at a critical exponent.

It only supplies the actual-zeta capacity object required by the direct-L2
high-zero complement.
