# Q-power detector scale barrier

## Verified theorem

Let `p` be a real polynomial of degree at most `N`, and define

```text
A(s) = p(q^(-s)),  q >= 2.
```

Assume

```text
A(s0) = 1,
A(1) = 0,
Re(s0) < 1.
```

The compiled endpoint

```text
qPowerDetector_supportCompatible_negativeMass_loss
```

proves that for every `x > 0` with `q^N <= x`,

```text
x^Re(s0) / 2 <= x * polynomialNegativeMassAt (1 / q) p.
```

The result is independent of the particular annihilating polynomial and of
the old zeros used to construct it.

## Why the lower bound is unavoidable

At the target node,

```text
1 = |p(q^(-s0))|.
```

The triangle inequality and `degree p <= N` give

```text
1 <= (|q^(-s0)| / q^(-1))^N * weightedL1(1 / q, p).
```

Since `A(1) = 0`, the positive and negative weighted coefficient masses are
equal.  Hence

```text
negativeMass(1 / q, p)
  >= (1 / 2) * q^(-N * (1 - Re(s0))).
```

When the whole q-power support is visible at scale `x`, namely `q^N <= x`,
the right side is at least `(1 / 2) * x^(Re(s0) - 1)`.  Multiplication by the
elementary `O(x)` prime-side bound produces the displayed `x^Re(s0) / 2`
loss.

## Consequence for the Sharp route

A normalized zero residue has scale

```text
x^Re(s0) / |s0|.
```

Therefore a proof which handles negative detector coefficients only by
coefficientwise positivity and an `O(x)` bound cannot make the error smaller
than the target residue uniformly in the zero height.  Increasing the degree
or shifting the q-power support does not repair this while `q^N <= x`.

This closes the previously informal no-free-shift warning with an exact Lean
inequality.  In particular, the algebraic q-power annihilator by itself cannot
supply the arbitrary-`S`, cofinal right-higher Sharp lower bound.

## What remains viable

The theorem does not rule out a detector argument using genuinely stronger
arithmetic cancellation.  A surviving route must provide at least one of:

1. a signed prime correlation whose loss is strictly smaller than the
   coefficientwise `x * negativeMass` bound;
2. a smoothing or higher-order Perron kernel that preserves the target
   `1 / |s0|` response while gaining the same factor on the negative part;
3. an independent arithmetic lower bound which cannot be carried solely by
   the already-recorded finite zero packet.

The next Sharp theorem must state one of these gains quantitatively before it
can be connected to `rightHigherExclusionSet`.

## Claim boundary

This branch proves a detector obstruction.  It does not prove positive
right-higher complement energy, a new zeta zero, a Carlson contradiction, a
zero-free half-plane, or RH.
