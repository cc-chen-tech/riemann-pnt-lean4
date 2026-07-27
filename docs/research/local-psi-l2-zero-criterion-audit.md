# Local psi L2 zero criterion: upper-bound audit

## Proved endpoint

For fixed `epsilon > 0`, define

```text
M_epsilon(Y) =
  integral over [log Y, (1 + epsilon) log Y]
    of |psi(exp y) - exp y|^2 dy.
```

The Lean endpoint `LocalPsiL2ExponentAtMost epsilon theta` says that

```text
M_epsilon(Y) = o(Y^(2 beta) log Y)
```

for every `beta > theta`. The proved converse excludes every
positive-ordinate zeta zero with

```text
Re rho > max(theta, 1/2).
```

At `theta = 1/2`, conjugation and critical-line reflection put every
non-real nontrivial zero on the critical line. The remaining real-axis case
is an explicit premise of the conditional RH endpoint.

## Why the current unconditional PNT error does not close the criterion

The strongest unconditional pointwise input currently on `main` has the
classical shape

```text
|psi(x) - x| <= C x exp(-c sqrt(log x)).
```

Writing `L = log Y`, its direct use on
`y in [L, (1 + epsilon) L]` gives only

```text
M_epsilon(Y)
  <= C_epsilon L
       exp(2 (1 + epsilon) L - 2 c sqrt L).
```

Against the scale forced by a zero `rho = beta + i gamma`, the quotient is
bounded only at the scale

```text
exp(2 (1 + epsilon - beta) L - 2 c sqrt L).
```

For every `beta < 1` and every fixed `epsilon > 0`, the positive linear term
dominates the square-root saving. This estimate therefore does not tend to
zero and cannot feed `LocalPsiL2ExponentAtMost epsilon (1/2)`.

The qualitative PNT statement `psi(x) - x = o(x)` is also insufficient:
it has no rate capable of overcoming the same right-endpoint exponent.

## Why Carlson does not yet produce a contradiction

Carlson bounds the number of zeros to the right of a vertical line. The new
lower bound concerns the nonnegative arithmetic quantity

```text
integral |psi(exp y) - exp y|^2 dy.
```

A zero-count upper bound alone supplies no upper bound for this integral.
Turning density information into such an upper bound requires additional
cancellation in the explicit formula, including control of cross terms and
truncation tails. That analytic bridge is not present in the repository.

## Exact remaining mathematical input

One of the following would advance the chain:

1. An unconditional estimate proving
   `LocalPsiL2ExponentAtMost epsilon theta` for some `theta < 1`.
   This would exclude positive-ordinate zeros with real part greater than
   `max(theta, 1/2)`.
2. The critical estimate
   `LocalPsiL2ExponentAtMost epsilon (1/2)`.
   Together with the elementary real-axis nonvanishing bridge, the proved
   endpoint yields RH.
3. A density-to-arithmetic-mean-square theorem converting Carlson-type zero
   counts plus explicit-formula cancellation into the first estimate.

Item 2 is already RH-strength. The non-circular research target is item 3,
or a new direct arithmetic mean-square upper bound that does not assume RH.

