# Ford incomplete-support moment: verified boundary

## Purpose

Ford's short-sum argument introduces an incomplete Vinogradov mean value that
retains only a consecutive window of power-sum equations.  The modules in this
slice formalize the finite modular Fourier identity underlying that object.
They are a reusable algebraic input, not the analytic estimate that completes
Ford's short-sum theorem.

The reference is Kevin Ford, *Vinogradov's integral and bounds for the Riemann
zeta function*, especially Lemma 5.1 and equations (5.3)--(5.4):
<https://arxiv.org/abs/1910.08209>.

## Proved in Lean

For the consecutive degree window `h, ..., h + d - 1`, the code defines the
modular system

```text
sum_i x_i^(h+j) = sum_i y_i^(h+j)  (mod Q),  0 <= j < d,
```

its ordered solution count, its finite Weyl sum, and its normalized `2s`-th
moment.  Finite character orthogonality proves exactly

```text
normalized incomplete moment = incomplete solution count.
```

The same identity is proved for an arbitrary finite alphabet mapped into
`ZMod Q`, then specialized to an arbitrary finite support `B`.  For the support
model, the unnormalized real moment is also identified exactly:

```text
sum_a |W_B(a)|^(2s) = Q^d * incompleteSupportSolutionCount.
```

The public API also records:

- recovery of the complete Vinogradov system when the window starts at degree
  one;
- monotonicity under dropping equations;
- the trivial Weyl-sum bound by the alphabet or support cardinality;
- the trivial solution-count bound by `|B|^(2s)`.

Contracts lock all public theorem types, and the axiom audit admits only the
repository's standard logical axioms.

## Not proved

This slice does **not** prove a nontrivial upper bound for the incomplete
solution count.  In particular it does not prove the estimate for
`J_{s,g,h}(B)` used after Ford's equation (5.4).  Adding the omitted lower-degree
equations would give the inequality in the wrong direction: more equations
produce fewer solutions, while Ford needs an upper bound for the system with
those equations absent.

The following therefore remain open:

- Ford's short-sum estimate in Lemma 5.1;
- tent-kernel localization and the associated coefficient constraints;
- smooth-support and near-integer estimates needed in the analytic argument;
- the final zeta-growth optimization;
- the Vinogradov--Korobov zero-free region and its `3/5` PNT remainder.

Nothing in this slice proves RH or excludes any new zeta zeros.

## Next mathematical input

The next useful theorem must be a genuinely nontrivial upper bound for the
support-restricted incomplete moment (or an equivalent localized continuous
mean value), with the parameter dependence required by Ford's Holder step.
The exact Fourier identities here provide the endpoint to which that analytic
or combinatorial estimate can attach.
