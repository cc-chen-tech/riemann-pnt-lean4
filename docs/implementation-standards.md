# Implementation Standards for Remaining Chains

This document defines when a target statement may be promoted to a theorem in
this repository.

## Promotion Rule

A declaration of the form

```lean
def some_deep_result : Prop := ...
```

may be replaced by

```lean
theorem some_deep_result : ... := by
  ...
```

only when all of the following are true:

1. the mathematical statement has been checked for correctness against the
   standard analytic number theory literature;
2. the Lean theorem statement includes the hypotheses needed for the theorem to
   be true;
3. the proof is accepted by Lean without `sorry`, `admit`, or new `axiom`;
4. the change is verified by `lake build`;
5. the documentation is updated so that it no longer lists the statement as a
   target.

## Forbidden Shortcuts

The following are not acceptable ways to reduce the target count:

- replacing a theorem with an axiom;
- using `by
  sorry`, `by
  admit`, or an equivalent placeholder;
- weakening a theorem silently while keeping the old mathematical description;
- keeping a false theorem statement and adding assumptions that make it vacuous;
- proving only `True` while preserving a name that suggests a deep theorem;
- citing a `def ... : Prop` target as a proved theorem.

## Corrected Target Principle

Some earlier targets were too strong or mathematically false.  In those cases,
the right next step is not to force a proof, but to write a corrected target.

Examples:

- An unweighted statement that eventual positivity of `f` implies eventual
  positivity of `int_0^T f` is false; a tail-dominance hypothesis is needed.
- An exact finite-sum approximate functional equation is false; a remainder
  term and a bound are needed.
- A zero-counting lower bound for all `T >= 1` is usually false; an eventual
  lower bound after some `T0` is the correct shape.
- An unrestricted sum over all nontrivial zeros in an explicit formula needs a
  convergence convention such as truncation, principal value, or smoothing.

## Chain Acceptance Criteria

### Quantitative Zero-Free Region

The target may be promoted only after the proof supplies:

- a zeta-specific growth bound in the relevant vertical strip;
- a logarithmic-derivative bound or zero-repulsion lemma near `Re(s)=1`;
- a formal use of the verified 3-4-1 inequality;
- explicit constant management sufficient to produce one positive `c`.

### Explicit Formula

The target may be promoted only after the proof supplies:

- a corrected statement, preferably truncated or smoothed;
- Perron's formula for the relevant Dirichlet series;
- contour shifting and residue extraction;
- estimates for vertical and horizontal contour edges;
- a formal convention for zero sums.

### RH Error Equivalence

The target may be promoted only after the proof supplies both directions:

- RH implies the stated error term, using explicit formula bounds and
  zero-counting estimates;
- the stated error term implies no zero has `Re(s) > 1/2`, using a converse
  explicit-formula argument.

The final statement must match the chosen prime-counting function and smoothing
convention.

### Hardy Theorem and Quantitative Extensions

Hardy's theorem is now discharged by a first-zeta-approximation route. Its
accepted proof surface consists of:

- a uniform critical-line first zeta approximation;
- a linear lower bound for the dyadic critical-line zeta `L1` integral;
- an `O(T^(3/4))` upper bound for the dyadic Hardy-Z integral;
- a verified constant-sign contradiction under bounded critical-line zeros;
- theorem witnesses for both unbounded positive zero heights and the infinite
  set of distinct zero ordinates.

The remaining Hardy-Littlewood, Selberg, and Conrey-style targets are stronger
quantitative extensions. The repository now specifies separate odd-order,
distinct, and analytic-multiplicity counts. Hardy-Littlewood and Selberg use
the odd-order count detected by sign changes; Conrey must continue to
distinguish multiplicity-counted critical-line zeros from simple zeros.

## Verification Commands

Before claiming progress on any chain, run:

```bash
lake build
rg -n "sorry|admit|axiom" *.lean
```

If a chain-specific document is updated, also check that
`docs/missing-chains-index.md` links to it.
