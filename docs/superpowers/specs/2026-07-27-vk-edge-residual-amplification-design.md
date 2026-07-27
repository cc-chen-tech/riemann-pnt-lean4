# VK-edge residual amplification design

## Purpose

The existing VK-edge chain proves that one off-critical-line zero forces a
linear ordinary local second-moment lower bound for the normalized prime
number theorem error.  It does not show that any zero other than the target
zero is needed to account for that mass.

This branch makes a model-level obstruction quantitative. It defines a
cosine pair using multiplicity, height, and argument copied from the selected
zero, computes the model's local second-moment budget, and compares that
budget with the existing swept Gaussian lower-bound constant. It does not
identify the model with a term in the true explicit formula.

This is a gate toward

```text
off-line zero
  -> a proved explicit-formula identification of the cosine model
  -> residual large values after subtracting the identified term
  -> an additional right-hand zero contribution
  -> a possible zero-density contradiction.
```

It is not an RH theorem and it does not create a second zero by itself.

## Normalization

For a nontrivial zero

```text
rho = beta + i gamma
```

of analytic multiplicity `m`, the repository uses

```text
F_rho(y) =
  norm rho * (chebyshevPsi (exp y) - exp y) * exp (-beta * y).
```

The branch defines the real cosine model

```text
P_rho(y) = -2 * m * cos (gamma * y - arg rho)
```

using these parameters. Define the formal model residual by

```text
R_rho(y) = F_rho(y) - P_rho(y).
```

The sign of `P_rho` is immaterial for its second moment. No theorem in this
branch proves that `P_rho` equals the selected pair's true explicit-formula
contribution, or that `R_rho` consists of other zeros and contour terms.

## Target-pair energy

For an interval `[a,b]` and `gamma != 0`, the exact cosine-square identity
gives

```text
integral_[a,b] P_rho(y)^2 dy
  = 2 * m^2 * (b-a)
    + (m^2 / gamma)
        * (sin (2*gamma*b - 2*arg rho)
           - sin (2*gamma*a - 2*arg rho)).
```

Consequently,

```text
integral_[a,b] P_rho(y)^2 dy
  <= 2 * m^2 * (b-a) + 2 * m^2 / abs gamma.
```

On the epsilon logarithmic window

```text
[log Y, (1+epsilon) * log Y],
```

the leading cosine-model energy is

```text
2 * epsilon * m^2 * log Y.
```

Thus a total-error lower bound with a coefficient no larger than
`2 * epsilon * m^2` can be explained by the cosine model alone.

## Existing constant is below the gate

Write

```text
c2 = centeredSharpenedSweptOrdinaryL2Constant epsilon rho k.
```

The definitions at scale `epsilon / 2` simplify to

```text
q       = 64 * (epsilon + 4)^2 / epsilon^2,
d       = 64 * (epsilon + 4) / epsilon,
q - d   = 256 * (epsilon + 4) / epsilon^2,
R - 1   = epsilon / (epsilon + 2).
```

The missing-harmonic denominator satisfies

```text
1 / pi <= sharpenedMissingHarmonicDenominator k,
```

and the paired kernel envelope is at least `1`.  The remaining Gaussian
mass factor is strictly larger than `1/q`.  Substituting these estimates in
the definition of `c2` gives

```text
c2
  < pi * m^2 *
      epsilon * (epsilon + 4) / (8 * (epsilon + 2))
  < epsilon * m^2.
```

The last inequality uses `(epsilon + 4)/(epsilon + 2) < 2` and `pi < 4`.
The intended public theorem is:

```lean
theorem centeredSharpenedSweptOrdinaryL2Constant_lt_cosineModelHalfEnergy
    {epsilon : Real} {rho : Complex} {k : Nat}
    (hepsilon : 0 < epsilon)
    (hzero : riemannZeta rho = 0)
    (hnontrivial : RiemannHypothesis.IsNontrivialZero rho) :
    centeredSharpenedSweptOrdinaryL2Constant epsilon rho k <
      epsilon * (analyticOrderNatAt riemannZeta rho : Real) ^ 2
```

The exact hypotheses may be reduced if the existing multiplicity-positive
API only needs `hzero` plus analyticity at `rho`.

This is strictly below one half of the cosine model's leading energy
coefficient.  Therefore the current swept lower bound cannot imply a
positive residual lower bound.

## Generic residual-energy interface

Create a zeta-independent module for the reverse triangle inequality in
`L2`.  If, on a finite-measure set,

```text
integral F^2 >= A * L,
integral P^2 <= B * L,
A > B,
```

then

```text
integral (F-P)^2
  >= (sqrt A - sqrt B)^2 * L.
```

The implementation should preferably use the existing `snorm` or
`MemLp` API.  If that introduces unnecessary coercion overhead, first prove
the squared integral form from Cauchy-Schwarz:

```text
sqrt (integral (F-P)^2)
  >= sqrt (integral F^2) - sqrt (integral P^2).
```

The module must remain independent of zeta so that it can be reused by
other explicit-formula projects.

## Zeta-parameterized model endpoint

Define:

```lean
def normalizedCosineModelPair (rho : Complex) (y : Real) : Real
def normalizedPsiModelResidual (rho : Complex) (y : Real) : Real
```

and prove:

1. measurability and interval integrability;
2. the exact cosine-model second-moment identity;
3. the explicit interval upper bound;
4. a conditional model-residual lower-bound theorem whose hypothesis requires a
   total second-moment coefficient strictly greater than the cosine-model
   coefficient.

Do not claim that the existing swept theorem discharges this hypothesis.
The constant comparison theorem proves that it does not.

## Next mathematical input

After this branch, the next research question is deliberately narrow:

> Can one first identify `normalizedCosineModelPair rho` with the true
> selected-pair term in a multiplicity-aware explicit formula, and then prove
> that `normalizedPsiModelResidual rho` has a linear local second moment?

The current branch has not crossed that identification bridge. Generic
zero-free-region and zero-density arguments are also not enough: one cosine
model is compatible with the existing lower bounds,
and Beurling-prime constructions realize analogous sharp behavior.  The
candidate extra inputs are:

1. a classical-prime correlation estimate which excludes the
   one-frequency residual model;
2. a detector that annihilates the cosine model and still has a nonzero
   arithmetic main term;
3. a noncircular recurrence theorem weaker than zeta strong recurrence.

Strong self-recurrence cannot be used as an independent input because its
classical zeta form is equivalent to RH.

## Files

Planned new files:

```text
MathlibAux/ResidualSecondMoment.lean
PrimeNumberTheorem/VKEdgeResidualAmplification.lean
Test/ResidualSecondMomentContract.lean
Test/VKEdgeResidualAmplificationContract.lean
Test/VKEdgeResidualAmplificationAxiomAudit.lean
docs/research/vk-edge-residual-amplification-audit.md
```

Only the corresponding targets are added to `lakefile.lean`.

## Validation

The branch is accepted when:

1. the exact pair identity and interval bound compile;
2. the generic residual-energy theorem compiles;
3. the strict comparison
   `c2 < epsilon * multiplicity^2` compiles;
4. contracts fix all public signatures;
5. `#print axioms` shows only the standard Lean/Mathlib logical axioms;
6. new source contains no `sorry`, `admit`, or project `axiom`;
7. focused builds, `git diff --check`, baseline verification, and full
   `lake build` pass.

The branch does not pass by merely defining a residual or restating a
conditional proposition.
