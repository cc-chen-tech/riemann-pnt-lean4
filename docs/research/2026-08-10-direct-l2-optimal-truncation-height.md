# Direct L2 optimal truncation height

## Purpose

The dynamic-strip analysis identifies a feasible cutoff height.  This note
solves the associated one-variable minimax problem exactly and separates two
different meanings of "optimal height":

1. tail-only optimization, where the best cutoff lies at the admissible upper
   boundary;
2. robust high/low optimization, where a genuine high-tail or contour exponent
   penalizes loss of headroom and produces an interior optimum.

The distinction is essential.  A domain restriction must not be presented as
an analytic error term unless the explicit formula actually supplies the
corresponding exponent.

## Direct-L2 strip envelope

Fix

```text
g := lambda * (1 - beta),
g < gamma < c.
```

Here `gamma` is the lower dyadic cutoff exponent, so the cutoff is

```text
H = X^gamma.
```

The direct-L2 real-strip analysis gives the two worst polynomial exponents

```text
fLeft(gamma)  := -gamma,
fRight(gamma) := -2 * (gamma - g).
```

Thus the uniform infinitesimal-strip margin is

```text
rTail(gamma)
  := min gamma (2 * (gamma - g)),

maxStripExponent(gamma) = -rTail(gamma).
```

Both entries of `rTail` are strictly increasing in `gamma`.

## Tail-only optimum

If `c` is only an admissible-height cap, then on the closed interval
`g <= gamma <= c`,

```text
max rTail(gamma) = rTail(c)
                 = min c (2 * (c - g)).
```

The optimum is attained at

```text
gamma = c.
```

If the theorem requires the strict domain `gamma < c`, there is no optimizer;
there is only the supremum

```text
sup rTail(gamma) = rTail(c).
```

Any claim of an interior "optimal" height in this tail-only problem is false.
An interior midpoint is merely a convenient feasible witness.

For the natural cap

```text
c = lambda / 2,
```

feasibility `g < c` is exactly `beta > 1/2`.

## A genuine headroom exponent

Suppose a separately proved high-tail or contour estimate contributes the
polynomial exponent

```text
fCap(gamma) := kappa * (gamma - c),
```

where

```text
0 < kappa.
```

Its positive decay margin is

```text
rCap(gamma) := kappa * (c - gamma).
```

This is an analytic input, not a formal replacement for the condition
`gamma < c`.

The robust cutoff problem is now

```text
maximize R(gamma)

R(gamma)
  := min gamma
       (min (2 * (gamma - g))
         (kappa * (c - gamma)))

subject to g <= gamma <= c.
```

The first two margins increase and the last decreases, so the optimizer is
where the decreasing line meets the active increasing branch.

## Exact piecewise optimizer

Define the transition condition

```text
cTransition := 2 * g * (1 + 1 / kappa).
```

### Regime I: right-strip branch active

If

```text
c <= 2 * g * (1 + 1 / kappa),
```

then the active increasing margin is `2 * (gamma - g)`.  The unique optimizer
is

```text
gammaStar
  := (kappa * c + 2 * g) / (kappa + 2),
```

and the optimal margin is

```text
RStar
  := 2 * kappa * (c - g) / (kappa + 2).
```

At this point

```text
2 * (gammaStar - g)
  = kappa * (c - gammaStar)
  = RStar,

gammaStar <= 2 * g,

gammaStar >= RStar.
```

The last inequality says the left-strip line is inactive or tied.

### Regime II: left-strip branch active

If

```text
2 * g * (1 + 1 / kappa) <= c,
```

then the active increasing margin is `gamma`.  The unique optimizer is

```text
gammaStar
  := kappa * c / (kappa + 1),
```

and the optimal margin is

```text
RStar
  := kappa * c / (kappa + 1).
```

At this point

```text
gammaStar
  = kappa * (c - gammaStar)
  = RStar,

2 * g <= gammaStar,

2 * (gammaStar - g) >= RStar.
```

The right-strip line is inactive or tied.

At equality of the transition condition, both formulas give

```text
gammaStar = 2 * g,
```

and all three margins agree.

## Affine dual certificates

The minimax objective is

```text
minimize max (fLeft gamma) (max (fRight gamma) (fCap gamma)).
```

The exact optimizers can be checked by the finite affine certificate without
formalizing an optimization algorithm.

### Regime I certificate

The active lines are `fRight` and `fCap`, with slopes `-2` and `kappa`.  Use

```text
wRight := kappa / (kappa + 2),
wCap   := 2 / (kappa + 2).
```

Then

```text
wRight >= 0,
wCap >= 0,
wRight + wCap = 1,
-2 * wRight + kappa * wCap = 0.
```

The weighted active value is `-RStar`.  The regime inequality verifies that
`fLeft(gammaStar) <= -RStar`.

### Regime II certificate

The active lines are `fLeft` and `fCap`, with slopes `-1` and `kappa`.  Use

```text
wLeft := kappa / (kappa + 1),
wCap  := 1 / (kappa + 1).
```

Then

```text
wLeft >= 0,
wCap >= 0,
wLeft + wCap = 1,
-wLeft + kappa * wCap = 0.
```

The weighted active value is `-RStar`.  The regime inequality verifies that
`fRight(gammaStar) <= -RStar`.

These are complete global-optimality certificates for the one-dimensional
affine problem.

## Natural cap and unit headroom slope

For the illustrative specialization

```text
c     := lambda / 2,
kappa := 1,
```

the transition is

```text
c <= 4 * g
```

or, equivalently,

```text
beta <= 7/8.
```

For `1/2 < beta <= 7/8`,

```text
gammaStar = lambda * (5 - 4 * beta) / 6,
RStar     = lambda * (2 * beta - 1) / 3.
```

For `7/8 <= beta < 1`,

```text
gammaStar = lambda / 4,
RStar     = lambda / 4.
```

This specialization is valid only when an actual high-tail theorem supplies
the line `gamma - lambda/2`.  The direct-L2 cap by itself does not supply that
line.

## Finite strips and logarithmic loss

Suppose the infinitesimal real-strip exponent is at most `-RStar`.  Since
`kappa_lambda` is `lambda`-Lipschitz, choose strip width

```text
delta := RStar / (4 * lambda).
```

Then every finite strip has energy exponent at most

```text
-RStar / 2.
```

The fixed energy-level loss `(log X)^5` can absorb another half of the
remaining polynomial margin, giving

```text
energy = O(X^(-RStar / 4)),
RMS    = O(X^(-RStar / 8)).
```

These are conservative certificate rates, not sharp asymptotic constants.

## Proposed arithmetic theorem chain

```text
directL2TailMargin_mono
directL2TailMargin_sup_at_cap
directL2RobustObjective
directL2RobustRegimeOne_gamma
directL2RobustRegimeOne_margin
directL2RobustRegimeOne_certificate
directL2RobustRegimeTwo_gamma
directL2RobustRegimeTwo_margin
directL2RobustRegimeTwo_certificate
directL2RobustOptimizer
directL2NaturalCap_transition_iff
directL2NaturalCap_regimeOne_formula
directL2NaturalCap_regimeTwo_formula
directL2RobustFiniteStripExponent_neg
```

The arithmetic slice should depend only on ordered-field algebra and the
finite affine certificate.  It must not import zeta zeros, Sharp lower bounds,
or half-isolated occupancy.

## Audit rules

- State whether the height problem has a maximum or only a supremum.
- Do not turn an admissibility cap into an error exponent.
- Keep the low cutoff `gamma` distinct from the outer contour height `alpha`.
- Record the active exponent lines and dual weights.
- Treat zero exponent as critical, not decaying.
- Record energy and RMS rates separately.
- Do not interpret the `beta = 7/8` regime transition as a zero-free result.
- Do not claim optimality for a high-tail model until its affine headroom line
  has been proved from the actual explicit formula.
