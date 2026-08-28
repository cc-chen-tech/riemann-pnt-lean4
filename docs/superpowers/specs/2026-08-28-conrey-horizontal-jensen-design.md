# Conrey Horizontal Jensen Design

## Scope

Build the function-specific Jensen disk and admissible-height checkpoint for
the actual explicit product `conreyMollifiedDegreeOneV1 (49/100) 0 (51/50)`.
The implementation must follow
`docs/research/2026-08-28-conrey-horizontal-jensen-math.md`.

## Required public boundary

The checkpoint must provide:

1. the exact moving disk geometry with left edge `1/4`;
2. analyticity of the actual product on that disk;
3. a direct center lower bound `1/6` on `1 <= t <= exp L`;
4. an actual-product outer-circle growth bound under `2 <= Y`,
   `Y <= exp L`, `0 <= R <= 6/5`, and `L >= 40000`;
5. a Jensen divisor-mass bound with the denominator
   `log (outerRadius / innerRadius)` visible;
6. a height in every admissible unit window on which the whole horizontal
   segment is nonzero.

The PR may stop at this checkpoint. It must not claim that the regular-part
logarithmic derivative, the weighted horizontal term, equations (38)--(41),
the far-right argument variation in equation (37), the long mollified mean
square, or strict `> 2/5` are complete.  The proved right-edge
`integral |log |F||` is not a bound for that argument variation.

## Mathematical constants

- `rightEdge L = 2 * Real.log L`
- `leftEdge R L = 1 / 2 - R / L`
- `outerRadius L = rightEdge L - 1 / 4`
- `innerRadius R L = sqrt ((rightEdge L - leftEdge R L)^2 + 1/4)`
- `center L U = rightEdge L + I * (U + 1/2)`
- `L >= 40000`, `0 <= R <= 6/5`
- admissible window: `rightEdge L + 1 <= U` and `U + 1 <= exp L`
- center norm lower bound: `1/6`

The later division by the Littlewood gap additionally requires `0 < R`.
This checkpoint keeps `R = 0` only because disk geometry and height selection
do not divide by the gap. The explicit certificate value `R = 6/5` must be
admissible.

## Proof-status rules

- Prove growth for the actual product; do not introduce an assumed growth
  predicate and call the checkpoint closed.
- Keep exact finite divisor sums and exact radii through Jensen. Big-O prose
  belongs only in the research note.
- Lean is a verifier for the preceding mathematics. If any displayed
  inequality fails, update the mathematical note before weakening code.
- Every public theorem gets a contract and `#print axioms`; only standard
  axioms are allowed.
