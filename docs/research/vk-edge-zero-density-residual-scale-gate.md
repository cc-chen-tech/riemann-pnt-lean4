# Zero-density residual scale gate

## Scope

This checkpoint tests one precise route from a selected off-line zero to an
upper bound for the remaining finite zero contribution. It does not prove a
contradiction, RH, or an unconditional upper bound for the prime-counting
error.

The Lean implementation has two layers:

- `VKEdgeZeroDensityResidualL2.lean` bounds a positive-height finite zero
  package using `zeroDensityCount` and Carlson's fixed-line estimate.
- `VKEdgeExplicitFormulaResidualBound.lean` identifies and bounds the genuine
  multiplicity-weighted finite zero remainder in the repository's explicit
  formula.

## The parameter competition

Write the logarithmic window center as `a` and choose the truncation height

\[
T(a)=\exp(\tau a).
\]

After normalization by the target scale \(x^\beta\), a classical \(x/T\)
contour error requires

\[
\tau>1-\beta.
\]

For a fixed line \(\sigma\), Carlson gives

\[
N(\sigma,T)
\ll_\sigma T^{4\sigma(1-\sigma)}(\log T)^4.
\]

If all residual zeros lie at least \(\delta\) to the left of the target, the
count-squared local \(L^2\) bound decays when

\[
4\sigma(1-\sigma)\tau+\eta<\delta
\]

for an arbitrarily small exponential loss \(\eta>0\).

The two requirements admit a common \(\tau\) exactly when

\[
4\sigma(1-\sigma)(1-\beta)+\eta<\delta.
\]

This equivalence and its negation are formalized as
`exists_exponentialTruncationScale_iff` and
`no_exponentialTruncationScale_of_gap_le`.

## Consequence

Carlson's count bound alone does not produce an RH contradiction. It controls
how many residual zeros occur to the right of a fixed line, but it does not
provide the required real-part gap from an arbitrary selected zero. When that
gap is absent, nearby zeros must be treated as a finite cluster rather than as
an exponentially decaying remainder.

The next mathematical input must therefore be cluster-aware:

1. isolate a finite top real-part band;
2. keep the entire band in the main oscillatory package;
3. use zero density only to bound its size;
4. prove a lower-energy or non-cancellation statement for that package;
5. control the complement and the genuine contour terms uniformly.

Until those steps are closed, local \(L^2\) lower bounds remain compatible
with a single off-line conjugate pair and do not imply extra zeros.
