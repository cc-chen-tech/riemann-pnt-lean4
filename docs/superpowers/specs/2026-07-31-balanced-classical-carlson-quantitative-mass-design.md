# Balanced classical Carlson quantitative-mass design

## Objective

Propagate the exact optimized zero-free gap constant from the balanced
truncation theorem into the actual Carlson-controlled moving zero masses.
Previous quantitative mass endpoints existentially selected `b` and
`gapRate` without retaining their relation.

## Parameterized transfer

The first theorem accepts:

- a positive classical height parameter `b`;
- a positive `gapRate`;
- a selected-height dynamic zero-free certificate at
  `gapRate / (1 + sqrt(log m))`.

It then returns a positive constant `D` such that, for every selector,

\[
\text{middleMass}(m)
 \le \text{lowMass}(m)+M_{D,r}(m),
\]

and

\[
\text{movingStripMass}(m)\le M_{D,r}(m),
\]

where

\[
M_{D,r}(m)=\exp\!\left(
 \log D-3\log r+11\log(1+\sqrt{\log m})
 -\frac r4\sqrt{\log m}\right).
\]

The same input `gapRate` appears in the zero-free region, dyadic layer width,
and output majorant.

## Balanced instance

Using the stack-27 exact zero-free endpoint, the module returns constants with

\[
\text{gapRate}=\frac{\min(1,\sqrt b)}2
\]

and preserves the verified bottleneck identity

\[
\frac{\min(1,\sqrt b)}8=\frac{\text{gapRate}}4.
\]

Thus the explicit Carlson mass now carries the actual optimized truncation
rate as theorem data rather than an informal reconstruction.

## Honest boundary

This stack propagates the exact rate through the positive moving mass layer.
The selector-dependent critical-half and low-strip norm constants, finite
real-ordinate term, and explicit-formula remainder still need to be
reassembled to produce a balanced-rate full-PNT endpoint.  The factor four in
the Carlson exponent remains the current coarse aggregation loss and is not
claimed optimal.
