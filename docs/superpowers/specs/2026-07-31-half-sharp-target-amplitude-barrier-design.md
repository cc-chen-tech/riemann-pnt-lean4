# Half-Sharp Full-PNT Target-Amplitude Barrier Design

## Objective

Determine whether the attained classical Carlson upper bound from stack 33 can
be inserted directly into the existing quantitative reverse-cluster theorem.

The reverse theorem requires an eventual bound of the form

```text
|relativeChebyshevPsi0Error m|
  <= q * targetZeroPowerAmplitude beta m
```

for a fixed `beta < 1` and coefficient `q`. Stack 33 instead bounds the error
by a square-root-logarithmic full-PNT majorant.

## Scale comparison

The Carlson component has the form

```text
K * (1 + sqrt(log m))^11 * exp(-(rate / 2) * sqrt(log m)).
```

After division by

```text
targetZeroPowerAmplitude beta m
  = exp((beta - 1) * log m),
```

the decisive exponential is

```text
exp((1 - beta) * log m - (rate / 2) * sqrt(log m)),
```

which tends to infinity for every fixed `beta < 1`. The polynomial factor is
at least one and therefore cannot reverse this divergence.

## Concrete theorem chain

1. Define the normalized half Carlson kernel ratio.
2. Rewrite it exactly as a positive constant times a polynomial factor times
   the existing contour-to-target ratio.
3. Prove that this kernel ratio tends to infinity.
4. Prove the half Carlson kernel is a nonnegative summand of the complete
   closed-form full-PNT majorant.
5. Deduce that the normalized complete majorant also tends to infinity.
6. Prove that no fixed coefficient `q` eventually bounds the complete
   majorant by `q * targetZeroPowerAmplitude beta`.

## Interpretation

This is a barrier for the **available majorant**, not a lower bound for the
actual PNT error. It proves that the newly optimized upper-bound chain cannot
by itself trigger the fixed-beta reverse-cluster theorem.

A genuine contradiction therefore requires an additional input, such as:

- a target-amplitude-normalized complementary/remainder estimate;
- a distinct lower-bound height at polynomial scale;
- a two-height decomposition;
- or a smoothed explicit formula with a different contour cost.

## Scope

The module does not modify `ZeroForcingUnifiedTransfer.lean`, the separately
owned complementary-zero module, or VK-edge files. It prevents an invalid
upper/lower composition and identifies the exact missing growth-rate bridge.
