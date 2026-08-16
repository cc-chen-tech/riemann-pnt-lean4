# Windowed half-isolated detector: Lean specification

## Status

Specification (no proofs yet) for the candidate repair of Gate gaps 1 and 2
(`gate-mechanism-gap-diagnosis.md`).  Numerical support in
`experiments/gate_budget/windowed_detector.py`
(output `windowed_detector_report.md`).  Toy numerics only; the Lean
statements below are the next formalization target.

## Goal

A detector that forces a top-layer zero **inside a prescribed height window**
`[T0, T0+H]`, not just somewhere below `T`.  With such a detector, one
directed layer can run `q(T) ~ H/delta` separated windows and produce
`q(T) = T^(h-kappa)` successors per seed, closing `hgap` for **every**
`beta > 2/3` (needs `(h-kappa) * depth > q(sigma)`, `kappa < h`).

## Detection principle

For a detection frequency `gamma` and scale `x = exp y`, the explicit formula
gives (modulo the standard approximation error)

```text
integral of the oscillation over [X, X^lam] weighted by x^(-1-i gamma)
  = seed response + sum over complementary zeros (Re <= beta - gap)
      m(rho) * x^(beta - gap) / (|rho| * |gamma - im rho|)
    + error.
```

If there is no top-layer (real part `beta`) zero with `im` in `[T0, T0+H]`,
the only contributions are the complementary weighted sum and the error; when
the aligned seed response exceeds their total, a top-layer zero must exist in
the window.

## Three lemmas to formalize

### L1: detection-point choice

```lean
theorem exists_good_detection_point
    (T0 H gap : ℝ) (complementary : Finset ℂ) :
    0 < H → -- plus density assumptions on `complementary`
    ∃ γ, T0 ≤ γ ∧ γ ≤ T0 + H ∧
      (∑ ρ ∈ complementary, analyticOrderNatAt riemannZeta ρ / (‖ρ‖ * |γ - ρ.im|))
        ≤ C * (1 + Real.log (T0 + H)) ^ 3 / T0
```

Numerical support: mean of the weighted sum scales like `T^(-1)` polylog
(poisson model, fitted exponent -0.85) and the fraction of "bad" gamma
exceeding 10x the mean stays below 2.5%.  Proof shape: average over the
window + remove a small bad set (measure argument).

### L2: windowed Mellin response identity

```lean
theorem windowed_mellin_response_eq_seed_add_complementary_add_error
    (X lam T0 H β gap : ℝ) (γ : ℝ) :
    -- hypotheses: X and lam bounds, gamma in [T0, T0+H], etc.
    ∃ C, 0 ≤ C ∧
      ‖windowedOscillationResponse X lam γ -
          (seedResponse X lam γ β + complementaryWeightedSum X T0 H β gap γ)‖ ≤
        C * errorEnvelope X lam T0 H
```

This is the frequency-localized version of the existing explicit formula
with the `x^(-1-i gamma)` weight; it must reuse `ExplicitFormulaAllHeights`
and the truncated-formula modules, not invent a new contour theory.

### L3: threshold comparison forces a windowed zero

```lean
theorem windowed_response_below_envelope_implies_top_layer_zero_in_window
    (X lam T0 H β gap : ℝ)
    (hnoZero : ∀ ρ, RiemannHypothesis.IsNontrivialZero ρ →
        ρ.re = β → T0 ≤ ρ.im → ρ.im ≤ T0 + H → False)
    (hseed : alignedSeedResponseLowerBound X lam β T0)
    (hcomp : complementaryWeightedSumBound X T0 H β gap)
    (hgapPos : 0 < gap)
    (hlarge : envelopeStrictlyBelowSeed hseed hcomp) :
    False
```

Note the real-part separation `gap > 0` does all the work: the complementary
weight decays like `x^(-gap)` while the seed stays at `x^beta`.

## Interface to the gate

- `hbranch`: one `L3` application per separated window in `[T0, T0+H]`
  gives `q(T) = H / (2 delta) = T^(h - kappa)` successors per node;
- `hdisjoint`: windows separated by `2 delta` are disjoint
  (`topLayerWindow_disjoint_of_imag_separation`, already proved);
- `hgap`: `T^((h-kappa) * depth)` beats `C (T+H)^(4 sigma (1-sigma)) log^4`
  once `(h-kappa) * depth > 4 sigma (1-sigma)` and `kappa < h`.

## Open sub-questions before proof work

1. Exact dependence of `L1`'s constant on the density model: the current
   numerics use the global-count density `log T / 2pi`; the Lean statement
   must use the proved complementary mass bounds
   (`norm_complementaryZeroPackageContribution_le_exp_gap_mul_sum` and its
   companions) instead of a synthetic density assumption.
2. Whether `L2`'s error envelope can be absorbed by the strict gap without
   losing the `x^(-gap)` advantage (the cubic design's `X^(-1/20)` margin
   is the intended budget).
3. Whether `delta` can stay a constant while windows are separated (then
   `kappa = 0` and `q(T) = T^h`): the directed order needs `im` strictly
   increasing across layers, so `delta > 0` suffices for disjointness while
   the window exponent `h` alone supplies the growth.

## Boundaries

Specification only; no theorem-level claims.  The numerics are toy models,
not proofs.
