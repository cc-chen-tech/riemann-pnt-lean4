# Li Criterion Computational Plan

## Scope

This plan expands the computational route around Li coefficients without
modifying Lean files. The Python experiment is a finite zero-sum truncation
tool only. It can produce evidence, regression fixtures, and exportable tables,
but it cannot prove the Riemann Hypothesis.

## Current Artifacts

- `experiments/rh/zeros_fixture.csv`
  - CSV fixture with positive zero ordinates and provenance notes.
  - Values are rounded decimal ordinates retained from the earlier embedded
    script fixture.
- `experiments/rh/li_coefficients.py`
  - Standard-library-only loader, finite zero-pair summation, Markdown report,
    coefficient CSV export, and truncation-sensitivity CSV export.
  - CLI defaults derive valid sensitivity cutoffs from the loaded fixture size,
    so smaller fixture files remain usable without extra flags.
- `experiments/rh/output/li_coefficients_report.md`
  - Human-readable empirical report with cutoff comparison.
- `experiments/rh/output/li_coefficients.csv`
  - Machine-readable coefficient table for the selected finite cutoff.
- `experiments/rh/output/li_truncation_sensitivity.csv`
  - Machine-readable comparison across finite zero-pair cutoffs.

## Data Limitations

The fixture is deliberately small. It is useful for software regression tests
and for making the truncation behavior visible, not for high-confidence
numerics. Before using the data in a paper or formal argument, replace or
augment it with a citable high-precision zero table and record exact source,
license, retrieval date, rounding policy, and checksum.

Every computed value in the current route is:

- empirical;
- finite-cutoff truncated;
- sensitive to how many zero pairs are included;
- independent of any formal Lean proof;
- insufficient to prove positivity of all Li coefficients.

## Next Computational Targets

1. Add a larger external fixture with explicit source URL, retrieval date,
   rounding policy, and checksum.
2. Add a JSON fixture format if richer metadata becomes necessary.
3. Compare the zero-sum approximation against a xi-derivative or
   generating-function computation for small `n`.
4. Add an error-budget document before increasing precision or publishing
   numeric conclusions.
5. Keep CSV schemas stable so reports can be diffed across fixture revisions.
6. Keep default truncation cutoffs fixture-aware; larger fixtures may add more
   comparison points, but smaller fixtures should still run without manual
   cutoff flags.

## Next Formalization Targets

The computational route should feed statement design, not theorem claims. The
first Lean-facing targets remain:

1. Define a canonical `xiFunction` API, separate from any exploratory local
   completed-zeta definitions.
2. State a noncomputable `liCoefficient` definition through the xi derivative
   route after branch and nonvanishing assumptions are explicit.
3. Prove or import the real-valuedness statement for Li coefficients.
4. State `LiCriterionHolds : Prop` without adding new `sorry` to main proof
   files.
5. Only after the xi route is stable, connect the zero-sum expression to the
   derivative definition with convergence and symmetric-limit hypotheses.

## Validation Commands

Use focused Python checks for this route:

```bash
python3 -m pytest tests/test_li_coefficients.py -q
python3 -m compileall -q experiments tests
python3 experiments/rh/li_coefficients.py
```

These commands validate the experiment tooling and regenerated artifacts. They
do not validate any Lean theorem and do not reduce the remaining `sorry`
inventory.
