# Parallel RH Agent Run

## Purpose

Coordinate the current parallel work on RH-adjacent computational tooling while
another worker handles Lean `sorry` cleanup. This file records ownership so the
parallel tasks stay isolated.

## Workers

### Gauss: Li Coefficient Experiment

Owned files:

- `experiments/rh/__init__.py`
- `experiments/rh/li_coefficients.py`
- `experiments/rh/output/li_coefficients_report.md`
- `tests/test_li_coefficients.py`

Goal:

- Add a standard-library-only prototype for truncated Li coefficient
  approximations using paired nontrivial-zero fixtures.

Status:

- Completed. Focused tests passed.

### Noether: PNT Report Generator

Owned files:

- `experiments/pnt/report.py`
- `experiments/pnt/output/pnt_report.md`
- `tests/test_pnt_report.py`

Goal:

- Turn PNT sample rows into an empirical Markdown summary with extrema and sign
  changes.

Status:

- Completed. Focused tests passed.

### Averroes: Ramsey Certificate Export

Owned files:

- `experiments/discrete/ramsey_search.py`
- `experiments/discrete/output/ramsey_r3_3_n5.json`
- `tests/test_ramsey_certificate.py`

Goal:

- Export and verify finite JSON certificates for the Ramsey toy search.

Status:

- Completed. Focused tests passed.

## Integration Rules

- Do not modify Lean files during this run.
- Do not revert existing user or external worker changes.
- Run focused Python tests first, then a combined Python test pass.
- Treat numerical output as empirical only.
