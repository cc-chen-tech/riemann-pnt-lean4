# PR #474: windowed detector and single-layer forcing boundary

## What is theorem-level

PR #474 adds a kernel-checked collection of conditional transfer theorems:

- `WindowedMellinL2` proves the per-zero Mellin response formula and endpoint
  bounds.
- `ZeroDensityLayerBudgetCubicKernelLocal` and
  `WindowedDetectorResponseKernel` prove the local cubic response multiplier
  identities and bounds.
- `HalfIsolatedZeroDichotomy.DetectionPointChoice` proves the interval-covering,
  windowed-count, dyadic-distance, and good-detection-point lemmas that had
  previously been described as route inputs.
- `WindowedMellinResponseIdentity`, `WindowedMellinL3`, and
  `WindowedDetectorConclusion` turn an explicitly supplied truncated formula,
  error bound, mass budgets, and seed signal into the L3 contradiction and a
  top-layer mass conclusion.
- `SharpWitnessTransfer` proves deterministic energy-to-pointwise and
  energy-to-count transfer lemmas.
- `SingleLayerForcingBeta14Over17` proves that a forcing lower count with the
  displayed exponent beats the existing fixed-sigma Carlson upper bound when
  `beta > 14/17`.

These are genuine Lean theorems. Their hypotheses remain visible in their
signatures; they must not be summarized as an unconditional zero-free result.

## What remains conditional

The repository does **not** yet prove either of the following without an
additional input:

```text
every nontrivial zero has Re(rho) <= 14/17
every nontrivial zero has Re(rho) <= 2/3
```

The `14/17` endpoint is exposed through
`no_nontrivial_zero_re_gt_14_over_17_of_forcing`,
`no_nontrivial_zero_re_gt_14_over_17_of_certificates`, and
`no_nontrivial_zero_re_gt_14_over_17_of_cubicLine`. The missing mathematical
step is a theorem constructing `CubicLineForcingAssumption.lower` from the
concrete `DirectL2` and two-height capacity inputs for every required `beta`
and `lam`.

The `2/3` endpoint is exposed through
`no_nontrivial_zero_re_gt_two_thirds_of_gateInputs` and
`no_nontrivial_zero_re_gt_two_thirds_of_assembly`. It still requires a
`GateAssemblyInput` for every feasible parameter tuple, including the actual
branching, separation, lower-count, explicit-formula/error, and exponent-budget
suppliers. Packaging these requirements in a structure does not prove them.

## Build and audit coverage

The merged modules and their 13 focused axiom-audit modules are registered in
the default Lake target. `scripts/check_axiom_allowlist.py` also invokes those
audits explicitly and accepts only `propext`, `Classical.choice`, and
`Quot.sound` for the declarations they print.

Before publishing claims from this route, run:

```bash
./scripts/verify-baseline.sh
python3 -m pytest
python3 scripts/list-prop-targets.py
```

The full build and axiom audit establish kernel and dependency cleanliness.
They do not discharge the explicit analytic inputs described above.
