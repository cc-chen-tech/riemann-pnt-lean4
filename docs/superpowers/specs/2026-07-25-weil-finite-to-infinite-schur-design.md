# Weil Finite-to-Infinite Schur Feasibility Design

## Purpose

Build a mathematically honest gate that separates the existing certified
finite Weil block from the analytic estimates needed for an infinite-dimensional
positivity result.

The feature must never infer an infinite-dimensional Weil criterion or RH from
the shipped finite certificates alone. Its output is a closure diagnosis:

- `CLOSES`: all stated finite and analytic inequalities satisfy a proved bridge;
- `BOUND_FAILS`: supplied rigorous bounds do not satisfy the bridge inequality;
- `MISSING_ANALYTIC_BOUNDS`: the finite block is certified, but required
  complement or tail bounds have not been supplied.

## Scope

The first version covers two sufficient bridge criteria:

1. Normalized truncation:

   `q_N(x) >= epsilon * size(x)^2`,

   `abs (q(x) - q_N(x)) <= delta * size(x)^2`,

   `delta <= epsilon`

   imply `q(x) >= 0`.

2. Schur block decomposition:

   `q_low(u) >= epsilon * size_low(u)^2`,

   `q_high(v) >= gamma * size_high(v)^2`,

   `abs (q_cross(u,v)) <= beta * size_low(u) * size_high(v)`,

   `beta^2 <= epsilon * gamma`

   imply

   `q_low(u) + 2 * q_cross(u,v) + q_high(v) >= 0`.

The feature does not construct the analytic Weil high-frequency estimates.
Instead, it defines their exact required interface and rejects closure when they
are absent.

## Architecture

### Lean bridge module

Create:

`WeilExtremalKernels/FiniteToInfiniteSchur.lean`

The module imports `WeilExtremalKernels.FiniteQuadraticForm` and proves:

- `nonneg_of_normalized_truncation_bound`;
- `two_mul_coupling_le_of_sq_le`;
- `schur_nonneg_of_bounds`;
- strict variants that produce positivity when at least one bridge inequality
  has strict slack.

The theorems are pointwise and generic over the low- and high-space types.
They do not assume a particular Hilbert-space implementation. Later analytic
modules can instantiate `size_low`, `size_high`, and the three form pieces with
the actual normalized Weil form.

### Exact feasibility diagnostic

Create:

`experiments/rh/weil_schur_feasibility.py`

The program consumes:

- one existing validated dual-route overlap artifact;
- optionally one analytic-bounds JSON artifact.

It imports the existing overlap artifact validator rather than duplicating its
schema and hash checks. All bridge arithmetic uses `fractions.Fraction`.

The finite low-block margin is derived from the existing certificate:

`epsilon = center_lower_bound - perturbation_row_bound`.

No floating-point conversion is permitted in the decision path.

### Analytic-bounds artifact

Schema version:

`weil-finite-to-infinite-schur-bounds/v1`

Required identity fields:

- `schema_version`;
- `source_overlap_payload_sha256`;
- `c`;
- `N`;
- `dimension`;
- `index_convention`;
- `normalization_id`;
- `claim_scope`;
- `bounds`;
- `provenance`;
- `payload_sha256`.

`claim_scope` must be:

`finite-to-infinite sufficient bounds only; no RH claim`

`bounds` supports either or both routes:

```json
{
  "normalized_tail_operator_norm_upper": "1/1000",
  "high_block_lower": "1/10",
  "coupling_norm_upper": "1/100"
}
```

Values are exact rational strings. Missing keys mean the corresponding
analytic estimate is unavailable, not zero.

`normalization_id` identifies the mathematical reference form and basis
normalization. The initial finite artifacts use:

`euclidean-fourier-raw/v1`

Any future preconditioned certificate must use a different identifier. Bounds
with a mismatched normalization are rejected.

The canonical SHA-256 calculation follows the existing overlap artifact rule:
serialize the payload without `payload_sha256` using sorted keys and compact
JSON separators.

## Decision Logic

Let:

- `epsilon` be the exact certified finite margin;
- `delta` be `normalized_tail_operator_norm_upper`;
- `gamma` be `high_block_lower`;
- `beta` be `coupling_norm_upper`.

The diagnostic first rejects malformed, mismatched, negative, or hash-invalid
inputs.

Normalized-tail route:

- closes when `epsilon > 0` and `delta <= epsilon`;
- fails the supplied bound when both values exist and `delta > epsilon`;
- is unavailable when `delta` is missing.

Schur route:

- closes when `epsilon > 0`, `gamma >= 0`, `beta >= 0`, and
  `beta^2 <= epsilon * gamma`;
- fails the supplied bound when all values exist and the inequality is false;
- is unavailable when either `gamma` or `beta` is missing.

Overall result:

- `CLOSES` if either route closes;
- `BOUND_FAILS` if no route closes and at least one complete route fails;
- `MISSING_ANALYTIC_BOUNDS` if no complete analytic route was supplied.

`CLOSES` means only that the supplied hypotheses imply positivity through the
formal bridge. It does not establish that the supplied analytic bounds are true
unless a separate Lean theorem provides them.

## Output

The command prints canonical JSON containing:

- artifact identity and normalization;
- exact `epsilon`;
- supplied exact analytic bounds;
- `epsilon - delta` when available;
- `epsilon * gamma - beta^2` when available;
- per-route verdicts;
- overall verdict;
- a list of missing mathematical obligations;
- an explicit scope warning.

The process exit code is:

- `0` for a valid diagnostic, including non-closing verdicts;
- `2` for malformed, corrupted, or mismatched input.

## Research Note

Create:

`docs/research/weil-finite-to-infinite-schur.md`

The note explains in nontechnical Chinese:

- what the finite certificate proves;
- why a complement estimate is required;
- what `epsilon`, `delta`, `gamma`, and `beta` mean;
- why the current artifacts initially return
  `MISSING_ANALYTIC_BOUNDS`;
- the next analytic task: isolate a positive reference form and prove either a
  normalized tail bound or high-block/coupling bounds;
- the separate `N -> infinity` and `c -> infinity` obligations.

## Error Handling

The diagnostic rejects:

- invalid overlap artifacts;
- invalid analytic-bounds hashes;
- source hash mismatches;
- parameter or index-convention mismatches;
- normalization mismatches;
- unknown schema or claim scope;
- non-rational bound strings;
- negative tail or coupling upper bounds;
- negative high-block lower bounds in the first version.

It never repairs, widens, or substitutes missing bounds.

## Tests

Extend:

`tests/test_weil_interval_integration.py`

Coverage:

- current N=16 and N=32 artifacts report `MISSING_ANALYTIC_BOUNDS`;
- an exact normalized-tail fixture with `delta <= epsilon` reports `CLOSES`;
- an exact Schur fixture with `beta^2 <= epsilon * gamma` reports `CLOSES`;
- complete bounds that miss both inequalities report `BOUND_FAILS`;
- source hash, parameter, normalization, and payload tampering are rejected;
- rational boundary equality is accepted exactly;
- no float appears in decision values.

Lean coverage uses a small import/check module proving concrete scalar examples
through both bridge theorems.

## Acceptance Boundary

The implementation is complete when the generic Lean bridge, exact diagnostic,
Chinese research note, and focused integration tests exist.

Passing the diagnostic on a synthetic fixture is a software acceptance result.
The research route is not mathematically closed until a separate analytic
development supplies and proves the actual Weil tail or Schur hypotheses.
