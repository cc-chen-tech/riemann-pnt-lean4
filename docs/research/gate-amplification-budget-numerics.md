# Gate amplification exponent budget: numerical verification

## Status

Candidate numerical budget for the amplification gate
(`PrimeNumberTheorem/ExceptionalZeroAmplificationGateContract.lean`, worktree
`exceptional-zero-amplification-integration`).  Experiment-only; not a theorem.
Must be aligned with `ZeroDensityLayerBudgetDirectL2NumericalCore` before any
Lean statement.

Scripts: `experiments/gate_budget/gate_budget.py`,
`experiments/gate_budget/toy_iteration.py`
Reports: `experiments/gate_budget/output/*.md`

## Mechanism map (from the Lean modules)

The gate inputs are fed by two mechanisms already present in Lean:

1. **Combinatorial dichotomy** (`HalfIsolatedZeroDichotomy`): every top-layer
   zero is either half-isolated (alone in its `delta` window) or in a
   quantitative local cluster (window of at least two zeros).  Non-isolated
   centers double the count (`2 * centers.card <= zset.card`).  This gives
   constant branching only.
2. **Lean no-go** (`one_offline_zero_certificate_does_not_yield_diverging_gap`):
   a single-window/single-zero certificate can never produce the divergent
   gap required by `hgap`.  Branching `q(T)` must grow with `T`.

Hence the growth must come from a *density* mechanism: the energy excess
forced by the seed must supply successor zeros at a density above the global
average.

## Exponent models

Fix `2/3 < beta < 1`, `lambda in [1, 2)`, Occupancy `theta`, cutoff height
`T = X^gamma`.  The forced-successor count in a height window is at least

```text
N >= c X^(2 lam (beta - sigma) - gamma (q(sigma) + theta)),
q(sigma) = 4 sigma (1 - sigma),
```

so the branching exponent relative to `T` is

```text
e_M = 2 lam (beta - sigma) / gamma - q(sigma) - theta.
```

Optimizing `gamma -> g = lam (1 - beta)` and `sigma -> 2/3+` (lambda cancels):

```text
e_M_max(beta) = 2 (beta - 2/3) / (1 - beta) - 8/9 - theta,
```

positive exactly for `beta > 10/13 = 0.7692...` when `theta = 0`
(exact-fraction check in the script; theta > 0 only shrinks e_M).

The toy iteration model (`toy_iteration.py`) confirms the structural side:
with a global-count-shaped top layer (average density `O(log T)`), the
per-node branching is `O(delta * log T)` — logarithmic, exponent kappa = 0 —
and the reachable set merely fills `[0, T]` (exponent 1).  A fixed
separation delta keeps `q(T)` bounded for Poisson gaps (`delta = 1` stalls
immediately, matching the Lean stall theorem).

## Verified results

1. **Design identities (A1-A6)**: all verified to machine precision,
   including the shared-outer-cap interval `epsilon < (3beta-2)/(1-beta)`
   (positive iff `beta > 2/3`) and the strict margins
   `F_R(1) = -lambda(beta-1/2)`, `F_L <= -etaLeft`.

2. **Coherent branching (B/B2)**: `e_M > 0` exactly for `beta > 10/13`
   (at `theta = 0`); e.g. `e_M = 0.40` at `beta = 0.8`, `1.79` at `0.9`
   (lam = 1.1, sigma = 2/3 + 0.005, gamma = g).  On `(2/3, 10/13]` the
   coherent mechanism cannot force more than `O(1)` successors.

3. **Toy iteration (toy_iteration.py)**: uniform-type top layers give
   max gap `~ 1/log T` (grid) or constant (Poisson); branching stays
   logarithmic (kappa = 0), reachable set grows like `T`; the cluster model
   shows that only a super-logarithmic local density can raise kappa.

## Consequences for the gate

- The coherent energy route closes the gate for seed zeros with
  `beta > 10/13`; its branching exponent is comfortably positive.
- The strip `(2/3, 10/13]` is **not covered** by the current mechanism
  family (coherent capacity + global counting).  Covering it requires
  either a strictly better capacity model (stronger than
  `sum m^2/|rho|^2 <= T^(q-2) log^5`), or a separation/density mechanism
  that raises the local top-layer density above the global average without
  the coherent energy input.
- `hdisjoint`/`hroots`/`hlower` remain structural (windows disjoint, seed
  nonempty, witnesses counted into `N(sigma, T+H)`); the decisive numeric
  gap is exactly the branching exponent on `(2/3, 10/13]`.

## Boundaries

Generated observations are not proofs.  Candidate theorems must be promoted
only after a clear Lean statement and proof strategy exist.
