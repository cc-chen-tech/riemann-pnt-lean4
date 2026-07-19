# Weil Extremal-Kernel Preregistration

Status: preregistered infrastructure milestone, 2026-07-19

## Claim Boundary

This workstream studies finite restrictions of the Weil quadratic form and the
certificates needed to audit their signs. The first executable milestone is
infrastructure and a search protocol. It is not a proof of the Riemann
Hypothesis, a new zero-free region, or a new theorem about prime counting.

A finite rational matrix is not itself a Weil matrix. An exact certificate for
that rational matrix becomes evidence about the analytic matrix only after a
separate, rigorous enclosure argument proves the required relation between the
two matrices. Floating-point eigenvalues, however many digits are printed, do
not supply that relation.

## Second executable milestone outcome

The exact checker now accepts a symmetric rational interval matrix, factors
its rational center, verifies the inverse-transpose data exactly, and compares
a rigorous center lower bound with the maximum interval-radius row sum. The
corresponding Lean theorems prove that a symmetric entrywise perturbation with
that row budget preserves positive semidefiniteness, and preserves positive
definiteness when the budget inequality is strict.

This closes a generic finite interval-transfer step only. No entry of
`Q_infinity(100, 200)` or `Q_infinity(100, 250)` has been assembled or enclosed,
and no Guinand--Weil prime, pole, or Archimedean block has been connected to the
checker. Gates A and B therefore remain open.

## Registered Mathematical Target

Use the even-sector, cutoff-free Connes--van Suijlekom / Connes--Consani--
Moscovici Galerkin matrix in the normalization of Groskin's finite
Guinand--Weil dictionary. Write it as

```text
Q_infinity(c, N) in Sym_(N+1)(R).
```

The primary candidate theorem is the finite statement

```text
Q_infinity(100, 250) is positive semidefinite.
```

The matrix must be assembled from the closed-form prime, pole, and cutoff-free
archimedean blocks in the cited normalization. The even embedding, Fourier
normalization, index order `0, ..., N`, and sign convention must be recorded in
the experiment artifact. A result for a congruent matrix is acceptable only if
the change-of-basis matrix and its exact invertibility certificate are shipped.

This target is deliberately finite. Through the finite dictionary it concerns
an explicit 251-dimensional family of admissible band-limited test functions;
it does not establish positivity on all admissible test functions.

### Calibration Target

Before attempting the primary target, reproduce the published cutoff-free
interval-LDL result at

```text
(c, N) = (100, 200).
```

Reproduction is a required calibration gate and is not a strict improvement.

### Strict Improvement Rule

Only a rigorous positive-semidefinite certificate for the registered
`(100, 250)` cutoff-free matrix counts as a strict improvement over the
registered `(100, 200)` finite-band baseline. Any of the following is useful
infrastructure but not a strict mathematical improvement:

- certifying a rounded rational surrogate without an analytic enclosure;
- reproducing `N = 200`;
- reporting positive floating-point eigenvalues;
- certifying a principal submatrix of the `N = 250` matrix;
- certifying only a pole-neutral or moment-neutral subspace;
- certifying a finite-`T` archimedean truncation without the tail-order bridge.

## Literature Baseline

The baseline is frozen to the versions available on 2026-07-19.

1. Weil positivity is the classical RH-equivalent positivity problem for the
   Weil quadratic form. Bombieri and Yoshida developed finite or variational
   treatments; this milestone does not claim those mechanisms as new.
2. Connes and Consani, *Spectral triples and zeta-cycles*, Enseign. Math. 69
   (2023), 93--148, give concrete semilocal finite matrices and numerical
   investigations of their very small eigenvalues:
   <https://doi.org/10.4171/LEM/1049>.
3. Suzuki, *Weil's quadratic form via the screw function*,
   arXiv:2606.09096v1, gives a continuous-function framework for the
   distributional Weil form and explicitly states that its results do not
   assume RH: <https://arxiv.org/abs/2606.09096v1>.
4. Groskin, *A finite Guinand--Weil dictionary and archimedean tail order for
   the truncated Weil quadratic form*, arXiv:2607.02828v1, proves the exact
   finite dictionary, the pole-neutral family, and the archimedean tail order.
   Its released artifacts include a cutoff-free interval `LDL^T` audit at
   `(c, N) = (100, 200)` and explicitly make no RH claim:
   <https://arxiv.org/abs/2607.02828v1>.
5. Groskin, *High-Precision Approximation of Riemann Zeros via the Truncated
   Weil Form*, arXiv:2605.20224v2, reports computations through `N = 250` and
   warns that raw negative signs in deep spectra do not establish continuum
   negativity: <https://arxiv.org/abs/2605.20224v2>.

The registered novelty question is therefore not whether finite Weil matrices,
the finite dictionary, pole-neutrality, tail ordering, or interval LDL exist.
It is whether the published cutoff-free rigorous band can be extended from
`N = 200` to the fixed target `N = 250`, with a complete independent audit.

## Required Certificate Chain

A positive result must contain every link below.

1. **Assembly identity.** Two independent implementations produce enclosing
   intervals for every entry of the same `Q_infinity(100, N)`, and their
   intervals overlap entrywise.
2. **Symmetry.** The enclosure is exactly symmetrized by intersection, not by
   silently copying one triangle over the other.
3. **Rational reduction.** The artifact states an exact rational matrix and the
   rigorous perturbation or interval theorem that transfers its certificate to
   every real matrix in the analytic enclosure.
4. **Exact algebra.** A unit lower-triangular rational `L` and rational diagonal
   `D` satisfy `A = L D L^T` by exact arithmetic, with every diagonal entry of
   `D` nonnegative.
5. **Analytic transfer.** The lower margin after all interval, truncation, and
   basis-change budgets is nonnegative. A certificate for the rational center
   alone fails this gate.
6. **Independent replay.** A clean process verifies the JSON artifact using
   only the standard-library checker from this repository.

The first milestone implemented link 4 and exact artifact plumbing. The second
milestone implements a generic rational interval reduction and perturbation
transfer for links 3 and 5. Link 1 and the analytic instantiation of links 3
and 5 for the registered Weil matrix remain absent.

## Quantitative Gates

### Gate A: Baseline Reproduction

At `(c, N) = (100, 200)`:

- both assembly routes overlap entrywise;
- the exact checker accepts the emitted rational LDL certificate;
- the analytic transfer margin is at least zero;
- repeating at two precision settings separated by at least 512 bits preserves
  the certified inertia and narrows every entry enclosure;
- all artifact hashes and the replay command are present.

Failure of Gate A stops the `N = 250` claim search. Debugging may continue, but
no mathematical conclusion is registered.

### Gate B: Primary Success

At `(c, N) = (100, 250)`, all six certificate-chain links pass and the final
analytic lower margin is nonnegative. The result must survive reassembly at a
precision at least 512 bits higher than the first successful run.

Passing Gate B permits the narrow claim that the registered finite matrix is
positive semidefinite. It does not permit an RH claim.

### Gate C: Inconclusive/Failure

The run is `INCONCLUSIVE` if any candidate lower margin interval contains zero,
if the LDL process encounters a pivot whose sign is not rigorously determined,
or if independent entry enclosures fail to overlap. Three consecutive
precision doublings without a determined sign close this milestone as a
quantitative failure to certify, not as evidence of negativity.

The run is `FAILED_REPRODUCTION` if Gate A cannot be recovered from the frozen
normalization and source version.

### Gate D: Strict Negative

A negative result requires an exact nonzero rational vector `v` and a rigorous
upper bound

```text
v^T Q_infinity(100, N) v < 0.
```

For a finite-`T` assembly, it instead requires the finite value to lie strictly
below the full published tail budget, with all normalization constants audited.
A floating-point negative eigenvalue or a value in the tail uncertainty band is
`INCONCLUSIVE`.

Because the finite dictionary turns such a vector into an admissible test
function, a strict negative would be mathematically consequential. It must be
reproduced by both assembly routes, by an independent interval implementation,
and from a clean artifact before it is described as a candidate counterexample.

## Counterexample and Invalidating Conditions

A claimed certificate or counterexample is rejected if any condition holds:

- matrix dimension, basis order, even embedding, Fourier convention, or sign
  convention differs from the registered target without an exact bridge;
- the pole term is omitted without an exact pole-neutral constraint proof;
- prime powers at or below `c` are omitted or counted with the wrong weight;
- a finite archimedean cutoff is treated as cutoff-free;
- matrix entries are parsed through binary floating point before conversion to
  rationals;
- `L` is not exactly unit lower triangular, `D` has the wrong dimension, or
  exact reconstruction fails;
- the JSON digest, source digest, or replay command is missing or mismatched;
- only one numerical implementation produces the result;
- the witness changes after seeing unregistered parameter sweeps;
- a negative value is not below every stated error and tail budget.

Unexpected results trigger a normalization audit before any mathematical
interpretation.

## Reproducible Experiment Format

Every run is a UTF-8 JSON object. Rational numbers are canonical strings:
integers as `"n"`, nonintegers as `"n/d"` with `d > 0` and `gcd(n,d) = 1`.
No JSON floating-point number is allowed in a matrix, certificate, witness, or
bound.

Required top-level fields for the prototype artifact are:

```text
schema_version  = "weil-extremal-kernel-ldlt/v1"
claim_scope     = "finite-rational-matrix-only"
matrix          = square array of canonical rational strings
certificate     = {lower: square array, diagonal: array}
parameters      = JSON object, including c/N/sector when applicable
result          = {exact_reconstruction, nonnegative_diagonal, certified_psd}
payload_sha256  = SHA-256 of canonical JSON without this field
```

Analytic experiments must additionally record:

```text
git_commit, dirty, command, utc_timestamp
paper_versions and source URLs
source file SHA-256 values
assembly route and software versions
c, N, sector, basis order, normalization, cutoff mode
working precision in bits
entry interval matrix or a content-addressed path to it
rational reduction rule and transfer budget
archimedean cutoff T and tail budget, or cutoff_free=true
witness vector for a negative claim
independent replay result
```

Canonical JSON uses sorted keys, comma/colon separators without extra spaces,
and a terminal newline on disk. Large matrices may be stored as separate
content-addressed JSON files, but the manifest must retain their SHA-256 values.

## First-Milestone Deliverables

- this preregistration;
- a standard-library Python module for exact finite rational quadratic forms,
  exact unpivoted `LDL^T`, certificate checking, and canonical JSON artifacts;
- tests that demonstrate the red-green development cycle and reject tampering;
- a Lean module proving that an exact `LDL^T` representation with nonnegative
  diagonal makes the associated finite real quadratic form nonnegative;
- Lean contract and axiom-audit modules;
- targeted Python and Lean verification.

### Test-First Record

The Python tests were added before the implementation module. The first run was

```text
python3 -m pytest -q tests/test_weil_extremal_kernels.py
```

and exited `2` during collection with the expected missing-feature error:

```text
ImportError: cannot import name 'weil_extremal_kernels' from 'experiments.rh'
```

After implementing the module and making its runtime type alias compatible with
the repository's Python 3.9 interpreter, the same command reported `10 passed`.

## Known Mathematical Gap

The branch does not assemble `Q_infinity(c, N)`, prove interval containment for
its transcendental entries, or formalize the finite Guinand--Weil dictionary.
The generic interval-to-center perturbation theorem is now present, but no
analytic matrix enclosure instantiates it. Until those missing links are
closed, the executable checker certifies only the finite rational interval
matrix stored in its artifact.
