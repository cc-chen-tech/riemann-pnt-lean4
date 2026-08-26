# Carlson Two-Thirds Improvement Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize Carlson's mollifier-length no-go, the endpoint-saving optimization, the explicit two-scale `5/64` exponent ledger, and a single-layer forcing theorem with separate forcing and density exponents, while isolating the still-unformalized Conrey--Deshouillers--Iwaniec normalization and L2 interpolation input.

**Architecture:** Pure real-linear minimax algebra lives in one small module. Exact DI parameter arithmetic lives in a second module and proves only rational inequalities. A generalized density certificate and forcing contradiction live above the existing zero-density count interfaces. The published analytic estimate enters only through an explicit proposition-valued certificate whose unconditional constructor is a separate final task.

**Tech Stack:** Lean 4.33.0, Mathlib, Lake contract files, `#print axioms`, Markdown mathematical audit.

**Spec:** `docs/superpowers/specs/2026-08-26-carlson-two-thirds-improvement-design.md`

## Global constraints

- No `sorry`, `admit`, or new mathematical axiom.
- Do not call a conditional certificate an unconditional zero-density theorem.
- Preserve the distinction between Carlson internal retuning, Carlson plus DI large values, and direct Ingham replacement.
- Each production module begins with a contract import that is observed failing before implementation.
- Fresh focused builds, contract builds, `#print axioms`, `git diff --check`, and final `lake build` are required before a completion claim.

### Task 1: Carlson endpoint minimax and uniqueness

**Files:**
- Create: `PrimeNumberTheorem/CarlsonLengthMinimax.lean`
- Create: `Test/CarlsonLengthMinimaxContract.lean`

**Interfaces:**
- `carlsonLowerEndpointExponent sigma x`
- `carlsonUpperEndpointExponent sigma x`
- `carlsonEndpointBalance`
- `carlson_endpoint_max_ge_optimum`
- `carlson_endpoint_max_eq_optimum_iff`
- `carlson_twoThirds_endpoint_formulas`
- `carlson_twoThirds_length_minimax`

- [x] Create a contract importing the absent production module and checking the exact formulas, unique equality case, and `sigma=2/3` specialization.
- [x] Run `lake env lean Test/CarlsonLengthMinimaxContract.lean` and record the missing-module failure.
- [x] Implement definitions and prove the two half-line cases using `max`, `linarith`, and `ring`.
- [x] Re-run the contract and require exit code `0`.
- [x] Add `#print axioms` for the two minimax theorems.

### Task 2: Fixed endpoint savings

**Files:**
- Modify: `PrimeNumberTheorem/CarlsonLengthMinimax.lean`
- Modify: `Test/CarlsonLengthMinimaxContract.lean`

**Interfaces:**
- `carlsonSavedLowerEndpointExponent sigma deltaL x`
- `carlsonSavedUpperEndpointExponent sigma deltaU x`
- `carlsonSavedBalance sigma deltaL deltaU`
- `carlsonSavedOptimum sigma deltaL deltaU`
- `carlson_saved_endpoint_max_ge_optimum`
- `carlson_saved_endpoint_max_eq_optimum_iff`
- `carlson_twoThirds_saved_optimum`

- [x] Add contract assertions for the balance point and the formula
  `4*sigma*(1-sigma) - 2*(1-sigma)*deltaL - (2*sigma-1)*deltaU`.
- [x] Run the contract and observe failure from missing declarations.
- [x] Implement the saved endpoint definitions and unique minimax proof.
- [x] Re-run the contract and require exit code `0`.

### Task 3: Exact DI exponent ledger

**Files:**
- Create: `PrimeNumberTheorem/CarlsonTwoThirdsDIExponent.lean`
- Create: `Test/CarlsonTwoThirdsDIExponentContract.lean`

**Interfaces:**
- exact constants `diCoreExponent`, `diOuterExponent`, `diRightBoundary`, `diEpsilon`, `diInterpolationWeight`, `diInterpolatedExponent`, `diTargetExponent`, `diDelta`
- `di_twoScale_length_range`
- `di_interpolated_exponent_eq`
- `di_interpolated_exponent_lt_target`
- `di_lower_endpoint_lt_target`
- `di_target_eq_carlson_sub_delta`
- `di_fourteenSeventeenths_margin`
- `di_separated_threshold_eq`

- [x] Create the contract with `example` statements for every exact rational identity and inequality.
- [x] Run it and record the missing-module failure.
- [x] Implement only rational definitions and `norm_num`/`ring` proofs; no analytic estimate is declared here.
- [x] Re-run contract and add `#print axioms` for all exported exponent theorems.

### Task 4: General density certificate with a free exponent

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityExponentCertificate.lean`
- Create: `Test/ZeroDensityExponentCertificateContract.lean`

**Interfaces:**
- `ZeroDensityEventualMajorant sigma q B`
- `ZeroDensityEventualMajorant.isBigO`
- `ZeroDensityEventualMajorant.mono_exponent`
- `CarlsonDIImprovedDensityCertificate`
- `CarlsonDIImprovedDensityCertificate.isBigO`

- [x] Write a contract that constructs a generic certificate from an eventual inequality and converts it to `IsBigO`.
- [x] Run the contract and observe missing declarations.
- [x] Implement the generic record and elementary conversion lemmas.
- [x] Define the DI improved-density certificate transparently as the generic exponent `467/576`, log-power `6` certificate; do not provide an unconditional constructor.
- [x] Prove that a populated certificate yields the corresponding `IsBigO` theorem.
- [x] Re-run the contract and audit axioms.

### Task 5: Separate forcing and density exponents

**Files:**
- Create: `PrimeNumberTheorem/SingleLayerForcingSeparatedDensity.lean`
- Create: `Test/SingleLayerForcingSeparatedDensityContract.lean`

**Interfaces:**
- `singleLayerForcing_density_contradiction`
- `singleLayerForcing_DI_contradiction`
- `separatedDensity_gap_at_fourteen_seventeenths`
- `no_nontrivial_zero_re_gt_14_over_17_of_forcing_and_DI`

- [x] Write a failing contract for a theorem whose forcing lower exponent uses `qF` and whose upper certificate uses `qD`.
- [x] Run the contract and observe missing declarations.
- [x] Generalize the normalization argument from `singleLayerForcing_carlson_contradiction`, reusing `powerGrowth_logGap_contradiction`.
- [x] Specialize to `sigma=2/3`, `qF=8/9`, `qD=467/576`, prove the direct margin `15/1088`, and connect a supplied DI density certificate to the existing terminal exclusion shape.
- [x] Re-run the contract and audit axioms.

### Task 6: Root integration and focused verification

**Files:**
- Modify: `PrimeNumberTheorem.lean`
- Modify: `lakefile.lean`
- Create: `Test/CarlsonTwoThirdsImprovementAxiomAudit.lean`

- [x] Add the new modules and contracts to the Lake roots. (`PrimeNumberTheorem.lean` is a foundational module, not an aggregate importer, so adding imports there would create cycles.)
- [x] Build all new production modules and contract files.
- [x] Run the axiom audit and require only `propext`, `Classical.choice`, and `Quot.sound` where inherited analysis needs them; pure algebra should have no unexpected axioms.
- [x] Run `rg -n 'sorry|admit|^axiom ' <new files>` and `git diff --check`.

Focused integration evidence: all new roots built successfully in one Lake run
(`8756/8756`, exit code `0`).  A subsequent default `lake build` exposed an
unrelated `origin/main` root-list defect: `HardyTheorem.ConreyLittlewoodMeanSquare`
imports the existing source `MathlibAux.LogMeanSquare`, but that module is not a
Lake root, so its `.olean` was absent.  The failed full run was stopped after
this deterministic upstream failure; no new Carlson target failed.

### Task 7: Analytic local-to-global Carlson assembly

**Files:**
- Create: `PrimeNumberTheorem/CarlsonGaussianL2ThreeLines.lean`
- Create: `PrimeNumberTheorem/CarlsonDILocalDensity.lean`
- Create: `Test/CarlsonDILocalDensityContract.lean`

**Interfaces:**
- a generic mollifier coefficient interface and a real mollified-error mean-square input
- Gaussian-window boundary L2 hypotheses
- L2 three-lines interpolation for the regularized detector
- local zero count bound in one Gaussian window
- `O(log U)` window cover of `[U,2U]`
- dyadic summation to `ZeroDensityEventualMajorant (2/3) (467/576) 6`

- [ ] State the exact L2 three-lines theorem using existing Fourier/Plancherel infrastructure and prove it without adding a hypothesis that already contains the conclusion.
- [x] Extract the existing fixed-right contour theorem with the *actual* mollified-error integral on the left, before the classical sharp endpoint is substituted.
- [ ] Generalize the detector from the repository's sharp Mobius cutoff to a finite coefficient family with constant coefficient one.
- [ ] Connect the fixed-right contour selection to the Gaussian/global L2 count.
- [ ] Prove the finite window cover and dyadic summation, keeping every logarithmic loss explicit.
- [ ] Assemble the proved components into `CarlsonDIImprovedDensityCertificate`.
- [ ] Run focused contracts and axiom audit.

### Task 8: Two-scale Conrey--Deshouillers--Iwaniec input

**Files:**
- Create: `PrimeNumberTheorem/DeshouillersIwaniecMollifiedMeanSquare.lean`
- Create: `Test/DeshouillersIwaniecMollifiedMeanSquareContract.lean`
- Modify: `PrimeNumberTheorem/CarlsonDILocalDensity.lean`

**Interfaces:**
- exact core exponent `57/100` and outer exponent `571/1000`
- the plateau/taper weight, with exact reciprocal cancellation through the core
- its identity as a fixed linear combination of two linear Selberg mollifiers
- Conrey Theorem 2 for each Selberg component, normalized to the required height weight
- a constructor for the critical-boundary input used by the local-density assembly

- [ ] Formalize the two-scale weight identity and the exact vanishing of the coefficients of `zeta M - 1` through `T^(57/100)`.
- [ ] Formalize Conrey's published `theta < 4/7` mean square, including the slight horizontal shift and smooth height weight; the underlying Kloosterman/Kuznetsov input must not be hidden in an axiom.
- [ ] Combine the two component bounds by the elementary square inequality and test the `57/100 < 571/1000 < 4/7` specialization.
- [ ] Only after this constructor and Task 7 compile, expose the unconditional `N(2/3,T)=O(T^(467/576)(log T)^6)` theorem.
- [ ] Run full `lake build`, repository tests, axiom allowlist, and `git diff --check` with exit code `0`.
