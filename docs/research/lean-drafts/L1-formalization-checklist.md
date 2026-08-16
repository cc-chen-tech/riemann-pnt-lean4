# L1 formalization checklist (drafts -> modules)

## Drafts (docs/research/lean-drafts/, uncompiled)

1. `DetectionPointChoiceGridDraft.lean` — Appendix A, grid covering lemma
2. `WindowedCountDraft.lean` — Appendix B, windowed zero count
3. `DetectionPointChoiceMainDraft.lean` — main assembly (Steps 0-2)

## Promotion order

1. Prove Appendix A as
   `PrimeNumberTheorem/HalfIsolatedZeroDichotomy/DetectionPointChoice.lean`
   (replacing the axiom `exists_point_avoiding_small_intervals`).
   - Mathlib names VERIFIED against local sources (2026-08-15):
     - `Int.card_Ioo` (`Mathlib/Data/Int/Interval.lean:105`):
       `#(Ioo a b) = (b - a - 1).toNat` — the integer-count fact;
     - `Finset.card_biUnion_le` (used in
       `Mathlib/NumberTheory/SmoothNumbers.lean:515`);
     - `Int.ceil_add_le` (`Mathlib/Algebra/Order/Floor/Ring.lean:699`):
       `⌈a + b⌉ ≤ ⌈a⌉ + ⌈b⌉` — sum of ceilings bound, no slack term
       needed;
     - `Int.ceil_add_natCast` / `Int.ceil_add_one` (same file).
   - The draft's `sum_ceil_bound` can be strengthened to
     `Σ ⌈f i⌉ ≤ ⌈Σ f i⌉` (exact, via `ceil_add_le` induction).
2. Prove Appendix B in the same file (replacing
   `exists_windowedZeroMultiplicity_le`).  Decision recorded here: state it
   with `riemannZeroCount` (positive-imaginary count, matches
   `exists_abs_riemannZeroCount_sub_mainTerm_le_log`) and add a separate
   bridge `globalZeroMultiplicity = 2 * riemannZeroCount`-style lemma if a
   global-count consumer appears (real non-trivial zeros do not exist on
   `(0,1)`, so the symmetry bridge should be provable from the existing
   nontrivial-zero symmetry modules).
   - Mathlib names VERIFIED against local sources (2026-08-15):
     - `norm_image_sub_le_of_norm_deriv_le_segment`
       (`Mathlib/Analysis/Calculus/MeanValue.lean:337`) — the mean value
       step for the main-term difference;
     - `hasDerivAt_riemannVonMangoldtMainTerm` (repo,
       `RiemannVonMangoldt/AllHeightAsymptotic.lean:10`) — derivative
       `log(T/2π)/2π`.
3. Prove the main assembly (Steps 0-2) as `exists_good_detection_point`
   and delete the axiom.  All inputs then present:
   - `exists_card_nontrivialZerosFinset_le_mul_log` (N0);
   - `exists_globalReciprocalZeroMultiplicity_le_log_sq` (low part);
   - Appendix B (I2, dyadic shells);
   - Appendix A (avoidance).
4. Update `Test/DetectionPointChoiceAxiomAudit.lean`: after each
   promotion the corresponding `#print axioms` line must shrink; the end
   state is an empty target list.

## Open design decisions

- Constants: the draft keeps `∃ C` forms; the final theorem may fix an
  explicit (large) constant, which is fine because the downstream L3
  comparison only needs the exponent shape.
- `η` denominator: `H / (4 N0)` with `N0 = C0 T1 (1 + log(T1+6))`; verify
  `H / (4 N0) > 0` and the `Σ 2η ≤ H/2` arithmetic once `C0` is fixed.

## Boundaries

Drafts only; promotion starts only when a local build environment is
available (shared `vendor/mathlib` cache contention made local builds
unusable at the time of writing).
