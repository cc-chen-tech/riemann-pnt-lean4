# L1 compile-iteration battle plan (11 sorry blocks)

File: `PrimeNumberTheorem/HalfIsolatedZeroDichotomy/DetectionPointChoice.lean`
(531 lines; Appendix A and B fully proved; the 11 blocks below are in the
main assembly).  Order of attack (dependency order):

1. **L484 hN0** — membership bridge `complementary ⊆ nontrivialZerosFinset (T0+H)`
   from `him_pos`/`him_le`.  Needs: the finset membership characterization
   (`mem_nontrivialZerosFinset` from ZeroDensityCount/GlobalZeroCount) —
   `him_pos` gives `0 < Im ρ`, `him_le` gives `Im ρ ≤ T0+H`, so
   `|Im ρ| ≤ T0+H` follows; the zero-ness hypothesis is missing (the
   family is a *given* set of zeros, but the theorem takes no zero
   hypothesis!).  FIX OPTION: add hypothesis
   `∀ ρ ∈ complementary, RiemannHypothesis.IsNontrivialZero ρ` to the
   main theorem (harmless: callers pass actual zero families) — add it
   now, adjust the AxiomAudit expectations.

2. **L512 hwin constant** — `exists_windowedZeroMultiplicity_le` returns
   `C0 + 1` (its proof closes the constant); use that closed form here
   (rcases gives C'; prove `C' ≤ C0+1` by re-deriving, or restate the
   Appendix B theorem with an explicit constant instead of `∃ C`).

3. **L414 ringMass_le_windowedCount** — ring ⊆ height window
   `[γ - 2^(k+1)η, γ + 2^(k+1)η]`; use the hwin bound with
   `a = max(T0/2, γ - 2^(k+1)η)`, `b = min(T1, γ + 2^(k+1)η)`; the
   ring's zeros (Im ≥ T0/2 by the high-region hypothesis, Im ≤ T1) all
   lie in `[a, b]`; `b - a ≤ 2^(k+2)η`; also needs the bridge from the
   analytic multiplicity sum over a Finset subset to `riemannZeroCount`
   differences (`riemannZeroCount_sub_eq_between` from
   RiemannVonMangoldt/ZeroCount — already proved).

4. **L439 hringMass** — apply 3 to the filter subset (subset argument).

5. **L445 hpoint** — `2^⌊log x⌋ ≤ x` for `x = |γ-ρ.im|/η ≥ 1`
   (Mathlib: `Real.rpow_natCast` / `Nat.floor` lemmas; candidates
   `Real.log_le_log`, `Real.rpow_le_rpow`, or the existing
   `Nat.lt_floor_add_one` chain).

6. **L452 hsum_rings** — split `complementary` by
   `k = Nat.floor (log(|γ-ρ.im|/η))`, k < K; each class mass ≤ 3's bound;
   `Σ (1/2)^k ≤ 2`.

7. **L465 final constant cleaning** — `K ≤ log(T1/η)+3`,
   `η = H/(4 N0)` with `N0 = C0 T1 (1+log(T1+6))` (needs N0 as a
   parameter or re-derive inside), `T1/H ≥ 1`, `1+log(T1+6) ≤ 1+log T1`
   style chains; pure nlinarith/ring.

8. **L519 hsplit** — `Finset.sum_filter_add_sum_filter_not` or the
   partition lemma for the high/low split.

9. **L523 hhigh_bound** — dyadic (7's lemma) times `2/T0`
   (`1/|ρ| ≤ 2/T0` on the high region).

10. **L527 hlow_bound** — `|γ-ρ.im| ≥ T0/2` on the low region +
    `exists_globalReciprocalZeroMultiplicity_le_log_sq`.

11. **L528 final merge** — `high + low ≤ C (1+logT1)^2 T1/(T0 H)` using
    `T1/H ≥ 1` and the two bounds.

## Prerequisites check

- `riemannZeroCount_sub_eq_between` (ZeroCount.lean) — verified present.
- `mem_nontrivialZerosFinset` — verified present (ZeroDensityCount uses it).
- `exists_globalReciprocalZeroMultiplicity_le_log_sq` — verified present.
- `Int.floor_lt_ceil_of_lt` etc. — verified present (Appendix A already
  uses the Int interval lemmas).

## Boundary

Battle plan only; execution starts when the build reaches the repository
modules (mathlib tail is finishing now).
