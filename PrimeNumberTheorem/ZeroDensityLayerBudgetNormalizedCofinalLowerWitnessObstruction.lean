import PrimeNumberTheorem.ZeroDensityLayerBudgetAutomaticBestOfDirectAndCarlsonFullPNT

/-!
# Normalized cofinal lower-witness obstruction

This module exposes the precise interface between the automatic PNT upper
majorant and a future oscillation witness. A cofinal lower witness cannot have
an amplitude that asymptotically dominates the certified upper majorant.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- A cofinal sequence of PNT lower witnesses whose asserted amplitude
asymptotically dominates a proposed upper majorant. -/
def IsNormalizedCofinalPNTLowerWitness
    (upper : ℕ → ℝ) (witness : ℕ → ℕ) (amplitude : ℕ → ℝ) : Prop :=
  Tendsto witness atTop atTop ∧
  (∀ᶠ j : ℕ in atTop, 0 < amplitude j) ∧
  (∀ᶠ j : ℕ in atTop,
    amplitude j ≤
      |relativeChebyshevPsi0Error (witness j : ℝ)|) ∧
  Tendsto (fun j : ℕ => upper (witness j) / amplitude j)
    atTop (nhds 0)

/-- An eventual upper bound on the real PNT error excludes every normalized
cofinal lower witness for that same upper majorant. -/
theorem not_isNormalizedCofinalPNTLowerWitness_of_eventually_upper
    {upper : ℕ → ℝ}
    (hupper : ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤ upper m)
    (witness : ℕ → ℕ) (amplitude : ℕ → ℝ) :
    ¬ IsNormalizedCofinalPNTLowerWitness upper witness amplitude := by
  rintro ⟨hwitness, hamplitude, hlower, hratio⟩
  have hupperWitness : ∀ᶠ j : ℕ in atTop,
      |relativeChebyshevPsi0Error (witness j : ℝ)| ≤
        upper (witness j) :=
    hwitness.eventually hupper
  have hratioGe : ∀ᶠ j : ℕ in atTop,
      1 ≤ upper (witness j) / amplitude j := by
    filter_upwards [hamplitude, hlower, hupperWitness] with j hpositive hj hU
    apply (le_div_iff₀ hpositive).2
    simpa using hj.trans hU
  have hratioLt : ∀ᶠ j : ℕ in atTop,
      upper (witness j) / amplitude j < 1 :=
    (tendsto_order.1 hratio).2 1 zero_lt_one
  rcases (hratioGe.and hratioLt).exists with ⟨j, hge, hlt⟩
  exact (not_lt_of_ge hge) hlt

/-- For every good-height selector there is an automatically certified
best-of-direct-and-Carlson majorant which tends to zero, dominates the real PNT
error, and excludes normalized cofinal lower witnesses. -/
theorem exists_automaticBestPNTMajorant_with_normalizedLowerWitnessObstruction
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∃ upper : ℕ → ℝ,
      Tendsto upper atTop (nhds 0) ∧
      (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| ≤ upper m) ∧
      ¬ ∃ (witness : ℕ → ℕ) (amplitude : ℕ → ℝ),
        IsNormalizedCofinalPNTLowerWitness upper witness amplitude := by
  rcases exists_automaticBestOfDirectAndCarlsonFullPNT with
    ⟨bDirect, CDirect, bCarlson, gapRate, D,
      hbDirect, hCDirect, hbCarlson, hgapRateEq, hgapRate, hD,
      hgap, hverified, hautomatic⟩
  rcases hautomatic 2 selection (by norm_num : (1 : ℝ) < 2) with
    ⟨directGrid, carlsonGrid, E, eta, CCarlson, kappa,
      hdRates, hdBase, hdLower, hdSelection,
      hcRates, hcBase, hcSelection, hcZeroFree,
      hE, heta, hCCarlson, hkappa, hdecay, herror⟩
  let upper : ℕ → ℝ :=
    bestOfDirectAndCarlsonPNTErrorMajorant
      (actualStrictMarginGridFullPNTErrorMajorant
        directGrid CDirect ((1 : ℝ) / 2) bDirect 1)
      (classicalDyadicCarlsonClosedFormFullPNTErrorMajorant
        bCarlson selection E eta CCarlson kappa D gapRate)
  refine ⟨upper, hdecay, herror, ?_⟩
  rintro ⟨witness, amplitude, hwitness⟩
  exact
    (not_isNormalizedCofinalPNTLowerWitness_of_eventually_upper
      herror witness amplitude) hwitness

end PrimeNumberTheorem
