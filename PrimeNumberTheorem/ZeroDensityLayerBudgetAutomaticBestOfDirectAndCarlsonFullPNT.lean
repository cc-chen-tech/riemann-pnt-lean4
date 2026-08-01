import PrimeNumberTheorem.ZeroDensityLayerBudgetActualStrictMarginGridFullPNTEnvelopeDecay

/-!
# Automatic best-of-direct-and-Carlson full PNT bound

The actual strict-margin explicit-formula majorant and the dyadic Carlson
majorant both control the same real relative Chebyshev error. Their pointwise
minimum therefore retains error domination and convergence to zero.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Pointwise best bound supplied by two PNT error majorants. -/
def bestOfDirectAndCarlsonPNTErrorMajorant
    (direct carlson : ℕ → ℝ) (m : ℕ) : ℝ :=
  min (direct m) (carlson m)

/-- The pointwise minimum of two vanishing PNT majorants also vanishes. -/
theorem tendsto_bestOfDirectAndCarlsonPNTErrorMajorant_zero
    {direct carlson : ℕ → ℝ}
    (hdirect : Tendsto direct atTop (nhds 0))
    (hcarlson : Tendsto carlson atTop (nhds 0)) :
    Tendsto (bestOfDirectAndCarlsonPNTErrorMajorant direct carlson)
      atTop (nhds 0) := by
  simpa [bestOfDirectAndCarlsonPNTErrorMajorant] using
    hdirect.min hcarlson

/-- If the real PNT error is eventually controlled by both majorants, then it
is eventually controlled by their pointwise minimum. -/
theorem eventually_abs_relativeChebyshevPsi0Error_le_bestOfMajorants
    {direct carlson : ℕ → ℝ}
    (hdirect : ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤ direct m)
    (hcarlson : ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤ carlson m) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        bestOfDirectAndCarlsonPNTErrorMajorant direct carlson m := by
  filter_upwards [hdirect, hcarlson] with m hdirectM hcarlsonM
  exact le_min hdirectM hcarlsonM

/-- Automatic constants and actual grids for the pointwise best of the direct
strict-margin and dyadic Carlson full-PNT bounds. The two certified heights may
be different; only their bounds are combined. -/
theorem exists_automaticBestOfDirectAndCarlsonFullPNT :
    ∃ bDirect CDirect bCarlson gapRate D : ℝ,
      0 < bDirect ∧ 0 ≤ CDirect ∧
      0 < bCarlson ∧
      gapRate = classicalAdmissibleBalancedRate bCarlson / 2 ∧
      0 < gapRate ∧ 0 < D ∧
      IsCarlsonMovingDyadicLogPowerGap
        (classicalAdmissibleDyadicCarlsonGapWidth gapRate) ∧
      classicalAdmissibleVerifiedPNTDecayRate bCarlson = gapRate / 4 ∧
      ∀ (q : ℝ) (selection : UniformNaturalPointGoodHeightSelection),
        1 < q →
          ∃ (directGrid carlsonGrid : ActualPintzCarlsonGoodHeightRateGrid)
              (E eta CCarlson kappa : ℝ),
            directGrid.rates =
              {classicalAdmissibleBalancedRate (bDirect / q)} ∧
            directGrid.baseRate =
              classicalAdmissibleBalancedRate (bDirect / q) ∧
            classicalAdmissibleBalancedRate bDirect / q ≤
              directGrid.baseRate ∧
            directGrid.selection = selection ∧
            carlsonGrid.rates =
              {classicalAdmissibleBalancedRate bCarlson} ∧
            carlsonGrid.baseRate =
              classicalAdmissibleBalancedRate bCarlson ∧
            carlsonGrid.selection = selection ∧
            IsSelectedHeightDynamicZeroFree
              (actualPintzCarlsonRateCandidateHeight carlsonGrid
                (classicalAdmissibleBalancedRate bCarlson))
              (classicalAdmissibleDyadicCarlsonGapWidth gapRate) ∧
            0 ≤ E ∧ 0 < eta ∧ 0 ≤ CCarlson ∧ 0 < kappa ∧
            Tendsto
              (bestOfDirectAndCarlsonPNTErrorMajorant
                (actualStrictMarginGridFullPNTErrorMajorant
                  directGrid CDirect ((1 : ℝ) / q) bDirect 1)
                (classicalDyadicCarlsonClosedFormFullPNTErrorMajorant
                  bCarlson selection E eta CCarlson kappa D gapRate))
              atTop (nhds 0) ∧
            ∀ᶠ m : ℕ in atTop,
              |relativeChebyshevPsi0Error (m : ℝ)| ≤
                bestOfDirectAndCarlsonPNTErrorMajorant
                  (actualStrictMarginGridFullPNTErrorMajorant
                    directGrid CDirect ((1 : ℝ) / q) bDirect 1)
                  (classicalDyadicCarlsonClosedFormFullPNTErrorMajorant
                    bCarlson selection E eta CCarlson kappa D gapRate) m := by
  rcases
      exists_constants_automaticStrictMarginRateRecovery_PNT_majorant_decay with
    ⟨bDirect, CDirect, hbDirect, hCDirect, hdirect⟩
  rcases exists_automaticActualGrid_balancedDyadicCarlsonClosedFormFullPNT with
    ⟨bCarlson, gapRate, D, hbCarlson, hgapRateEq, hgapRate, hD,
      hgap, hverified, hcarlson⟩
  refine ⟨bDirect, CDirect, bCarlson, gapRate, D,
    hbDirect, hCDirect, hbCarlson, hgapRateEq, hgapRate, hD,
    hgap, hverified, ?_⟩
  intro q selection hq
  rcases hdirect q selection hq with
    ⟨directGrid, hdRates, hdBase, hdLower, hdSelection,
      hdDecay, hdError⟩
  rcases hcarlson selection with
    ⟨carlsonGrid, hcRates, hcBase, hcSelection, hcZeroFree,
      E, eta, CCarlson, kappa, hE, heta, hCCarlson, hkappa,
      hcDecay, hcError⟩
  refine ⟨directGrid, carlsonGrid, E, eta, CCarlson, kappa,
    hdRates, hdBase, hdLower, hdSelection,
    hcRates, hcBase, hcSelection, hcZeroFree,
    hE, heta, hCCarlson, hkappa, ?_, ?_⟩
  · exact tendsto_bestOfDirectAndCarlsonPNTErrorMajorant_zero
      hdDecay hcDecay
  · exact eventually_abs_relativeChebyshevPsi0Error_le_bestOfMajorants
      hdError hcError

end PrimeNumberTheorem
