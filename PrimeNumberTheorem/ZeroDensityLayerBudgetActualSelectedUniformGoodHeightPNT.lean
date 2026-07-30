import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightMovingCarlsonPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderDecay

/-!
# PNT transfer at the canonical uniformly good height

This file removes the explicit-formula remainder certificate from the final
selected-height transfer.  The canonical selector already supplies that
certificate at every exponent in `(0, 1]`; only decay of the full finite-zero
tail remains as mathematical input.
-/

namespace PrimeNumberTheorem

open Filter

/-- A canonical height selected from `[x^innerAlpha - 1, x^innerAlpha]`
is eventually below every strictly larger polynomial height. -/
theorem eventually_selectedUniformGoodHeight_le_polynomialHeight
    {innerAlpha outerAlpha : ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ x : ℝ in atTop,
      selectedUniformGoodHeight innerAlpha selection x ≤
        carlsonPolynomialHeight outerAlpha x := by
  filter_upwards
      [eventually_selectedUniformGoodHeight_mem hinner selection,
        eventually_ge_atTop (1 : ℝ)] with x hx hxOne
  exact hx.2.trans (by
    simpa [carlsonPolynomialHeight] using
      Real.rpow_le_rpow_of_exponent_le hxOne hstrict.le)

/-- The fully automatic exact-height Carlson strip decay survives replacement
of `x^outerAlpha` by the canonical good height selected below
`x^innerAlpha`, provided `innerAlpha < outerAlpha`. -/
theorem tendsto_actualSelectedUniformGoodHeightMovingCarlsonStripMass_zero
    {innerAlpha outerAlpha : ℝ}
    {delta : ℕ → ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hdelta :
      ∀ᶠ m : ℕ in atTop,
        0 < delta m ∧ delta m ≤ 1 / 8 ∧
          128 * outerAlpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta) :
    Tendsto
      (actualSelectedHeightMovingCarlsonStripMass
        (selectedUniformGoodHeight innerAlpha selection) delta)
      atTop (nhds 0) := by
  have hheight :
      ∀ᶠ m : ℕ in atTop,
        selectedUniformGoodHeight innerAlpha selection (m : ℝ) ≤
          carlsonPolynomialHeight outerAlpha (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_selectedUniformGoodHeight_le_polynomialHeight
        hinner hstrict selection)
  have hexact :
      Tendsto
        (actualMovingCarlsonStripMass outerAlpha delta)
        atTop (nhds 0) :=
    tendsto_actualMovingCarlsonStripMass_zero_fullyAutomatic
      houter hdelta hgap
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun m =>
      actualSelectedHeightMovingCarlsonStripMass_nonneg
        (selectedUniformGoodHeight innerAlpha selection) delta m)
    ?_ hexact
  filter_upwards [hheight] with m hm
  exact actualSelectedHeightMovingCarlsonStripMass_le_exact hm

/-- At the canonical uniformly good height, decay of the full finite-zero tail
is enough to force decay of the relative `psi₀` error.  The explicit-formula
remainder certificate is generated automatically from the selector. -/
theorem tendsto_relativeChebyshevPsi0Error_of_selectedUniformGoodHeight_fullTail
    {alpha : ℝ}
    (halpha : 0 < alpha)
    (halphaOne : alpha ≤ 1)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hfull :
      Tendsto
        (fun m : ℕ =>
          dynamicFullPNTZeroTailNorm
            (selectedUniformGoodHeight alpha selection) (m : ℝ))
        atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop (nhds 0) := by
  apply tendsto_relativeChebyshevPsi0Error_of_dynamicFullPNTZeroTailNorm hfull
  exact
    selectedUniformGoodHeight_actualNaturalRemainderCertificate
      (beta := 1) (alpha := alpha)
      (by norm_num) halpha halphaOne (by simpa using halpha) selection

end PrimeNumberTheorem
