import PrimeNumberTheorem.ZeroDensityLayerBudgetSeparatedThirdOrderContourCarlson
import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderActualSynchronizedFormula

open Complex Set Filter Topology
open scoped ArithmeticFunction BigOperators

namespace PrimeNumberTheorem

/--
Synchronize the genuine second-smoothed explicit formula with the actual
reciprocal-cubic Carlson `L2` tail at one natural scale.

The middle-to-high energy uses analytic multiplicity squared and keeps the
strictly negative cubic block exponent visible.  An arbitrary finite set `S`
may be deleted.  The low layer is deliberately left untouched for a separate
Gram/Schur occupancy argument, while the intervening energy, contour error,
and actual Perron residual are simultaneously smaller than `epsilon`.
-/
theorem exists_actualThirdOrderPsiFormula_with_cubicHighToLowL2Tail
    {beta c : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1)
    (hc : 1 < c) (hcTwo : c ≤ 2) :
    ∃ sigma tau gammaLow : ℝ,
      1 / 2 < sigma ∧
      sigma < tau ∧
      tau < beta ∧
      0 < gammaLow ∧
      gammaLow ≤ (3 / 4 : ℝ) ∧
      cubicCarlsonL2BlockExponent beta sigma tau gammaLow < 0 ∧
      ∀ (certificate : CarlsonEventualMajorant sigma) (S : Finset ℂ)
          (ε : ℝ), 0 < ε →
        ∀ᶠ m : ℕ in atTop,
          ∃ T ∈ Icc ((m : ℝ) ^ (3 / 4 : ℝ))
              ((m : ℝ) ^ (3 / 4 : ℝ) + 1),
            ∃ (poles : Finset ℂ) (residue : ℂ → ℂ) (cubic : ℂ),
              ExplicitFormulaAux.goodHeight T ∧
              ‖ExplicitFormulaResidues.thirdOrderContourRemainder
                  (m : ℝ) (-1) c (T / (2 * Real.pi))‖ < ε ∧
              0 ∈ poles ∧
              (∀ p ∈ poles, (-1 : ℝ) < p.re ∧ p.re < c ∧
                -T < p.im ∧ p.im < T) ∧
              (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
              (∀ p ∈ poles, residue p =
                if p = 0 then residue 0
                else if p = 1 then ((m : ℝ) : ℂ)
                else -(analyticOrderNatAt riemannZeta p : ℂ) *
                  (((m : ℝ) : ℂ) ^ p) / p ^ 3) ∧
              residue 0 =
                iteratedDeriv 2
                  (ExplicitFormulaResidues.thirdOrderZeroCore (m : ℝ)) 0 / 2 ∧
              cubic = -deriv riemannZeta 0 / riemannZeta 0 ∧
              (m : ℝ) ^ (-beta) *
                  ‖(∑ p ∈ poles, residue p) -
                    ExplicitFormulaResidues.thirdOrderContourRemainder
                      (m : ℝ) (-1) c (T / (2 * Real.pi)) -
                    (secondSmoothedChebyshevPsi (m : ℝ) : ℂ)‖ < ε ∧
              actualCubicNormalizedSmoothedStripEnergyUpTo
                  beta sigma tau (3 / 4 : ℝ) S m =
                actualCubicNormalizedSmoothedStripEnergyUpTo
                    beta sigma tau gammaLow S m +
                  actualCubicNormalizedSmoothedStripEnergyBetween
                    beta sigma tau gammaLow (3 / 4 : ℝ) S m ∧
              actualCubicNormalizedSmoothedStripEnergyBetween
                  beta sigma tau gammaLow (3 / 4 : ℝ) S m < ε := by
  obtain ⟨sigma, tau, layerAlpha, gammaLow, gammaHigh,
      epsilonLow, epsilonHigh,
      hsigma, hsigmaTau, htauBeta, hsigmaOne,
      hcontourLayer, hlayerAlpha, hlayerAlphaOne,
      hgammaLowEq, hgammaLow, hgammaLowLayer,
      hgammaHighEq, hgammaHigh, hgammaHighLayer,
      hepsilonLow, hepsilonHigh,
      hlow, hhigh, hcarlsonLow, hcarlsonHigh,
      hcubicLow, hcubicHigh, hcubicLayer,
      htwoThirds, hthreeQuarters, hgammaLowContour,
      hcontour, htransfer⟩ :=
    exists_separatedThirdOrderContourHeight_with_actualCubicSmoothedHighToLowTransfer
      hbeta hbetaOne hc hcTwo
  refine ⟨sigma, tau, gammaLow,
    hsigma, hsigmaTau, htauBeta, hgammaLow,
    hgammaLowContour, hcubicLow, ?_⟩
  intro certificate S ε hε
  obtain ⟨hdecomposition, htail⟩ := htransfer certificate S
  have htailLt :
      ∀ᶠ m : ℕ in atTop,
        actualCubicNormalizedSmoothedStripEnergyBetween
            beta sigma tau gammaLow (3 / 4 : ℝ) S m < ε :=
    (tendsto_order.1 htail).2 ε hε
  have hformulaReal :=
    eventually_exists_goodHeight_thirdOrderActualPsiFormula_normalized_error_lt
      hbeta hc hcTwo ε hε
  have hformulaNat :=
    tendsto_natCast_atTop_atTop.eventually hformulaReal
  filter_upwards [hformulaNat, hdecomposition, htailLt] with
      m hmFormula hmDecomposition hmTail
  obtain ⟨T, hTwindow, poles, residue, cubic,
      hgood, hcontourSmall, hzero, hpoles, hpolesType,
      hresidue, hresidueZero, hcubic, hformulaSmall⟩ := hmFormula
  exact ⟨T, hTwindow, poles, residue, cubic,
    hgood, hcontourSmall, hzero, hpoles, hpolesType,
    hresidue, hresidueZero, hcubic, hformulaSmall,
    hmDecomposition, hmTail⟩

end PrimeNumberTheorem
