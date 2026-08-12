import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicLowSummedGaussianL2
import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderActualL2SynchronizedTransfer

open Complex Set Filter Topology
open scoped ArithmeticFunction BigOperators

namespace PrimeNumberTheorem

/--
Synchronize the genuine third-order explicit formula with the complete direct
`L2` budget from the low dyadic range through the middle-to-high tail.

The low range is the sum of the actual Gaussian Gram forms over every dyadic
block up to `m ^ gammaLow`.  Its only extra input is a uniform unit-bucket
occupancy bound, supplied independently by the half-isolated argument.  The
result uses the exact finite low-block capacities followed by the existing
Carlson `log^5` tail; summing the blocks introduces neither a new logarithmic
loss nor a square of the number of blocks.  The remaining energy between
`m ^ gammaLow` and the contour height is absorbed into `epsilon`.
-/
theorem exists_actualThirdOrderPsiFormula_with_cubicDirectL2Budget
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
          (t width : ℝ) (occupancy : ℕ),
        0 ≤ t →
        1 ≤ width →
        (∀ᶠ m : ℕ in atTop,
          ∀ n ∈ Finset.range (actualCubicDyadicPolynomialCut gammaLow m + 1),
            ∀ q ∈ Finset.image actualCubicDyadicUnitBucket
                (actualCarlsonDyadicZeroStrip sigma tau n \ S),
              {rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S |
                  actualCubicDyadicUnitBucket rho = q}.card ≤ occupancy + 1) →
        ∃ B, 0 ≤ B ∧ ∃ N, ∀ (epsilon : ℝ), 0 < epsilon →
          ∀ᶠ m : ℕ in atTop,
            ∃ T ∈ Icc ((m : ℝ) ^ (3 / 4 : ℝ))
                ((m : ℝ) ^ (3 / 4 : ℝ) + 1),
              ∃ (poles : Finset ℂ) (residue : ℂ → ℂ) (cubic : ℂ),
                ExplicitFormulaAux.goodHeight T ∧
                ‖ExplicitFormulaResidues.thirdOrderContourRemainder
                    (m : ℝ) (-1) c (T / (2 * Real.pi))‖ < epsilon ∧
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
                      (secondSmoothedChebyshevPsi (m : ℝ) : ℂ)‖ < epsilon ∧
                actualCubicNormalizedSmoothedStripEnergyUpTo
                    beta sigma tau (3 / 4 : ℝ) S m =
                  actualCubicNormalizedSmoothedStripEnergyUpTo
                      beta sigma tau gammaLow S m +
                    actualCubicNormalizedSmoothedStripEnergyBetween
                      beta sigma tau gammaLow (3 / 4 : ℝ) S m ∧
                actualCubicNormalizedLowDyadicGaussianGramExcluding
                      beta sigma tau gammaLow S t width m +
                    actualCubicNormalizedSmoothedStripEnergyBetween
                      beta sigma tau gammaLow (3 / 4 : ℝ) S m <
                  MathlibAux.gaussianBucketSchurConstant * (occupancy + 1 : ℕ) *
                      actualCubicNormalizedLowDyadicL2CapacityMajorant
                        certificate B beta tau gammaLow N m + epsilon := by
  obtain ⟨sigma, tau, gammaLow,
      hsigma, hsigmaTau, htauBeta, hgammaLow,
      hgammaLowContour, hcubicLow, hsync⟩ :=
    exists_actualThirdOrderPsiFormula_with_cubicHighToLowL2Tail
      hbeta hbetaOne hc hcTwo
  refine ⟨sigma, tau, gammaLow,
    hsigma, hsigmaTau, htauBeta, hgammaLow,
    hgammaLowContour, hcubicLow, ?_⟩
  intro certificate S t width occupancy ht hwidth hoccupancy
  obtain ⟨B, hB, N, hcapacity⟩ :=
    exists_actualCubicNormalizedLowDyadicGaussianGramExcluding_le_lowDyadicL2CapacityMajorant
      certificate
  refine ⟨B, hB, N, ?_⟩
  intro epsilon hepsilon
  have hmOne : ∀ᶠ m : ℕ in atTop, 1 ≤ m := eventually_ge_atTop 1
  filter_upwards [hsync certificate S epsilon hepsilon, hoccupancy, hmOne] with
      m hmFormula hmOccupancy hmOne
  obtain ⟨T, hTwindow, poles, residue, cubic,
      hgood, hcontourSmall, hzero, hpoles, hpolesType,
      hresidue, hresidueZero, hcubic, hformulaSmall,
      hdecomposition, htailSmall⟩ := hmFormula
  have hlow :=
    hcapacity beta tau gammaLow S t width occupancy m
      hmOne ht hwidth hmOccupancy
  refine ⟨T, hTwindow, poles, residue, cubic,
    hgood, hcontourSmall, hzero, hpoles, hpolesType,
    hresidue, hresidueZero, hcubic, hformulaSmall,
    hdecomposition, ?_⟩
  exact add_lt_add_of_le_of_lt hlow htailSmall

end PrimeNumberTheorem
