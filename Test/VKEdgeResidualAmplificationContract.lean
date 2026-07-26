import PrimeNumberTheorem.VKEdgeResidualAmplification

open MeasureTheory Set
open PrimeNumberTheorem VKEdgePiOverTwo

#check cosineZeroPair
#check intervalIntegral_cosineZeroPair_sq
#check integral_Icc_cosineZeroPair_sq_le
#check normalizedTargetZeroPair
#check normalizedPsiResidual
#check measurable_normalizedTargetZeroPair
#check measurable_normalizedPsiResidual
#check integrableOn_normalizedTargetZeroPair_sq_Icc
#check integrableOn_normalizedPsiResidual_sq_Icc
#check integral_Icc_normalizedTargetZeroPair_sq_le
#check one_div_pi_le_sharpenedMissingHarmonicDenominator
#check one_le_centeredSharpenedProjectedPsiKernelEnvelopeConstant
#check centeredSharpenedSweptOrdinaryL2Constant_lt_targetPairHalfEnergy

example
    {m gamma phase a b : ℝ} (hgamma : gamma ≠ 0) :
    (∫ y in a..b, cosineZeroPair m gamma phase y ^ 2) =
      2 * m ^ 2 * (b - a) +
        m ^ 2 / gamma *
          (Real.sin (2 * gamma * b - 2 * phase) -
            Real.sin (2 * gamma * a - 2 * phase)) :=
  intervalIntegral_cosineZeroPair_sq hgamma

example
    {m gamma phase a b : ℝ}
    (hab : a ≤ b) (hgamma : gamma ≠ 0) :
    (∫ y in Icc a b, cosineZeroPair m gamma phase y ^ 2) ≤
      2 * m ^ 2 * (b - a) + 2 * m ^ 2 / |gamma| :=
  integral_Icc_cosineZeroPair_sq_le hab hgamma

example
    {rho : ℂ} {a b : ℝ}
    (hab : a ≤ b) (hgamma : rho.im ≠ 0) :
    (∫ y in Icc a b, normalizedTargetZeroPair rho y ^ 2) ≤
      2 * (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 * (b - a) +
        2 * (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / |rho.im| :=
  integral_Icc_normalizedTargetZeroPair_sq_le hab hgamma

example
    {epsilon : ℝ} {rho : ℂ} {k : ℕ}
    (hepsilon : 0 < epsilon)
    (hrho1 : rho ≠ 1)
    (hzero : riemannZeta rho = 0) :
    centeredSharpenedSweptOrdinaryL2Constant epsilon rho k <
      epsilon * (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 :=
  centeredSharpenedSweptOrdinaryL2Constant_lt_targetPairHalfEnergy
    hepsilon hrho1 hzero
