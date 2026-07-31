import PrimeNumberTheorem.VKEdgeResidualAmplification

open MeasureTheory Set
open PrimeNumberTheorem VKEdgePiOverTwo

#check cosinePairModel
#check normalizedCosineModelPair
#check normalizedPsiModelResidual
#check epsilonLogWindowCosineModelCoefficient

#check (intervalIntegral_cosinePairModel_sq :
  ∀ {m gamma phase a b : ℝ}, gamma ≠ 0 →
    (∫ y in a..b, cosinePairModel m gamma phase y ^ 2) =
      2 * m ^ 2 * (b - a) +
        m ^ 2 / gamma *
          (Real.sin (2 * gamma * b - 2 * phase) -
            Real.sin (2 * gamma * a - 2 * phase)))

#check (integral_Icc_cosinePairModel_sq_le :
  ∀ {m gamma phase a b : ℝ},
    a ≤ b → gamma ≠ 0 →
    (∫ y in Icc a b, cosinePairModel m gamma phase y ^ 2) ≤
      2 * m ^ 2 * (b - a) + 2 * m ^ 2 / |gamma|)

#check (measurable_normalizedCosineModelPair :
  ∀ rho : ℂ, Measurable (normalizedCosineModelPair rho))

#check (measurable_normalizedPsiModelResidual :
  ∀ rho : ℂ, Measurable (normalizedPsiModelResidual rho))

#check (integrableOn_normalizedCosineModelPair_sq_Icc :
  ∀ (rho : ℂ) (a b : ℝ),
    IntegrableOn (fun y => normalizedCosineModelPair rho y ^ 2)
      (Icc a b))

#check (integrableOn_normalizedPsiModelResidual_sq_Icc :
  ∀ {rho : ℂ}, rho.re < 1 → ∀ a b : ℝ,
    IntegrableOn (fun y => normalizedPsiModelResidual rho y ^ 2)
      (Icc a b))

#check (integral_Icc_normalizedCosineModelPair_sq_le :
  ∀ {rho : ℂ} {a b : ℝ},
    a ≤ b → rho.im ≠ 0 →
    (∫ y in Icc a b, normalizedCosineModelPair rho y ^ 2) ≤
      2 * (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 * (b - a) +
        2 * (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / |rho.im|)

#check (one_div_pi_le_sharpenedMissingHarmonicDenominator :
  ∀ k : ℕ, 1 / Real.pi ≤ sharpenedMissingHarmonicDenominator k)

#check (one_le_centeredSharpenedProjectedPsiKernelEnvelopeConstant :
  ∀ (q : ℝ) (rho : ℂ) (k : ℕ),
    1 ≤ centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k)

#check (
  centeredSharpenedSweptOrdinaryL2Constant_lt_cosineModelHalfEnergy :
  ∀ {epsilon : ℝ} {rho : ℂ} {k : ℕ},
    0 < epsilon →
    rho ≠ 1 →
    riemannZeta rho = 0 →
    centeredSharpenedSweptOrdinaryL2Constant epsilon rho k <
      epsilon * (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2)

#check (integral_Icc_normalizedPsiModelResidual_sq_lower :
  ∀ {rho : ℂ} {a b A B : ℝ},
    rho.re < 1 →
    a ≤ b →
    rho.im ≠ 0 →
    0 ≤ A →
    0 ≤ B →
    B < A →
    A * (b - a) ≤
      ∫ y in Icc a b, normalizedPsiError rho y ^ 2 →
    (∫ y in Icc a b, normalizedCosineModelPair rho y ^ 2) ≤
      B * (b - a) →
    (Real.sqrt A - Real.sqrt B) ^ 2 * (b - a) ≤
      ∫ y in Icc a b, normalizedPsiModelResidual rho y ^ 2)

#check (
  integral_Icc_normalizedCosineModelPair_sq_le_epsilonLogWindow :
  ∀ {epsilon Y : ℝ} {rho : ℂ},
    0 < epsilon →
    1 < Y →
    rho.im ≠ 0 →
    (∫ y in Icc (Real.log Y) ((1 + epsilon) * Real.log Y),
        normalizedCosineModelPair rho y ^ 2) ≤
      epsilonLogWindowCosineModelCoefficient epsilon rho Y *
        (epsilon * Real.log Y))

#check (integral_Icc_normalizedPsiModelResidual_sq_lower_epsilonLogWindow :
  ∀ {epsilon Y A : ℝ} {rho : ℂ},
    rho.re < 1 →
    0 < epsilon →
    1 < Y →
    rho.im ≠ 0 →
    0 ≤ A →
    epsilonLogWindowCosineModelCoefficient epsilon rho Y < A →
    A * (epsilon * Real.log Y) ≤
      ∫ y in Icc (Real.log Y) ((1 + epsilon) * Real.log Y),
        normalizedPsiError rho y ^ 2 →
    (Real.sqrt A -
        Real.sqrt
          (epsilonLogWindowCosineModelCoefficient epsilon rho Y)) ^ 2 *
          (epsilon * Real.log Y) ≤
      ∫ y in Icc (Real.log Y) ((1 + epsilon) * Real.log Y),
        normalizedPsiModelResidual rho y ^ 2)
