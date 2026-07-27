import PrimeNumberTheorem.VKEdgeExplicitFormulaPairBridge

open Complex
open PrimeNumberTheorem VKEdgePiOverTwo

#check (explicitFormulaZeroResidueTerm : ℝ → ℂ → ℂ)
#check (explicitFormulaConjugatePairResidue : ℝ → ℂ → ℂ)
#check (normalizedExplicitFormulaConjugatePair : ℂ → ℝ → ℂ)
#check (finiteNontrivialZeroResidueRemainder : ℝ → ℝ → ℂ → ℂ)
#check (explicitFormulaClosedTerms : ℝ → ℂ)
#check (normalizedExplicitFormulaResidual : ℂ → ℝ → ℝ → ℂ)

#check (normalizedExplicitFormulaConjugatePair_eq_cosineModel :
  ∀ {rho : ℂ},
    RiemannHypothesis.IsNontrivialZero rho →
    0 < rho.im →
    ∀ y : ℝ,
      normalizedExplicitFormulaConjugatePair rho y =
        (normalizedCosineModelPair rho y : ℂ))

#check (finiteNontrivialZeroResidueSum_eq_neg :
  ∀ (x T : ℝ),
    (∑ z ∈ nontrivialZerosFinset T,
        explicitFormulaZeroResidueTerm x z) =
      -finiteNontrivialZeroSumWithMultiplicity x T)

#check (finiteNontrivialZeroResidueSum_eq_pair_add_remainder :
  ∀ {rho : ℂ} {x T : ℝ},
    RiemannHypothesis.IsNontrivialZero rho →
    0 < rho.im →
    |rho.im| ≤ T →
    (∑ z ∈ nontrivialZerosFinset T,
        explicitFormulaZeroResidueTerm x z) =
      explicitFormulaConjugatePairResidue x rho +
        finiteNontrivialZeroResidueRemainder x T rho)

#check (normalizedPsiModelResidual_eq_explicitFormulaResidual :
  ∀ {rho : ℂ} {T : ℝ},
    RiemannHypothesis.IsNontrivialZero rho →
    0 < rho.im →
    |rho.im| ≤ T →
    ∀ y : ℝ,
      (normalizedPsiModelResidual rho y : ℂ) =
        normalizedExplicitFormulaResidual rho T y)
