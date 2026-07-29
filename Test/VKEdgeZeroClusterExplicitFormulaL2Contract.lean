import PrimeNumberTheorem.VKEdgeZeroClusterExplicitFormulaL2

open Complex MeasureTheory Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check finiteZeroClusterComplementContribution
#check finiteZeroClusterPsiExplicitFormulaRemainder
#check normalizedChebyshevPsiErrorAtExponent
#check normalizedFiniteZeroClusterPsiRemainder
#check normalizedChebyshevPsiErrorSecondMoment
#check normalizedFiniteZeroClusterPsiRemainderSecondMoment
#check normalizedChebyshevPsiErrorAtExponent_eq_neg_cluster_sub_remainder
#check normalizedChebyshevPsiErrorSecondMoment_ge_cluster_sub_remainder
#check normalizedChebyshevPsiErrorSecondMoment_ge_localSeparation_sub_remainder
#check normalizedChebyshevPsiErrorSecondMoment_pos_of_localSeparation_remainder

example
    {S : Finset ℂ} {T beta y : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T) :
    normalizedChebyshevPsiErrorAtExponent beta y =
      -normalizedFiniteZeroClusterContribution S
          (analyticOrderNatAt riemannZeta) beta y -
        normalizedFiniteZeroClusterPsiRemainder S T beta y :=
  normalizedChebyshevPsiErrorAtExponent_eq_neg_cluster_sub_remainder hS

example
    {S : Finset ℂ} {x T : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T) :
    finiteNontrivialZeroSumWithMultiplicity x T =
      (∑ rho ∈ S,
        (analyticOrderNatAt riemannZeta rho : ℂ) * (x : ℂ) ^ rho / rho) +
      finiteZeroClusterComplementContribution S x T :=
  finiteNontrivialZeroSumWithMultiplicity_eq_cluster_add_complement hS

example
    {S : Finset ℂ} {T y : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T) :
    (((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ)) =
      -(∑ rho ∈ S,
          (analyticOrderNatAt riemannZeta rho : ℂ) *
            (Real.exp y : ℂ) ^ rho / rho) -
        finiteZeroClusterPsiExplicitFormulaRemainder S y T :=
  chebyshevPsi_sub_exp_eq_neg_cluster_sub_remainder hS

example
    {S : Finset ℂ} {T beta a L : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T)
    (hL : 0 ≤ L) :
    (1 / 2 : ℝ) *
          (∫ y in a..(a + L),
            ‖normalizedFiniteZeroClusterContribution S
              (analyticOrderNatAt riemannZeta) beta y‖ ^ 2) -
        normalizedFiniteZeroClusterPsiRemainderSecondMoment
          S T beta a L ≤
      normalizedChebyshevPsiErrorSecondMoment beta a L :=
  normalizedChebyshevPsiErrorSecondMoment_ge_cluster_sub_remainder hS hL

example
    {S : Finset ℂ} {T beta a L delta : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T)
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hband : ∀ rho ∈ S, beta - delta ≤ rho.re ∧ rho.re ≤ beta)
    (hsupport : (MathlibAux.mergedFrequencySupport S Complex.im).Nontrivial) :
    (1 / 4 : ℝ) *
          (L * finiteZeroClusterMergedEnergy S
              (analyticOrderNatAt riemannZeta) beta a -
            4 * Real.pi *
              finiteZeroClusterLocalSeparationEnergy S
                (analyticOrderNatAt riemannZeta) beta a) -
        (1 / 2 : ℝ) * L *
          (1 - Real.exp (-delta * L)) ^ 2 *
            finiteZeroClusterCoefficientMass S
              (analyticOrderNatAt riemannZeta) beta a ^ 2 -
        normalizedFiniteZeroClusterPsiRemainderSecondMoment
          S T beta a L ≤
      normalizedChebyshevPsiErrorSecondMoment beta a L :=
  normalizedChebyshevPsiErrorSecondMoment_ge_localSeparation_sub_remainder
    hS hL hdelta hband hsupport

example
    {S : Finset ℂ} {T beta a L delta : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T)
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hband : ∀ rho ∈ S, beta - delta ≤ rho.re ∧ rho.re ≤ beta)
    (hsupport : (MathlibAux.mergedFrequencySupport S Complex.im).Nontrivial)
    (hremainder :
      normalizedFiniteZeroClusterPsiRemainderSecondMoment S T beta a L <
        (1 / 4 : ℝ) *
            (L * finiteZeroClusterMergedEnergy S
                (analyticOrderNatAt riemannZeta) beta a -
              4 * Real.pi *
                finiteZeroClusterLocalSeparationEnergy S
                  (analyticOrderNatAt riemannZeta) beta a) -
          (1 / 2 : ℝ) * L *
            (1 - Real.exp (-delta * L)) ^ 2 *
              finiteZeroClusterCoefficientMass S
                (analyticOrderNatAt riemannZeta) beta a ^ 2) :
    0 < normalizedChebyshevPsiErrorSecondMoment beta a L :=
  normalizedChebyshevPsiErrorSecondMoment_pos_of_localSeparation_remainder
    hS hL hdelta hband hsupport hremainder

end VKEdgePiOverTwo
end PrimeNumberTheorem
