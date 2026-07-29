import PrimeNumberTheorem.VKEdgeZeroClusterRemainderL2

open Complex MeasureTheory Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check jumpVonMangoldt_exp_ae_eq_zero
#check finiteZeroClusterPsiExplicitFormulaRemainderWithoutJump
#check normalizedFiniteZeroClusterPsiRemainderWithoutJump
#check normalizedFiniteZeroClusterPsiRemainderWithoutJumpSecondMoment
#check finiteZeroClusterPsiExplicitFormulaRemainder_ae_eq_withoutJump
#check normalizedFiniteZeroClusterPsiRemainder_ae_eq_withoutJump
#check normalizedFiniteZeroClusterPsiRemainderSecondMoment_eq_withoutJump
#check normalizedChebyshevPsiErrorAtExponent_ae_eq_neg_cluster_sub_withoutJump

example :
    (fun y : ℝ => jumpVonMangoldt (Real.exp y)) =ᵐ[volume] 0 :=
  jumpVonMangoldt_exp_ae_eq_zero

example
    (S : Finset ℂ) (T : ℝ) :
    (fun y =>
      finiteZeroClusterPsiExplicitFormulaRemainder S y T) =ᵐ[volume]
    (fun y =>
      finiteZeroClusterPsiExplicitFormulaRemainderWithoutJump S y T) :=
  finiteZeroClusterPsiExplicitFormulaRemainder_ae_eq_withoutJump S T

example
    (S : Finset ℂ) (T beta : ℝ) :
    (fun y =>
      normalizedFiniteZeroClusterPsiRemainder S T beta y) =ᵐ[volume]
    (fun y =>
      normalizedFiniteZeroClusterPsiRemainderWithoutJump S T beta y) :=
  normalizedFiniteZeroClusterPsiRemainder_ae_eq_withoutJump S T beta

example
    (S : Finset ℂ) (T beta a L : ℝ) :
    normalizedFiniteZeroClusterPsiRemainderSecondMoment S T beta a L =
      normalizedFiniteZeroClusterPsiRemainderWithoutJumpSecondMoment
        S T beta a L :=
  normalizedFiniteZeroClusterPsiRemainderSecondMoment_eq_withoutJump
    S T beta a L

example
    {S : Finset ℂ} {T beta : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T) :
    (fun y =>
      normalizedChebyshevPsiErrorAtExponent beta y) =ᵐ[volume]
    (fun y =>
      -normalizedFiniteZeroClusterContribution S
          (analyticOrderNatAt riemannZeta) beta y -
        normalizedFiniteZeroClusterPsiRemainderWithoutJump S T beta y) :=
  normalizedChebyshevPsiErrorAtExponent_ae_eq_neg_cluster_sub_withoutJump hS

end VKEdgePiOverTwo
end PrimeNumberTheorem
