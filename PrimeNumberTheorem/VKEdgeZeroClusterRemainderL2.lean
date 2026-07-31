import PrimeNumberTheorem.VKEdgeZeroClusterExplicitFormulaL2

open Complex MeasureTheory Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Removing the Chebyshev jump from logarithmic local second moments

The midpoint correction in the exact explicit formula is supported at the
countable set of logarithms of natural numbers.  It therefore vanishes almost
everywhere in the logarithmic variable and contributes exactly zero to every
continuous local second moment.
-/

/-- The Chebyshev jump at `exp y` vanishes for Lebesgue-almost every
logarithmic coordinate `y`. -/
theorem jumpVonMangoldt_exp_ae_eq_zero :
    (fun y : ℝ => jumpVonMangoldt (Real.exp y)) =ᵐ[volume] 0 := by
  let naturalCasts : Set ℝ := Set.range fun n : ℕ => (n : ℝ)
  have hnaturalCasts : naturalCasts.Countable :=
    Set.countable_range fun n : ℕ => (n : ℝ)
  have hpreimage : (Real.exp ⁻¹' naturalCasts).Countable :=
    hnaturalCasts.preimage Real.exp_injective
  filter_upwards [hpreimage.ae_notMem volume] with y hy
  rw [jumpVonMangoldt]
  split_ifs with hex
  · exfalso
    apply hy
    rcases hex with ⟨n, hn⟩
    exact ⟨n, hn.symm⟩
  · rfl

/-- The actual finite-height selected-cluster remainder after deleting the
midpoint jump correction. -/
noncomputable def finiteZeroClusterPsiExplicitFormulaRemainderWithoutJump
    (S : Finset ℂ) (y T : ℝ) : ℂ :=
  finiteZeroClusterComplementContribution S (Real.exp y) T +
    (explicitFormulaApproxWithMultiplicity (Real.exp y) T -
      (chebyshevPsi0 (Real.exp y) : ℂ)) +
    ZeroForcedOscillation.zeroPackageClosedTerms y

/-- The no-jump remainder with the same real-exponent normalization as the
selected zero cluster. -/
noncomputable def normalizedFiniteZeroClusterPsiRemainderWithoutJump
    (S : Finset ℂ) (T beta y : ℝ) : ℂ :=
  (Real.exp (-beta * y) : ℂ) *
    finiteZeroClusterPsiExplicitFormulaRemainderWithoutJump S y T

/-- Local second moment of the normalized no-jump remainder. -/
noncomputable def
    normalizedFiniteZeroClusterPsiRemainderWithoutJumpSecondMoment
    (S : Finset ℂ) (T beta a L : ℝ) : ℝ :=
  ∫ y in a..(a + L),
    ‖normalizedFiniteZeroClusterPsiRemainderWithoutJump
      S T beta y‖ ^ 2

/-- The actual standard-`psi` remainder and the no-jump remainder agree
almost everywhere in the logarithmic variable. -/
theorem finiteZeroClusterPsiExplicitFormulaRemainder_ae_eq_withoutJump
    (S : Finset ℂ) (T : ℝ) :
    (fun y =>
      finiteZeroClusterPsiExplicitFormulaRemainder S y T) =ᵐ[volume]
    (fun y =>
      finiteZeroClusterPsiExplicitFormulaRemainderWithoutJump S y T) := by
  filter_upwards [jumpVonMangoldt_exp_ae_eq_zero] with y hy
  simp [finiteZeroClusterPsiExplicitFormulaRemainder,
    finiteZeroClusterPsiExplicitFormulaRemainderWithoutJump, hy]

/-- Normalization preserves the almost-everywhere deletion of the jump
correction. -/
theorem normalizedFiniteZeroClusterPsiRemainder_ae_eq_withoutJump
    (S : Finset ℂ) (T beta : ℝ) :
    (fun y =>
      normalizedFiniteZeroClusterPsiRemainder S T beta y) =ᵐ[volume]
    (fun y =>
      normalizedFiniteZeroClusterPsiRemainderWithoutJump S T beta y) := by
  filter_upwards [
    finiteZeroClusterPsiExplicitFormulaRemainder_ae_eq_withoutJump S T
  ] with y hy
  simp [normalizedFiniteZeroClusterPsiRemainder,
    normalizedFiniteZeroClusterPsiRemainderWithoutJump, hy]

/-- Removing the midpoint jump does not change the local second moment of the
actual selected-cluster remainder. -/
theorem normalizedFiniteZeroClusterPsiRemainderSecondMoment_eq_withoutJump
    (S : Finset ℂ) (T beta a L : ℝ) :
    normalizedFiniteZeroClusterPsiRemainderSecondMoment S T beta a L =
      normalizedFiniteZeroClusterPsiRemainderWithoutJumpSecondMoment
        S T beta a L := by
  unfold normalizedFiniteZeroClusterPsiRemainderSecondMoment
  unfold normalizedFiniteZeroClusterPsiRemainderWithoutJumpSecondMoment
  apply intervalIntegral.integral_congr_ae
  filter_upwards [
    normalizedFiniteZeroClusterPsiRemainder_ae_eq_withoutJump S T beta
  ] with y hy
  intro _
  rw [hy]

/-- Almost-everywhere actual-standard-`psi` decomposition using the selected
finite zero cluster and the no-jump remainder. -/
theorem
    normalizedChebyshevPsiErrorAtExponent_ae_eq_neg_cluster_sub_withoutJump
    {S : Finset ℂ} {T beta : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T) :
    (fun y =>
      normalizedChebyshevPsiErrorAtExponent beta y) =ᵐ[volume]
    (fun y =>
      -normalizedFiniteZeroClusterContribution S
          (analyticOrderNatAt riemannZeta) beta y -
        normalizedFiniteZeroClusterPsiRemainderWithoutJump S T beta y) := by
  filter_upwards [
    normalizedFiniteZeroClusterPsiRemainder_ae_eq_withoutJump S T beta
  ] with y hy
  rw [normalizedChebyshevPsiErrorAtExponent_eq_neg_cluster_sub_remainder hS,
    hy]

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
