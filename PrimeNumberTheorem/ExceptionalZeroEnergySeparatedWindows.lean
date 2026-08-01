import MathlibAux.SeparatedForwardWindows
import PrimeNumberTheorem.ExceptionalZeroEnergyCapacityBridge

open Complex MeasureTheory Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Separated right-higher energy windows

This module combines forward half-open windows with the pointwise E0
energy-capacity bridge.  The Gaussian factor genuinely depends on the window
center through `normalizedGaussian m (y - a)`.  Pairwise separation supplies
the actual overlap bound one, so no external overlap hypothesis is retained.

The final algebraic identities choose a strictly interior height exponent
whose squared-capacity exponent is `-(beta - sigma)`.  They are only a local
safe-margin calculation.  In particular, they do not establish the proposed
two-thirds threshold, a zero-density input, or a contradiction.
-/

private def rightHigherSeparatedEnergyIntegrand
    (S : Finset ℂ) (Told sigma T beta m : ℝ) (a y : ℝ) : ℝ :=
  normalizedGaussian m (y - a) *
    ‖normalizedFiniteZeroClusterComplementContribution
        (rightHigherExclusionSet S Told sigma T) T beta y‖ ^ 2

private def rightHigherSeparatedCapacityIntegrand
    (S : Finset ℂ) (Told sigma T beta m : ℝ) (a y : ℝ) : ℝ :=
  normalizedGaussian m (y - a) *
    rightHigherTargetNormalizedAbsoluteMass S Told sigma T beta y ^ 2

/-- Accumulated actual right-higher energy over separated forward windows.
The local Gaussian is centered relative to each individual `a`. -/
noncomputable def rightHigherSeparatedWindowEnergy
    (centers : Finset ℝ) (S : Finset ℂ)
    (L Told sigma T beta m : ℝ) : ℝ :=
  MathlibAux.accumulatedForwardWindowIntegral centers L
    (rightHigherSeparatedEnergyIntegrand S Told sigma T beta m)

/-- Global capacity kernel obtained by extending each center-dependent local
capacity by zero outside that center's half-open window. -/
def rightHigherSeparatedCapacityKernel
    (centers : Finset ℝ) (S : Finset ℂ)
    (L Told sigma T beta m : ℝ) (y : ℝ) : ℝ :=
  MathlibAux.globalForwardWindowKernel centers L
    (rightHigherSeparatedCapacityIntegrand S Told sigma T beta m) y

/-- The accumulated right-higher capacity on the union of forward windows. -/
noncomputable def rightHigherSeparatedAccumulatedCapacity
    (centers : Finset ℝ) (S : Finset ℂ)
    (L Told sigma T beta m : ℝ) : ℝ :=
  ∫ y : ℝ in MathlibAux.forwardWindowUnion centers L,
    rightHigherSeparatedCapacityKernel
      centers S L Told sigma T beta m y

private theorem continuous_normalizedRightHigherComplement
    (S : Finset ℂ) (Told sigma T beta : ℝ) :
    Continuous (fun y : ℝ ↦
      normalizedFiniteZeroClusterComplementContribution
        (rightHigherExclusionSet S Told sigma T) T beta y) := by
  let Z : Finset ℂ :=
    nontrivialZerosFinset T \ rightHigherExclusionSet S Told sigma T
  have heq :
      (fun y : ℝ ↦
        normalizedFiniteZeroClusterComplementContribution
          (rightHigherExclusionSet S Told sigma T) T beta y) =
        fun y : ℝ ↦
          MathlibAux.driftingExponentialPolynomial Z
            (finiteZeroClusterCoefficientAt
              (analyticOrderNatAt riemannZeta) beta 0)
            Complex.im (fun rho ↦ rho.re - beta) 0 y := by
    funext y
    rw [← normalizedFiniteZeroClusterContribution_eq_drifting]
    rfl
  rw [heq]
  unfold MathlibAux.driftingExponentialPolynomial
  fun_prop

private theorem continuous_rightHigherAbsoluteMass
    (S : Finset ℂ) (Told sigma T beta : ℝ) :
    Continuous (fun y : ℝ ↦
      rightHigherTargetNormalizedAbsoluteMass S Told sigma T beta y) := by
  dsimp [rightHigherTargetNormalizedAbsoluteMass]
  fun_prop

private theorem continuous_normalizedGaussian_of_pos
    {m : ℝ} (hm : 0 < m) :
    Continuous (normalizedGaussian m) :=
  continuous_iff_continuousAt.mpr fun t ↦
    (hasDerivAt_normalizedGaussian hm t).continuousAt

private theorem integrableOn_rightHigherSeparatedEnergyIntegrand
    (S : Finset ℂ) (L Told sigma T beta a : ℝ)
    {m : ℝ} (hm : 0 < m) :
    IntegrableOn
      (rightHigherSeparatedEnergyIntegrand S Told sigma T beta m a)
      (MathlibAux.forwardWindow a L) := by
  have hgaussian : Continuous (fun y : ℝ ↦ normalizedGaussian m (y - a)) :=
    (continuous_normalizedGaussian_of_pos hm).comp
      (continuous_id.sub continuous_const)
  have hcomplement :=
    continuous_normalizedRightHigherComplement S Told sigma T beta
  have hcontinuous : Continuous
      (rightHigherSeparatedEnergyIntegrand S Told sigma T beta m a) := by
    dsimp [rightHigherSeparatedEnergyIntegrand]
    exact hgaussian.mul (hcomplement.norm.pow 2)
  exact
    (hcontinuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ico_subset_Icc_self

private theorem integrableOn_rightHigherSeparatedCapacityIntegrand
    (S : Finset ℂ) (L Told sigma T beta a : ℝ)
    {m : ℝ} (hm : 0 < m) :
    IntegrableOn
      (rightHigherSeparatedCapacityIntegrand S Told sigma T beta m a)
      (MathlibAux.forwardWindow a L) := by
  have hgaussian : Continuous (fun y : ℝ ↦ normalizedGaussian m (y - a)) :=
    (continuous_normalizedGaussian_of_pos hm).comp
      (continuous_id.sub continuous_const)
  have hmass := continuous_rightHigherAbsoluteMass S Told sigma T beta
  have hcontinuous : Continuous
      (rightHigherSeparatedCapacityIntegrand S Told sigma T beta m a) := by
    dsimp [rightHigherSeparatedCapacityIntegrand]
    exact hgaussian.mul (hmass.pow 2)
  exact
    (hcontinuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ico_subset_Icc_self

private theorem integrable_rightHigherSeparatedCapacityKernel
    (centers : Finset ℝ) (S : Finset ℂ)
    (L Told sigma T beta : ℝ) {m : ℝ} (hm : 0 < m) :
    Integrable (rightHigherSeparatedCapacityKernel
      centers S L Told sigma T beta m) := by
  classical
  unfold rightHigherSeparatedCapacityKernel
  exact MeasureTheory.integrable_finset_sum centers fun a ha ↦
    (integrableOn_rightHigherSeparatedCapacityIntegrand
      S L Told sigma T beta a hm).integrable_indicator measurableSet_Ico

/-- For separated centers, accumulated actual right-higher energy is bounded
by the accumulated E0 absolute-mass capacity with the proven overlap constant
one.  No multiplicity or packet-overlap assumption is an input. -/
theorem rightHigherSeparatedWindowEnergy_le_accumulatedCapacity
    (centers : Finset ℝ) (S : Finset ℂ)
    (L Told sigma T beta m : ℝ)
    (hsep : MathlibAux.finiteCentersPairwiseSeparated centers L)
    (hm : 0 < m) :
    rightHigherSeparatedWindowEnergy centers S L Told sigma T beta m ≤
      rightHigherSeparatedAccumulatedCapacity
        centers S L Told sigma T beta m := by
  let energy : ℝ → ℝ → ℝ :=
    rightHigherSeparatedEnergyIntegrand S Told sigma T beta m
  let capacity : ℝ → ℝ → ℝ :=
    rightHigherSeparatedCapacityIntegrand S Told sigma T beta m
  have henergyInt : ∀ a ∈ centers,
      IntegrableOn (energy a) (MathlibAux.forwardWindow a L) := by
    intro a ha
    exact integrableOn_rightHigherSeparatedEnergyIntegrand
      S L Told sigma T beta a hm
  have hkernelInt : Integrable
      (rightHigherSeparatedCapacityKernel
        centers S L Told sigma T beta m) :=
    integrable_rightHigherSeparatedCapacityKernel
      centers S L Told sigma T beta hm
  unfold rightHigherSeparatedWindowEnergy
  change MathlibAux.accumulatedForwardWindowIntegral centers L energy ≤ _
  apply MathlibAux.accumulatedForwardWindowIntegral_le_unionIntegral_of_pairwiseSeparated
    hsep henergyInt hkernelInt.integrableOn
  intro a ha y hy
  have hnorm :
      ‖normalizedFiniteZeroClusterComplementContribution
          (rightHigherExclusionSet S Told sigma T) T beta y‖ ≤
        rightHigherTargetNormalizedAbsoluteMass S Told sigma T beta y :=
    norm_normalizedRightHigherComplement_le_absoluteMass
      S Told sigma T beta y
  have hmassNonneg :
      0 ≤ rightHigherTargetNormalizedAbsoluteMass S Told sigma T beta y :=
    rightHigherTargetNormalizedAbsoluteMass_nonneg
      S Told sigma T beta y
  have hsq :
      ‖normalizedFiniteZeroClusterComplementContribution
          (rightHigherExclusionSet S Told sigma T) T beta y‖ ^ 2 ≤
        rightHigherTargetNormalizedAbsoluteMass S Told sigma T beta y ^ 2 := by
    nlinarith [norm_nonneg
      (normalizedFiniteZeroClusterComplementContribution
        (rightHigherExclusionSet S Told sigma T) T beta y)]
  have hlocal : energy a y ≤ capacity a y := by
    exact mul_le_mul_of_nonneg_left hsq
      (normalizedGaussian_pos hm (y - a)).le
  have hcapacityNonneg : ∀ b ∈ centers,
      0 ≤ (MathlibAux.forwardWindow b L).indicator (capacity b) y := by
    intro b hb
    by_cases hyb : y ∈ MathlibAux.forwardWindow b L
    · rw [Set.indicator_of_mem hyb]
      dsimp [capacity, rightHigherSeparatedCapacityIntegrand]
      exact mul_nonneg (normalizedGaussian_pos hm (y - b)).le
        (sq_nonneg
          (rightHigherTargetNormalizedAbsoluteMass S Told sigma T beta y))
    · rw [Set.indicator_of_notMem hyb]
  have hsingle : capacity a y ≤
      MathlibAux.globalForwardWindowKernel centers L capacity y := by
    unfold MathlibAux.globalForwardWindowKernel
    calc
      capacity a y =
          (MathlibAux.forwardWindow a L).indicator (capacity a) y :=
        (Set.indicator_of_mem hy (capacity a)).symm
      _ ≤ ∑ b ∈ centers,
          (MathlibAux.forwardWindow b L).indicator (capacity b) y :=
        Finset.single_le_sum hcapacityNonneg ha
  exact hlocal.trans hsingle

/-- Local Carlson exponent `q = 4 sigma (1 - sigma)`. -/
def localSafeQ (sigma : ℝ) : ℝ :=
  4 * sigma * (1 - sigma)

/-- Strictly interior height exponent
`alpha = (beta - sigma) / (2 q)`. -/
def localSafeAlpha (sigma beta : ℝ) : ℝ :=
  (beta - sigma) / (2 * localSafeQ sigma)

theorem localSafeQ_pos
    {sigma beta : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaBeta : sigma < beta)
    (hbeta : beta < 1) :
    0 < localSafeQ sigma := by
  unfold localSafeQ
  have hsigmaPos : 0 < sigma := by linarith
  have hsigmaOne : sigma < 1 := hsigmaBeta.trans hbeta
  exact mul_pos (mul_pos (by norm_num) hsigmaPos)
    (sub_pos.mpr hsigmaOne)

theorem localSafeAlpha_pos
    {sigma beta : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaBeta : sigma < beta)
    (hbeta : beta < 1) :
    0 < localSafeAlpha sigma beta := by
  unfold localSafeAlpha
  exact div_pos (sub_pos.mpr hsigmaBeta)
    (mul_pos (by norm_num) (localSafeQ_pos hsigma hsigmaBeta hbeta))

/-- The safe exponent uses exactly half of the available gap. -/
theorem localSafeAlpha_mul_q
    {sigma beta : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaBeta : sigma < beta)
    (hbeta : beta < 1) :
    localSafeAlpha sigma beta * localSafeQ sigma =
      (beta - sigma) / 2 := by
  have hq : localSafeQ sigma ≠ 0 :=
    ne_of_gt (localSafeQ_pos hsigma hsigmaBeta hbeta)
  unfold localSafeAlpha
  field_simp

/-- After squaring the capacity, the net polynomial exponent is the negative
gap `-(beta - sigma)`. -/
theorem localSafeSquaredCapacityExponent_eq
    {sigma beta : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaBeta : sigma < beta)
    (hbeta : beta < 1) :
    2 * (localSafeAlpha sigma beta * localSafeQ sigma + sigma - beta) =
      -(beta - sigma) := by
  rw [localSafeAlpha_mul_q hsigma hsigmaBeta hbeta]
  ring

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
