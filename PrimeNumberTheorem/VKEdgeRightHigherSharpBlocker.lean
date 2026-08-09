import PrimeNumberTheorem.ExceptionalZeroDirectedGrowth
import PrimeNumberTheorem.RiemannVonMangoldt.CriticalLinePartition
import PrimeNumberTheorem.VKEdgeResidualAmplification

open Complex
open scoped ComplexConjugate

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# The right-higher Sharp transfer blocker

The current Sharp lower bound is anchored at one fixed positive-ordinate
zero.  Once the old-height cutoff reaches that ordinate, the directed-growth
exclusion set contains both the anchor and its conjugate.  Consequently the
anchor pair is absent from the complementary packet whose positive energy is
needed for the next directed-growth step.

This module proves that absorption exactly.  It also records the zero-energy
endpoint when no higher right-strip zero remains.  It does not postulate or
prove the missing repeated positive-energy estimate.
-/

/-- Every truncated zero below the old-height cutoff belongs to the directed
exclusion set. -/
theorem mem_rightHigherExclusionSet_of_im_le
    {S : Finset ℂ} {Told sigma T : ℝ} {rho : ℂ}
    (hrhoT : rho ∈ nontrivialZerosFinset T)
    (him : rho.im ≤ Told) :
    rho ∈ rightHigherExclusionSet S Told sigma T := by
  simp [rightHigherExclusionSet, hrhoT, him]

/-- Once `Told` reaches the anchor ordinate, both the anchor and its
conjugate are absorbed by the directed exclusion set. -/
theorem targetPair_mem_rightHigherExclusionSet
    {S : Finset ℂ} {Told sigma T : ℝ} {rho : ℂ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (hgamma : 0 < rho.im)
    (hheight : |rho.im| ≤ T)
    (hTold : rho.im ≤ Told) :
    rho ∈ rightHigherExclusionSet S Told sigma T ∧
      conj rho ∈ rightHigherExclusionSet S Told sigma T := by
  have hrhoT : rho ∈ nontrivialZerosFinset T :=
    mem_nontrivialZerosFinset.mpr ⟨hrho, hheight⟩
  have hconjZero :
      RiemannHypothesis.IsNontrivialZero (conj rho) :=
    RiemannVonMangoldt.isNontrivialZero_conj hrho
  have hconjHeight : |(conj rho).im| ≤ T := by
    simpa using hheight
  have hconjT : conj rho ∈ nontrivialZerosFinset T :=
    mem_nontrivialZerosFinset.mpr ⟨hconjZero, hconjHeight⟩
  constructor
  · exact mem_rightHigherExclusionSet_of_im_le hrhoT hTold
  · apply mem_rightHigherExclusionSet_of_im_le hconjT
    simp
    linarith

/-- The absorbed anchor pair is absent from the dynamic complement used by
the directed-growth energy. -/
theorem targetPair_not_mem_dynamicComplementZeroSet
    {S : Finset ℂ} {Told sigma T : ℝ} {rho : ℂ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (hgamma : 0 < rho.im)
    (hheight : |rho.im| ≤ T)
    (hTold : rho.im ≤ Told) :
    rho ∉
        dynamicComplementZeroSet
          (rightHigherExclusionSet S Told sigma T) T ∧
      conj rho ∉
        dynamicComplementZeroSet
          (rightHigherExclusionSet S Told sigma T) T := by
  have hpair :=
    targetPair_mem_rightHigherExclusionSet
      (S := S) (sigma := sigma) hrho hgamma hheight hTold
  constructor
  · intro hmem
    exact (Finset.mem_sdiff.mp hmem).2 hpair.1
  · intro hmem
    exact (Finset.mem_sdiff.mp hmem).2 hpair.2

/-- The current swept Sharp `L²` coefficient is less than half of the
leading ordinary-energy coefficient of the anchor conjugate pair.  Thus the
verified lower bound can be carried by that pair alone at the coefficient
level. -/
theorem
    two_mul_currentSharpL2Constant_lt_targetPairLeadingEnergy
    {epsilon : ℝ} {rho : ℂ} {k : ℕ}
    (hepsilon : 0 < epsilon)
    (hrho1 : rho ≠ 1)
    (hzero : riemannZeta rho = 0) :
    2 * centeredSharpenedSweptOrdinaryL2Constant epsilon rho k <
      2 * epsilon *
        (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 := by
  have hhalf :=
    centeredSharpenedSweptOrdinaryL2Constant_lt_cosineModelHalfEnergy
      (k := k) hepsilon hrho1 hzero
  linarith

/-- If every truncated zero is already recorded, below `Told`, or outside
the strict right strip, then the directed full complementary energy is
exactly zero. -/
theorem
    rightHigherFullMovingGaussianSecondMoment_eq_zero_of_no_new_right_zero
    {S : Finset ℂ} {Told sigma T beta a m L : ℝ}
    (hexcluded :
      ∀ rho ∈ nontrivialZerosFinset T,
        rho ∈ S ∨ rho.im ≤ Told ∨ rho.re ≤ sigma) :
    dynamicComplementForwardMovingGaussianSecondMoment
        (rightHigherExclusionSet S Told sigma T) T beta a
        (dynamicComplementFullBucketSet
          (rightHigherExclusionSet S Told sigma T) T) m L = 0 := by
  apply dynamicComplementFullMovingGaussianSecondMoment_eq_zero_of_subset
  intro rho hrho
  rcases hexcluded rho hrho with hrhoS | hrhoBad
  · simp [rightHigherExclusionSet, hrhoS]
  · simp [rightHigherExclusionSet, hrho, hrhoBad]

/-- Combined obstruction: the old anchor pair has been absorbed, and in the
absence of any genuinely new higher right-strip zero the directed energy is
zero. -/
theorem
    targetPair_absorbed_and_fullMovingEnergy_zero_of_no_new_right_zero
    {S : Finset ℂ} {Told sigma T beta a m L : ℝ} {rho : ℂ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (hgamma : 0 < rho.im)
    (hheight : |rho.im| ≤ T)
    (hTold : rho.im ≤ Told)
    (hexcluded :
      ∀ z ∈ nontrivialZerosFinset T,
        z ∈ S ∨ z.im ≤ Told ∨ z.re ≤ sigma) :
    (rho ∈ rightHigherExclusionSet S Told sigma T ∧
        conj rho ∈ rightHigherExclusionSet S Told sigma T) ∧
      dynamicComplementForwardMovingGaussianSecondMoment
        (rightHigherExclusionSet S Told sigma T) T beta a
        (dynamicComplementFullBucketSet
          (rightHigherExclusionSet S Told sigma T) T) m L = 0 := by
  exact
    ⟨targetPair_mem_rightHigherExclusionSet
        (S := S) (sigma := sigma) hrho hgamma hheight hTold,
      rightHigherFullMovingGaussianSecondMoment_eq_zero_of_no_new_right_zero
        hexcluded⟩

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
