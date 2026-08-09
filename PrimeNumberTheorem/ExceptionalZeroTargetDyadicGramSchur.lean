import PrimeNumberTheorem.ExceptionalZeroDyadicSquareMultiplicity
import PrimeNumberTheorem.ExceptionalZeroEnergyCapacityBridge
import PrimeNumberTheorem.VKEdgeDynamicZeroPacket

open Complex Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Target-normalized dyadic Gram--Schur control

This module specializes the existing whole-Gram dynamic-packet Schur bound
to one dyadic ordinate block.  Finite Cauchy--Schwarz inside each unit bucket
costs only the largest local packet cardinality.  The resulting square sum is
identified exactly with the multiplicity-squared, reciprocal-square,
target-normalized zeta-zero capacity.

The weighted estimate is unconditional.  A separate dichotomy either returns
a surviving zero strictly to the right of the target `beta`, or permits the
exponential target weights to be removed when the logarithmic center is
nonnegative.
-/

/-- Natural unit-bucket indices in the half-open dyadic ordinate block
`[2^k, 2^(k+1))`. -/
def dyadicUnitBucketIndexSet (k : ℕ) : Finset ℕ :=
  Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1)

/-- Largest number of surviving actual zeta zeros in one unit bucket of the
`k`-th dyadic block.  It is zero when every packet is empty. -/
noncomputable def dynamicComplementDyadicOccupancy
    (S : Finset ℂ) (T : ℝ) (k : ℕ) : ℕ :=
  (dyadicUnitBucketIndexSet k).sup fun n =>
    (dynamicComplementZeroPacket S T n).card

theorem dynamicComplementZeroPacket_card_le_dyadicOccupancy
    (S : Finset ℂ) (T : ℝ) (k : ℕ) {n : ℕ}
    (hn : n ∈ dyadicUnitBucketIndexSet k) :
    (dynamicComplementZeroPacket S T n).card ≤
      dynamicComplementDyadicOccupancy S T k := by
  exact Finset.le_sup
    (s := dyadicUnitBucketIndexSet k)
    (f := fun j => (dynamicComplementZeroPacket S T j).card) hn

/-- Exact square norm of a target-normalized frozen zeta-zero coefficient. -/
theorem finiteZeroClusterCoefficientAt_norm_sq_eq
    (beta a : ℝ) (rho : ℂ) :
    ‖finiteZeroClusterCoefficientAt
        (analyticOrderNatAt riemannZeta) beta a rho‖ ^ 2 =
      (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2 *
        Real.exp (2 * (rho.re - beta) * a) := by
  rw [show Real.exp (2 * (rho.re - beta) * a) =
      Real.exp ((rho.re - beta) * a) ^ 2 by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]
  simp only [finiteZeroClusterCoefficientAt, norm_mul, norm_inv,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), div_eq_mul_inv]
  ring

/-- Target-weighted square reciprocal capacity of the surviving actual zeta
zeros in one dyadic block.  The packet form matches the whole-Gram theorem
without changing the zero set or target normalization. -/
noncomputable def dynamicComplementDyadicTargetSquareCapacity
    (S : Finset ℂ) (T beta a : ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ dyadicUnitBucketIndexSet k,
    ∑ rho ∈ dynamicComplementZeroPacket S T n,
      (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2 *
        Real.exp (2 * (rho.re - beta) * a)

/-- The corresponding unweighted square reciprocal capacity. -/
noncomputable def dynamicComplementDyadicSquareReciprocalCapacity
    (S : Finset ℂ) (T : ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ dyadicUnitBucketIndexSet k,
    ∑ rho ∈ dynamicComplementZeroPacket S T n,
      (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2

theorem dynamicComplementDyadicTargetSquareCapacity_nonneg
    (S : Finset ℂ) (T beta a : ℝ) (k : ℕ) :
    0 ≤ dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
  unfold dynamicComplementDyadicTargetSquareCapacity
  positivity

private theorem packetCoefficientMass_sq_le_occupancy_mul_sum_sq
    (S : Finset ℂ) (T beta a : ℝ) (k : ℕ) {n : ℕ}
    (hn : n ∈ dyadicUnitBucketIndexSet k) :
    dynamicComplementPacketCoefficientMass S T beta a n ^ 2 ≤
      (dynamicComplementDyadicOccupancy S T k : ℝ) *
        ∑ rho ∈ dynamicComplementZeroPacket S T n,
          ‖finiteZeroClusterCoefficientAt
              (analyticOrderNatAt riemannZeta) beta a rho‖ ^ 2 := by
  unfold dynamicComplementPacketCoefficientMass
  calc
    (∑ rho ∈ dynamicComplementZeroPacket S T n,
        ‖finiteZeroClusterCoefficientAt
            (analyticOrderNatAt riemannZeta) beta a rho‖) ^ 2 ≤
        ((dynamicComplementZeroPacket S T n).card : ℝ) *
          ∑ rho ∈ dynamicComplementZeroPacket S T n,
            ‖finiteZeroClusterCoefficientAt
                (analyticOrderNatAt riemannZeta) beta a rho‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ (dynamicComplementDyadicOccupancy S T k : ℝ) *
          ∑ rho ∈ dynamicComplementZeroPacket S T n,
            ‖finiteZeroClusterCoefficientAt
                (analyticOrderNatAt riemannZeta) beta a rho‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast
          dynamicComplementZeroPacket_card_le_dyadicOccupancy S T k hn
      · positivity

/-- Whole-Gram Schur control for one target-normalized dyadic block.  The
near-frequency loss is the actual largest unit-bucket occupancy, while the
right side retains the exact target exponential weight of every zero. -/
theorem dynamicComplementDyadicGaussianMajorantEnergy_le_targetSquareCapacity
    (S : Finset ℂ) (T beta a : ℝ) (k : ℕ)
    {m : ℝ} (hm : 1 ≤ m) :
    dynamicComplementGaussianMajorantEnergy S T beta a
        (dyadicUnitBucketIndexSet k) m ≤
      MathlibAux.gaussianBucketSchurConstant *
        (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
          dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
  have hschur :=
    dynamicComplementGaussianMajorantEnergy_le S T beta a
      (dyadicUnitBucketIndexSet k) hm
  have hpackets :
      (∑ n ∈ dyadicUnitBucketIndexSet k,
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2) ≤
        (dynamicComplementDyadicOccupancy S T k : ℝ) *
          dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
    calc
      (∑ n ∈ dyadicUnitBucketIndexSet k,
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2) ≤
          ∑ n ∈ dyadicUnitBucketIndexSet k,
            (dynamicComplementDyadicOccupancy S T k : ℝ) *
              ∑ rho ∈ dynamicComplementZeroPacket S T n,
                ‖finiteZeroClusterCoefficientAt
                    (analyticOrderNatAt riemannZeta) beta a rho‖ ^ 2 := by
        exact Finset.sum_le_sum fun n hn =>
          packetCoefficientMass_sq_le_occupancy_mul_sum_sq
            S T beta a k hn
      _ = (dynamicComplementDyadicOccupancy S T k : ℝ) *
            dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
        rw [← Finset.mul_sum]
        unfold dynamicComplementDyadicTargetSquareCapacity
        apply congrArg
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro rho hrho
        exact finiteZeroClusterCoefficientAt_norm_sq_eq beta a rho
  have hcapacityNonneg :
      0 ≤ dynamicComplementDyadicTargetSquareCapacity S T beta a k :=
    dynamicComplementDyadicTargetSquareCapacity_nonneg S T beta a k
  calc
    dynamicComplementGaussianMajorantEnergy S T beta a
        (dyadicUnitBucketIndexSet k) m ≤
        MathlibAux.gaussianBucketSchurConstant *
          ∑ n ∈ dyadicUnitBucketIndexSet k,
            dynamicComplementPacketCoefficientMass S T beta a n ^ 2 :=
      hschur
    _ ≤ MathlibAux.gaussianBucketSchurConstant *
          ((dynamicComplementDyadicOccupancy S T k : ℝ) *
            dynamicComplementDyadicTargetSquareCapacity S T beta a k) := by
      exact mul_le_mul_of_nonneg_left hpackets
        MathlibAux.gaussianBucketSchurConstant_pos.le
    _ ≤ MathlibAux.gaussianBucketSchurConstant *
          (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
            dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
      have hocc :
          (dynamicComplementDyadicOccupancy S T k : ℝ) ≤
            1 + (dynamicComplementDyadicOccupancy S T k : ℝ) := by linarith
      nlinarith [MathlibAux.gaussianBucketSchurConstant_pos]

/-- Actual centered frozen Gaussian `L²` energy of one target-normalized
dyadic block.  This is the energy object controlled by the whole-Gram
majorant, not merely a packet-mass algebraic surrogate. -/
theorem dynamicComplementDyadicCenteredFrozenGaussianSecondMoment_le_targetSquareCapacity
    (S : Finset ℂ) (T beta a : ℝ) (k : ℕ)
    {m : ℝ} (hm : 1 ≤ m) :
    dynamicComplementCenteredFrozenGaussianSecondMoment S T beta a
        (dyadicUnitBucketIndexSet k) m ≤
      MathlibAux.gaussianBucketSchurConstant *
        (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
          dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
  exact (dynamicComplementCenteredFrozenGaussianSecondMoment_le_majorant
    S T beta a (dyadicUnitBucketIndexSet k) (lt_of_lt_of_le zero_lt_one hm)).trans
      (dynamicComplementDyadicGaussianMajorantEnergy_le_targetSquareCapacity
        S T beta a k hm)

/-- The actual right-higher, finite-`S` specialization of the one-block
target-normalized Gram--Schur bound.  No constant depends on `S.card`. -/
theorem rightHigherDyadicGaussianMajorantEnergy_le_targetSquareCapacity
    (S : Finset ℂ) (Told sigma T beta a : ℝ) (k : ℕ)
    {m : ℝ} (hm : 1 ≤ m) :
    dynamicComplementGaussianMajorantEnergy
        (rightHigherExclusionSet S Told sigma T) T beta a
        (dyadicUnitBucketIndexSet k) m ≤
      MathlibAux.gaussianBucketSchurConstant *
        (1 + (dynamicComplementDyadicOccupancy
          (rightHigherExclusionSet S Told sigma T) T k : ℝ)) *
        dynamicComplementDyadicTargetSquareCapacity
          (rightHigherExclusionSet S Told sigma T) T beta a k := by
  exact dynamicComplementDyadicGaussianMajorantEnergy_le_targetSquareCapacity
    (rightHigherExclusionSet S Told sigma T) T beta a k hm

/-- Actual-zeta, target-normalized, right-higher, `S`-relative centered
frozen Gaussian `L²` upper bound for one dyadic block. -/
theorem rightHigherDyadicCenteredFrozenGaussianSecondMoment_le_targetSquareCapacity
    (S : Finset ℂ) (Told sigma T beta a : ℝ) (k : ℕ)
    {m : ℝ} (hm : 1 ≤ m) :
    dynamicComplementCenteredFrozenGaussianSecondMoment
        (rightHigherExclusionSet S Told sigma T) T beta a
        (dyadicUnitBucketIndexSet k) m ≤
      MathlibAux.gaussianBucketSchurConstant *
        (1 + (dynamicComplementDyadicOccupancy
          (rightHigherExclusionSet S Told sigma T) T k : ℝ)) *
        dynamicComplementDyadicTargetSquareCapacity
          (rightHigherExclusionSet S Told sigma T) T beta a k := by
  exact
    dynamicComplementDyadicCenteredFrozenGaussianSecondMoment_le_targetSquareCapacity
      (rightHigherExclusionSet S Told sigma T) T beta a k hm

/-- In one right-higher dyadic block, either a surviving zero lies strictly
to the right of `beta`, or every surviving zero has real part at most
`beta`.  The farther-right branch also returns the directed Carlson-strip
witness data. -/
theorem rightHigherDyadic_fartherRight_or_all_re_le
    (S : Finset ℂ) {Told sigma T beta : ℝ} (k : ℕ)
    (hTold : 0 ≤ Told) :
    (∃ n ∈ dyadicUnitBucketIndexSet k, ∃ rho,
      rho ∈ dynamicComplementZeroPacket
          (rightHigherExclusionSet S Told sigma T) T n ∧
        beta < rho.re ∧
        rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
        Told < rho.im ∧ rho ∉ S) ∨
      ∀ n ∈ dyadicUnitBucketIndexSet k, ∀ rho,
        rho ∈ dynamicComplementZeroPacket
            (rightHigherExclusionSet S Told sigma T) T n →
          rho.re ≤ beta := by
  classical
  by_cases hfar : ∃ n ∈ dyadicUnitBucketIndexSet k, ∃ rho,
      rho ∈ dynamicComplementZeroPacket
          (rightHigherExclusionSet S Told sigma T) T n ∧ beta < rho.re
  · left
    rcases hfar with ⟨n, hn, rho, hrhoPacket, hrhoFar⟩
    have hrhoInter := Finset.mem_inter.mp hrhoPacket
    have hrhoDiff := Finset.mem_sdiff.mp hrhoInter.2
    rcases directedWitness_of_not_mem_rightHigherExclusionSet
        hTold hrhoDiff.1 hrhoDiff.2 with ⟨hrhoStrip, hrhoHigh, hrhoS⟩
    exact ⟨n, hn, rho, hrhoPacket, hrhoFar,
      hrhoStrip, hrhoHigh, hrhoS⟩
  · right
    push Not at hfar
    exact fun n hn rho hrho => hfar n hn rho hrho

/-- If no surviving zero in the block is farther right than `beta`, then at
a nonnegative center every target exponential weight is at most one. -/
theorem rightHigherDyadicTargetSquareCapacity_le_unweighted_of_re_le
    (S : Finset ℂ) (Told sigma T beta : ℝ) {a : ℝ} (k : ℕ)
    (ha : 0 ≤ a)
    (hre : ∀ n ∈ dyadicUnitBucketIndexSet k, ∀ rho,
      rho ∈ dynamicComplementZeroPacket
          (rightHigherExclusionSet S Told sigma T) T n →
        rho.re ≤ beta) :
    dynamicComplementDyadicTargetSquareCapacity
        (rightHigherExclusionSet S Told sigma T) T beta a k ≤
      dynamicComplementDyadicSquareReciprocalCapacity
        (rightHigherExclusionSet S Told sigma T) T k := by
  unfold dynamicComplementDyadicTargetSquareCapacity
    dynamicComplementDyadicSquareReciprocalCapacity
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro rho hrho
  have hexp : Real.exp (2 * (rho.re - beta) * a) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [hre n hn rho hrho]
  exact mul_le_of_le_one_right (by positivity) hexp

/-- Requested explicit E2 alternative: either output a genuinely farther
right zero, or bound the whole dyadic Gram energy by the unweighted
reciprocal-square capacity. -/
theorem rightHigherDyadic_fartherRight_or_gram_le_unweighted
    (S : Finset ℂ) {Told sigma T beta a : ℝ} (k : ℕ)
    (hTold : 0 ≤ Told) (ha : 0 ≤ a) {m : ℝ} (hm : 1 ≤ m) :
    (∃ n ∈ dyadicUnitBucketIndexSet k, ∃ rho,
      rho ∈ dynamicComplementZeroPacket
          (rightHigherExclusionSet S Told sigma T) T n ∧
        beta < rho.re ∧
        rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
        Told < rho.im ∧ rho ∉ S) ∨
      dynamicComplementCenteredFrozenGaussianSecondMoment
          (rightHigherExclusionSet S Told sigma T) T beta a
          (dyadicUnitBucketIndexSet k) m ≤
        MathlibAux.gaussianBucketSchurConstant *
          (1 + (dynamicComplementDyadicOccupancy
            (rightHigherExclusionSet S Told sigma T) T k : ℝ)) *
          dynamicComplementDyadicSquareReciprocalCapacity
            (rightHigherExclusionSet S Told sigma T) T k := by
  rcases rightHigherDyadic_fartherRight_or_all_re_le S k hTold with
    hfar | hre
  · exact Or.inl hfar
  · right
    exact (rightHigherDyadicCenteredFrozenGaussianSecondMoment_le_targetSquareCapacity
      S Told sigma T beta a k hm).trans
        (mul_le_mul_of_nonneg_left
          (rightHigherDyadicTargetSquareCapacity_le_unweighted_of_re_le
            S Told sigma T beta k ha hre)
          (mul_nonneg MathlibAux.gaussianBucketSchurConstant_pos.le
            (by positivity)))

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
