import PrimeNumberTheorem.ExceptionalZeroTargetDyadicGramSchur

open Complex Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Logarithmic occupancy for target dyadic zero packets

Every dynamic complementary packet is contained in one absolute-ordinate
unit bucket.  Counting each actual zeta zero once is therefore bounded by
the bucket's analytic-multiplicity count.  The local Riemann--von Mangoldt
bound then gives a logarithmic bound for the largest packet in a dyadic
block, which can be substituted into the target-normalized Gram--Schur
alternative.
-/

/-- A dynamic complementary packet contains no more distinct zeros than the
total analytic multiplicity of its ambient unit ordinate bucket. -/
theorem dynamicComplementZeroPacket_card_le_unitBucketMultiplicity
    (S : Finset ℂ) (T : ℝ) (n : ℕ) :
    ((dynamicComplementZeroPacket S T n).card : ℝ) ≤
      zeroOrdinateUnitBucketMultiplicity n := by
  classical
  have hsubset : dynamicComplementZeroPacket S T n ⊆
      zeroOrdinateUnitBucket n := by
    exact Finset.inter_subset_left
  have hmult_one : ∀ rho ∈ dynamicComplementZeroPacket S T n,
      (1 : ℝ) ≤ (analyticOrderNatAt riemannZeta rho : ℝ) := by
    intro rho hrho
    have hrhoBucket : rho ∈ zeroOrdinateUnitBucket n := hsubset hrho
    have hrhoTruncated := (Finset.mem_filter.mp hrhoBucket).1
    have hrhoZero := (mem_nontrivialZerosFinset.mp hrhoTruncated).1
    have hrhoOne : rho ≠ 1 := by
      intro hrhoEq
      have hre := congrArg Complex.re hrhoEq
      simp at hre
      linarith [hrhoZero.2.2]
    have hpos : 0 < analyticOrderNatAt riemannZeta rho :=
      ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        hrhoOne hrhoZero.1
    exact_mod_cast hpos
  calc
    ((dynamicComplementZeroPacket S T n).card : ℝ) ≤
        ∑ rho ∈ dynamicComplementZeroPacket S T n,
          (analyticOrderNatAt riemannZeta rho : ℝ) := by
      simpa using
        (dynamicComplementZeroPacket S T n).card_nsmul_le_sum
          (fun rho => (analyticOrderNatAt riemannZeta rho : ℝ)) 1 hmult_one
    _ ≤ ∑ rho ∈ zeroOrdinateUnitBucket n,
          (analyticOrderNatAt riemannZeta rho : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun rho _ _ => Nat.cast_nonneg (analyticOrderNatAt riemannZeta rho))
    _ = zeroOrdinateUnitBucketMultiplicity n := rfl

/-- The largest surviving packet in the absolute-ordinate dyadic block
`[2^k, 2^(k+1))` has logarithmic cardinality, uniformly in the removed set
and in the height truncation. -/
theorem exists_dynamicComplementDyadicOccupancy_le_log :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Finset ℂ) (T : ℝ) (k : ℕ), 4 ≤ 2 ^ k →
        (dynamicComplementDyadicOccupancy S T k : ℝ) ≤
          C * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)) := by
  rcases exists_zeroOrdinateUnitBucketMultiplicity_le_log with
    ⟨C, hC, hbucket⟩
  refine ⟨C, hC, ?_⟩
  intro S T k hk
  have hindexNonempty : (dyadicUnitBucketIndexSet k).Nonempty := by
    refine ⟨2 ^ k, ?_⟩
    rw [dyadicUnitBucketIndexSet, Finset.mem_Icc]
    refine ⟨le_rfl, ?_⟩
    have hpowPos : 0 < 2 ^ k := by positivity
    rw [pow_succ]
    omega
  rcases Finset.exists_mem_eq_sup
      (dyadicUnitBucketIndexSet k) hindexNonempty
      (fun n => (dynamicComplementZeroPacket S T n).card) with
    ⟨n, hn, hsup⟩
  have hnBounds := Finset.mem_Icc.mp hn
  have hnFour : 4 ≤ n := hk.trans hnBounds.1
  have hnUpperNat : n ≤ 2 ^ (k + 1) := by
    omega
  have hnUpperReal : (n : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    exact_mod_cast hnUpperNat
  have hlog :
      Real.log ((n : ℝ) + 7) ≤
        Real.log ((2 : ℝ) ^ (k + 1) + 7) := by
    exact Real.log_le_log (by positivity) (by linarith)
  calc
    (dynamicComplementDyadicOccupancy S T k : ℝ) =
        ((dynamicComplementZeroPacket S T n).card : ℝ) := by
      exact_mod_cast hsup
    _ ≤ zeroOrdinateUnitBucketMultiplicity n :=
      dynamicComplementZeroPacket_card_le_unitBucketMultiplicity S T n
    _ ≤ C * (1 + Real.log ((n : ℝ) + 7)) := hbucket n hnFour
    _ ≤ C * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC

/-- Either the dyadic block contains a genuinely farther-right surviving
zero, or its target-normalized frozen Gaussian second moment is bounded by
the square reciprocal capacity with only a logarithmic occupancy loss. -/
theorem exists_rightHigherDyadic_fartherRight_or_gram_le_logOccupancy :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Finset ℂ) {Told sigma T beta a : ℝ} (k : ℕ),
        4 ≤ 2 ^ k → 0 ≤ Told → 0 ≤ a →
        ∀ {m : ℝ}, 1 ≤ m →
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
                (1 + C *
                  (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7))) *
                dynamicComplementDyadicSquareReciprocalCapacity
                  (rightHigherExclusionSet S Told sigma T) T k := by
  rcases exists_dynamicComplementDyadicOccupancy_le_log with
    ⟨C, hC, hocc⟩
  refine ⟨C, hC, ?_⟩
  intro S Told sigma T beta a k hk hTold ha m hm
  rcases rightHigherDyadic_fartherRight_or_gram_le_unweighted
      (S := S) (Told := Told) (sigma := sigma) (T := T)
      (beta := beta) (a := a) (k := k) (m := m)
      hTold ha hm with hfar | hgram
  · exact Or.inl hfar
  · right
    have hoccBound :=
      hocc (rightHigherExclusionSet S Told sigma T) T k hk
    have hfactor :
        MathlibAux.gaussianBucketSchurConstant *
            (1 + (dynamicComplementDyadicOccupancy
              (rightHigherExclusionSet S Told sigma T) T k : ℝ)) ≤
          MathlibAux.gaussianBucketSchurConstant *
            (1 + C *
              (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7))) := by
      apply mul_le_mul_of_nonneg_left
      · linarith
      · exact MathlibAux.gaussianBucketSchurConstant_pos.le
    have hcapacity :
        0 ≤ dynamicComplementDyadicSquareReciprocalCapacity
          (rightHigherExclusionSet S Told sigma T) T k := by
      unfold dynamicComplementDyadicSquareReciprocalCapacity
      positivity
    exact hgram.trans (mul_le_mul_of_nonneg_right hfactor hcapacity)

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
