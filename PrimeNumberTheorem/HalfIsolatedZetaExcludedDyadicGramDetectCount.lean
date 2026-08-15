import PrimeNumberTheorem.HalfIsolatedZetaExcludedDyadicGramCapacityBridge

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

section ExcludedDyadicGramDetectCount

/-- On the actual excluded zeta bucket set, either the Gaussian Gram energy is
controlled by the full positive/negative excluded square mass, or a unit bucket
contains more than the prescribed occupancy. -/
theorem zetaRightDyadicGaussianGramExcluding_le_fullMass_or_quantitativeCluster
    {x beta t m : ℝ} (k occupancy : ℕ) (S : Finset ℂ)
    (hx : 0 < x) (ht : 0 ≤ t) (hm : 1 ≤ m) :
    zetaRightDyadicGaussianGramExcluding x beta k S t m ≤
        MathlibAux.gaussianBucketSchurConstant * (occupancy + 1 : ℝ) *
          zetaRightDyadicFullMassSquareExcluding x beta k S ∨
      ∃ n ∈ Finset.image Prod.fst (zetaRightDyadicPairsExcluding beta k S),
        occupancy + 1 <
          {p ∈ zetaRightDyadicPairsExcluding beta k S | p.1 = n}.card := by
  classical
  by_cases hcluster :
      ∃ n ∈ Finset.image Prod.fst (zetaRightDyadicPairsExcluding beta k S),
        occupancy + 1 <
          {p ∈ zetaRightDyadicPairsExcluding beta k S | p.1 = n}.card
  · exact Or.inr hcluster
  · left
    have hoccupancy :
        ∀ n ∈ Finset.image Prod.fst (zetaRightDyadicPairsExcluding beta k S),
          {p ∈ zetaRightDyadicPairsExcluding beta k S | p.1 = n}.card ≤ occupancy + 1 := by
      intro n hn
      exact Nat.le_of_not_gt fun hgt => hcluster ⟨n, hn, hgt⟩
    simpa only [Nat.cast_add, Nat.cast_one] using
      (zetaRightDyadicGaussianGramExcluding_le_occupancy_mul_fullMass
        (beta := beta) k occupancy S hx ht hm hoccupancy)

/-- The bounded-occupancy branch of the excluded zeta Gram dichotomy is bounded
by the four positive/negative Carlson dyadic capacities from the full-mass
bridge; otherwise the same actual excluded bucket set contains a quantitative
unit cluster. -/
theorem
    zetaRightDyadicGaussianGramExcluding_le_fourCarlsonCapacities_or_quantitativeCluster
    {x sigma beta t m : ℝ} (k occupancy : ℕ) (S : Finset ℂ)
    (hx : 1 ≤ x) (hk : 1 ≤ k) (hsigma : sigma < beta)
    (ht : 0 ≤ t) (hm : 1 ≤ m) :
    zetaRightDyadicGaussianGramExcluding x beta k S t m ≤
        MathlibAux.gaussianBucketSchurConstant * (occupancy + 1 : ℝ) *
          ((x ^ (1 - beta)) ^ 2 *
            (actualCarlsonDyadicStripSquareReciprocalCapacityExcluding sigma 1 (k - 1) S +
                actualCarlsonDyadicStripSquareReciprocalCapacityExcluding sigma 1 k S +
              (actualCarlsonDyadicStripSquareReciprocalCapacityExcluding sigma 1 (k - 1)
                  (conjugateFinset S) +
                actualCarlsonDyadicStripSquareReciprocalCapacityExcluding sigma 1 k
                  (conjugateFinset S)))) ∨
      ∃ n ∈ Finset.image Prod.fst (zetaRightDyadicPairsExcluding beta k S),
        occupancy + 1 <
          {p ∈ zetaRightDyadicPairsExcluding beta k S | p.1 = n}.card := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rcases zetaRightDyadicGaussianGramExcluding_le_fullMass_or_quantitativeCluster
      k occupancy S hxpos ht hm with henergy | hcluster
  · left
    refine henergy.trans ?_
    exact mul_le_mul_of_nonneg_left
      (zetaRightDyadicFullMassSquareExcluding_le_fourCarlsonCapacities
        hx hk hsigma)
      (by
        unfold MathlibAux.gaussianBucketSchurConstant
        exact mul_nonneg
          (mul_nonneg (by norm_num)
            (tsum_nonneg (g := MathlibAux.gaussianBucketProfile) fun d => by
              change 0 ≤ Real.exp (-((d - 1 : ℕ) : ℝ))
              exact Real.exp_nonneg _))
          (by positivity))
  · exact Or.inr hcluster

end ExcludedDyadicGramDetectCount

end VKEdgePiOverTwo
end PrimeNumberTheorem
