import PrimeNumberTheorem.ExceptionalZeroTargetDyadicCapacityDecay

open Complex Filter Set
open scoped BigOperators Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Summable target dyadic Gram budgets

The one-block target estimate decays like `log^3 H / H` at dyadic height
`H = 2^k`.  This module proves that numerical majorant is summable and
packages the result as a finite-tail alternative: sufficiently high dyadic
blocks either contain a genuinely farther-right zero, or their total frozen
Gaussian Gram mass is arbitrarily small.
-/

/-- The numerical majorant appearing in the target dyadic Gram estimate. -/
def dyadicLogCubeDiv (k : ℕ) : ℝ :=
  (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)) ^ 3 / (2 : ℝ) ^ k

theorem dyadicLogCubeDiv_nonneg (k : ℕ) : 0 ≤ dyadicLogCubeDiv k := by
  unfold dyadicLogCubeDiv
  have hpow : 0 ≤ (2 : ℝ) ^ (k + 1) := by positivity
  have harg : 1 ≤ (2 : ℝ) ^ (k + 1) + 7 := by linarith
  exact div_nonneg (pow_nonneg (by linarith [Real.log_nonneg harg]) 3) (by positivity)

private theorem dyadicLogFactor_le_linear (k : ℕ) :
    1 + Real.log ((2 : ℝ) ^ (k + 1) + 7) ≤
      5 * ((k + 1 : ℕ) : ℝ) := by
  have hpowOne : 1 ≤ (2 : ℝ) ^ (k + 1) := by
    exact one_le_pow₀ (by norm_num)
  have hargPos : 0 < (2 : ℝ) ^ (k + 1) + 7 := by positivity
  have hargLe :
      (2 : ℝ) ^ (k + 1) + 7 ≤ 8 * (2 : ℝ) ^ (k + 1) := by
    nlinarith
  have hlog := Real.log_le_log hargPos hargLe
  have hlogTwo : Real.log 2 ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hrewrite :
      Real.log (8 * (2 : ℝ) ^ (k + 1)) =
        3 * Real.log 2 + ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_mul
      (pow_ne_zero 3 (by norm_num)) (pow_ne_zero (k + 1) (by norm_num)),
      Real.log_pow, Real.log_pow]
    norm_num
  rw [hrewrite] at hlog
  have hk : 0 ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg k
  have hkOne : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_num
  rw [hkOne] at hlog ⊢
  nlinarith

private theorem dyadicLogCubeDiv_le_geometricModel (k : ℕ) :
    dyadicLogCubeDiv k ≤
      125 * (((k + 1 : ℕ) : ℝ) ^ 3 * (1 / 2 : ℝ) ^ k) := by
  have hfactorNonneg :
      0 ≤ 1 + Real.log ((2 : ℝ) ^ (k + 1) + 7) := by
    have hpow : 0 ≤ (2 : ℝ) ^ (k + 1) := by positivity
    have harg : 1 ≤ (2 : ℝ) ^ (k + 1) + 7 := by linarith
    linarith [Real.log_nonneg harg]
  have hcube := pow_le_pow_left₀ hfactorNonneg
    (dyadicLogFactor_le_linear k) 3
  calc
    dyadicLogCubeDiv k ≤
        (5 * ((k + 1 : ℕ) : ℝ)) ^ 3 / (2 : ℝ) ^ k := by
      exact div_le_div_of_nonneg_right hcube (by positivity)
    _ = 125 * (((k + 1 : ℕ) : ℝ) ^ 3 * (1 / 2 : ℝ) ^ k) := by
      rw [one_div_pow]
      field_simp [pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)]
      ring

/-- The dyadic `log^3 H / H` majorant is summable. -/
theorem summable_dyadicLogCubeDiv : Summable dyadicLogCubeDiv := by
  have hbase : Summable (fun n : ℕ =>
      (n : ℝ) ^ 3 * (1 / 2 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 3 (by norm_num)
  have hshift : Summable (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) ^ 3 * (1 / 2 : ℝ) ^ (n + 1))) :=
    (summable_nat_add_iff 1).2 hbase
  have hmodel : Summable (fun n : ℕ =>
      125 * (((n + 1 : ℕ) : ℝ) ^ 3 * (1 / 2 : ℝ) ^ n)) := by
    refine (hshift.mul_left 250).congr ?_
    intro n
    rw [pow_succ]
    ring
  exact Summable.of_nonneg_of_le dyadicLogCubeDiv_nonneg
    dyadicLogCubeDiv_le_geometricModel hmodel

/-- Every sufficiently high finite dyadic interval has arbitrarily small
total numerical `log^3 H / H` budget. -/
theorem eventually_sum_Icc_dyadicLogCubeDiv_lt
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ K : ℕ in atTop,
      ∀ N : ℕ, K ≤ N →
        (∑ k ∈ Finset.Icc K N, dyadicLogCubeDiv k) < eta := by
  have hsummable := summable_dyadicLogCubeDiv
  rw [summable_iff_vanishing_norm] at hsummable
  obtain ⟨cutoff, hcutoff⟩ := hsummable eta heta
  let K0 : ℕ := if h : cutoff.Nonempty then cutoff.max' h + 1 else 0
  filter_upwards [eventually_ge_atTop K0] with K hK
  intro N hKN
  have hdisjoint : Disjoint (Finset.Icc K N) cutoff := by
    rw [Finset.disjoint_left]
    intro k hkIcc hkCutoff
    have hkLower : K ≤ k := (Finset.mem_Icc.mp hkIcc).1
    by_cases hne : cutoff.Nonempty
    · have hkMax : k ≤ cutoff.max' hne := Finset.le_max' cutoff k hkCutoff
      have hK0 : cutoff.max' hne + 1 ≤ K := by
        simpa [K0, hne] using hK
      omega
    · exact (hne ⟨k, hkCutoff⟩).elim
  have hsmall := hcutoff (Finset.Icc K N) hdisjoint
  rw [Real.norm_eq_abs, abs_of_nonneg] at hsmall
  · exact hsmall
  · exact Finset.sum_nonneg fun k _ => dyadicLogCubeDiv_nonneg k

/-- A genuinely farther-right surviving zero in dyadic block `k`. -/
def rightHigherDyadicFartherRight
    (S : Finset ℂ) (Told sigma T beta : ℝ) (k : ℕ) : Prop :=
  ∃ n ∈ dyadicUnitBucketIndexSet k, ∃ rho,
    rho ∈ dynamicComplementZeroPacket
        (rightHigherExclusionSet S Told sigma T) T n ∧
      beta < rho.re ∧
      rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
      Told < rho.im ∧ rho ∉ S

/-- For fixed analytic parameters, every sufficiently high finite dyadic
interval either produces a farther-right surviving zero, or has arbitrarily
small total centered frozen Gaussian Gram mass.  This is an upper-budget
statement only; it supplies no Sharp lower bound or repeatable residual
energy. -/
theorem eventually_rightHigherDyadic_fartherRight_or_gram_tail_lt
    (S : Finset ℂ) {Told sigma T beta a m eta : ℝ}
    (hTold : 0 ≤ Told) (ha : 0 ≤ a) (hm : 1 ≤ m) (heta : 0 < eta) :
    ∀ᶠ K : ℕ in atTop,
      ∀ N : ℕ, K ≤ N →
        (∃ k ∈ Finset.Icc K N,
            rightHigherDyadicFartherRight S Told sigma T beta k) ∨
          (∑ k ∈ Finset.Icc K N,
            dynamicComplementCenteredFrozenGaussianSecondMoment
              (rightHigherExclusionSet S Told sigma T) T beta a
              (dyadicUnitBucketIndexSet k) m) < eta := by
  rcases exists_rightHigherDyadic_fartherRight_or_gram_le_logCube_div with
    ⟨D, hD, hblock⟩
  have hden : 0 < D + 1 := by linarith
  have htail := eventually_sum_Icc_dyadicLogCubeDiv_lt
    (div_pos heta hden)
  filter_upwards [eventually_ge_atTop 2, htail] with K hK htailK
  intro N hKN
  by_cases hfar : ∃ k ∈ Finset.Icc K N,
      rightHigherDyadicFartherRight S Told sigma T beta k
  · exact Or.inl hfar
  · right
    have hterm : ∀ k ∈ Finset.Icc K N,
        dynamicComplementCenteredFrozenGaussianSecondMoment
            (rightHigherExclusionSet S Told sigma T) T beta a
            (dyadicUnitBucketIndexSet k) m ≤
          D * dyadicLogCubeDiv k := by
      intro k hk
      have hkTwo : 2 ≤ k := hK.trans (Finset.mem_Icc.mp hk).1
      have hkFour : 4 ≤ 2 ^ k := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := pow_le_pow_right' (by norm_num) hkTwo
      rcases hblock S k hkFour hTold ha hm with hfarBlock | hgram
      · exact (hfar ⟨k, hk, hfarBlock⟩).elim
      · simpa only [dyadicLogCubeDiv, mul_div_assoc] using hgram
    have hsum :
        (∑ k ∈ Finset.Icc K N,
          dynamicComplementCenteredFrozenGaussianSecondMoment
            (rightHigherExclusionSet S Told sigma T) T beta a
            (dyadicUnitBucketIndexSet k) m) ≤
          D * (∑ k ∈ Finset.Icc K N, dyadicLogCubeDiv k) := by
      calc
        (∑ k ∈ Finset.Icc K N,
          dynamicComplementCenteredFrozenGaussianSecondMoment
            (rightHigherExclusionSet S Told sigma T) T beta a
            (dyadicUnitBucketIndexSet k) m) ≤
            ∑ k ∈ Finset.Icc K N, D * dyadicLogCubeDiv k := by
          exact Finset.sum_le_sum hterm
        _ = D * (∑ k ∈ Finset.Icc K N, dyadicLogCubeDiv k) := by
          rw [Finset.mul_sum]
    have hscaled :
        D * (∑ k ∈ Finset.Icc K N, dyadicLogCubeDiv k) ≤
          D * (eta / (D + 1)) :=
      mul_le_mul_of_nonneg_left (htailK N hKN).le hD
    have hratio : D * (eta / (D + 1)) < eta := by
      rw [← mul_div_assoc, div_lt_iff₀ hden]
      nlinarith
    exact hsum.trans_lt (hscaled.trans_lt hratio)

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
