import PrimeNumberTheorem.ExceptionalZeroTargetDyadicOccupancy

open Complex Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Quantitative decay of target dyadic square capacity

The dynamic packet uses the same absolute-ordinate unit buckets as the
collision-safe high-zero estimate.  Inside one packet, the sum of squared
reciprocal-multiplicity coefficients is bounded by the square of the full
bucket coefficient mass.  The existing `O(log n / n)` bucket estimate then
gives a uniform `O(log^2 H / H)` bound over a dyadic block of height `H`.
-/

/-- The square reciprocal capacity of a surviving packet is bounded by the
square of the complete unit-bucket reciprocal coefficient mass. -/
theorem dynamicComplementZeroPacket_squareReciprocalCapacity_le_bucketMass_sq
    (S : Finset ℂ) (T : ℝ) (n : ℕ) :
    (∑ rho ∈ dynamicComplementZeroPacket S T n,
        (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) ≤
      zeroOrdinateUnitBucketCoefficientMass n ^ 2 := by
  have hsubset :
      dynamicComplementZeroPacket S T n ⊆ zeroOrdinateUnitBucket n := by
    intro rho hrho
    exact (Finset.mem_inter.mp hrho).1
  calc
    (∑ rho ∈ dynamicComplementZeroPacket S T n,
        (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) =
        ∑ rho ∈ dynamicComplementZeroPacket S T n,
          ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) ^ 2 := by
      apply Finset.sum_congr rfl
      intro rho hrho
      rw [div_pow]
    _ ≤ ∑ rho ∈ zeroOrdinateUnitBucket n,
          ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun rho _ _ => sq_nonneg _)
    _ ≤ (∑ rho ∈ zeroOrdinateUnitBucket n,
          (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) ^ 2 := by
      exact Finset.sum_sq_le_sq_sum_of_nonneg fun rho _ =>
        div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
    _ = zeroOrdinateUnitBucketCoefficientMass n ^ 2 := by
      rfl

/-- Uniform dyadic decay of the surviving square reciprocal capacity.  The
constant is independent of the deleted set `S`, truncation height `T`, and
dyadic index `k`. -/
theorem exists_dynamicComplementDyadicSquareReciprocalCapacity_le_log_sq_div :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Finset ℂ) (T : ℝ) (k : ℕ), 4 ≤ 2 ^ k →
        dynamicComplementDyadicSquareReciprocalCapacity S T k ≤
          C ^ 2 *
            (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)) ^ 2 /
              (2 : ℝ) ^ k := by
  rcases exists_zeroOrdinateUnitBucketCoefficientMass_le_log_div with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro S T k hk
  let H : ℝ := (2 : ℝ) ^ k
  let L : ℝ := 1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)
  have hH : 0 < H := by dsimp [H]; positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    have hpow : 0 ≤ (2 : ℝ) ^ (k + 1) := by positivity
    have harg : 1 ≤ (2 : ℝ) ^ (k + 1) + 7 := by linarith
    linarith [Real.log_nonneg harg]
  have hcard : (dyadicUnitBucketIndexSet k).card = 2 ^ k := by
    rw [dyadicUnitBucketIndexSet, Nat.card_Icc, pow_succ]
    have hpowPos : 0 < 2 ^ k := by positivity
    omega
  have hterm : ∀ n ∈ dyadicUnitBucketIndexSet k,
      (∑ rho ∈ dynamicComplementZeroPacket S T n,
          (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) ≤
        (C * L / H) ^ 2 := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hnLow, hnHigh⟩
    have hnFour : 4 ≤ n := hk.trans hnLow
    have hnPos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hnFour)
    have hnUpper : (n : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      exact_mod_cast hnHigh.trans (Nat.sub_le (2 ^ (k + 1)) 1)
    have hlog : 1 + Real.log ((n : ℝ) + 7) ≤ L := by
      dsimp [L]
      have := Real.log_le_log (by positivity : 0 < (n : ℝ) + 7)
        (by linarith : (n : ℝ) + 7 ≤ (2 : ℝ) ^ (k + 1) + 7)
      linarith
    have hnum : 0 ≤ C * L := mul_nonneg hC hL
    have hmassBound :
        zeroOrdinateUnitBucketCoefficientMass n ≤ C * L / H := by
      calc
        zeroOrdinateUnitBucketCoefficientMass n ≤
            C * (1 + Real.log ((n : ℝ) + 7)) / (n : ℝ) :=
          hmass n hnFour
        _ ≤ C * L / (n : ℝ) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog hC) hnPos.le
        _ ≤ C * L / H := by
          exact div_le_div_of_nonneg_left hnum hH
            (by dsimp [H]; exact_mod_cast hnLow)
    have hmassNonneg : 0 ≤ zeroOrdinateUnitBucketCoefficientMass n := by
      unfold zeroOrdinateUnitBucketCoefficientMass
      positivity
    have hmodelNonneg : 0 ≤ C * L / H := div_nonneg hnum hH.le
    exact
      (dynamicComplementZeroPacket_squareReciprocalCapacity_le_bucketMass_sq
        S T n).trans ((sq_le_sq₀ hmassNonneg hmodelNonneg).2 hmassBound)
  calc
    dynamicComplementDyadicSquareReciprocalCapacity S T k ≤
        ∑ n ∈ dyadicUnitBucketIndexSet k, (C * L / H) ^ 2 := by
      unfold dynamicComplementDyadicSquareReciprocalCapacity
      exact Finset.sum_le_sum hterm
    _ = C ^ 2 * L ^ 2 / H := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      dsimp [H]
      norm_num [Nat.cast_pow]
      field_simp [ne_of_gt hH]
    _ = C ^ 2 *
          (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)) ^ 2 /
            (2 : ℝ) ^ k := by rfl

/-- Combining logarithmic unit-bucket occupancy with square-capacity decay
gives a complete `O(log^3 H / H)` upper bound for one target dyadic Gram
block, unless that block already yields a farther-right zero. -/
theorem exists_rightHigherDyadic_fartherRight_or_gram_le_logCube_div :
    ∃ D : ℝ, 0 ≤ D ∧
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
              D *
                (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)) ^ 3 /
                  (2 : ℝ) ^ k := by
  rcases exists_rightHigherDyadic_fartherRight_or_gram_le_logOccupancy with
    ⟨Cocc, hCocc, hgram⟩
  rcases exists_dynamicComplementDyadicSquareReciprocalCapacity_le_log_sq_div with
    ⟨Ccap, hCcap, hcap⟩
  let D := MathlibAux.gaussianBucketSchurConstant * (1 + Cocc) * Ccap ^ 2
  refine ⟨D, by
    dsimp [D]
    exact mul_nonneg
      (mul_nonneg MathlibAux.gaussianBucketSchurConstant_pos.le (by linarith))
      (sq_nonneg Ccap), ?_⟩
  intro S Told sigma T beta a k hk hTold ha m hm
  rcases hgram S k hk hTold ha hm with hfar | hupper
  · exact Or.inl hfar
  · right
    let L : ℝ := 1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)
    have hL : 1 ≤ L := by
      dsimp [L]
      have hpow : 0 ≤ (2 : ℝ) ^ (k + 1) := by positivity
      have harg : 1 ≤ (2 : ℝ) ^ (k + 1) + 7 := by linarith
      linarith [Real.log_nonneg harg]
    have hcapBound :=
      hcap (rightHigherExclusionSet S Told sigma T) T k hk
    have hcapacityNonneg :
        0 ≤ dynamicComplementDyadicSquareReciprocalCapacity
          (rightHigherExclusionSet S Told sigma T) T k := by
      unfold dynamicComplementDyadicSquareReciprocalCapacity
      positivity
    have hoccFactor : 1 + Cocc * L ≤ (1 + Cocc) * L := by
      nlinarith
    calc
      dynamicComplementCenteredFrozenGaussianSecondMoment
          (rightHigherExclusionSet S Told sigma T) T beta a
          (dyadicUnitBucketIndexSet k) m ≤
          MathlibAux.gaussianBucketSchurConstant * (1 + Cocc * L) *
            dynamicComplementDyadicSquareReciprocalCapacity
              (rightHigherExclusionSet S Told sigma T) T k := by
        simpa [L] using hupper
      _ ≤ MathlibAux.gaussianBucketSchurConstant * ((1 + Cocc) * L) *
            (Ccap ^ 2 * L ^ 2 / (2 : ℝ) ^ k) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hoccFactor
            MathlibAux.gaussianBucketSchurConstant_pos.le)
          hcapBound hcapacityNonneg
          (mul_nonneg MathlibAux.gaussianBucketSchurConstant_pos.le
            (mul_nonneg (by linarith) (zero_le_one.trans hL)))
      _ = D * L ^ 3 / (2 : ℝ) ^ k := by
        dsimp [D]
        ring
      _ = D *
          (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)) ^ 3 /
            (2 : ℝ) ^ k := by rfl

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
