import PrimeNumberTheorem.QuantitativeGoodHeight

open Complex Filter Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Collision-safe high-zero bucket energy

The unit ordinate buckets below keep arbitrarily close zero ordinates in the
same fiber.  The local multiplicity estimate therefore controls the complete
fiber without any zero-spacing hypothesis.  The resulting reciprocal
coefficient masses have summable squares.
-/

/-- Nontrivial zeros whose absolute ordinate lies in `[n, n + 1)`. -/
noncomputable def zeroOrdinateUnitBucket (n : ℕ) : Finset ℂ :=
  (nontrivialZerosFinset ((n : ℝ) + 9 / 4)).filter fun rho =>
    (n : ℝ) ≤ |rho.im| ∧ |rho.im| < (n : ℝ) + 1

/-- Total analytic multiplicity in one absolute-ordinate unit bucket. -/
noncomputable def zeroOrdinateUnitBucketMultiplicity (n : ℕ) : ℝ :=
  ∑ rho ∈ zeroOrdinateUnitBucket n,
    (analyticOrderNatAt riemannZeta rho : ℝ)

/-- Total reciprocal-zero coefficient mass in one unit bucket. -/
noncomputable def zeroOrdinateUnitBucketCoefficientMass (n : ℕ) : ℝ :=
  ∑ rho ∈ zeroOrdinateUnitBucket n,
    (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖

private theorem zeroOrdinateUnitBucket_subset_localWindow (n : ℕ) :
    zeroOrdinateUnitBucket n ⊆
      (nontrivialZerosFinset ((n : ℝ) + 1 / 4 + 2)).filter fun rho =>
        (n : ℝ) + 1 / 4 - 1 / 4 ≤ |rho.im| ∧
          |rho.im| ≤ (n : ℝ) + 1 / 4 + 5 / 4 := by
  intro rho hrho
  rcases Finset.mem_filter.mp hrho with ⟨hzero, hlow, hhigh⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_, ?_⟩
  · simpa only [show (n : ℝ) + 1 / 4 + 2 = (n : ℝ) + 9 / 4 by ring] using hzero
  · simpa only [show (n : ℝ) + 1 / 4 - 1 / 4 = (n : ℝ) by ring] using hlow
  · linarith

private theorem zeroOrdinateUnitBucketMultiplicity_le_local
    (n : ℕ) :
    zeroOrdinateUnitBucketMultiplicity n ≤
      ExplicitFormulaAux.localZeroMultiplicity ((n : ℝ) + 1 / 4) := by
  unfold zeroOrdinateUnitBucketMultiplicity
    ExplicitFormulaAux.localZeroMultiplicity
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (zeroOrdinateUnitBucket_subset_localWindow n)
    (fun rho _ _ => Nat.cast_nonneg (analyticOrderNatAt riemannZeta rho))

/-- Unit-bucket analytic multiplicity is `O(log n)`, uniformly in the bucket. -/
theorem exists_zeroOrdinateUnitBucketMultiplicity_le_log :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, 4 ≤ n →
        zeroOrdinateUnitBucketMultiplicity n ≤
          C * (1 + Real.log ((n : ℝ) + 7)) := by
  rcases ExplicitFormulaAux.exists_localZeroMultiplicity_le_log_bound with
    ⟨C, hC, hlocal⟩
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hnReal : 4 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog :
      Real.log ((n : ℝ) + 1 / 4 + 6) ≤
        Real.log ((n : ℝ) + 7) := by
    exact Real.log_le_log (by positivity) (by linarith)
  calc
    zeroOrdinateUnitBucketMultiplicity n ≤
        ExplicitFormulaAux.localZeroMultiplicity ((n : ℝ) + 1 / 4) :=
      zeroOrdinateUnitBucketMultiplicity_le_local n
    _ ≤ C * (1 + Real.log ((n : ℝ) + 1 / 4 + 6)) :=
      hlocal ((n : ℝ) + 1 / 4) (by linarith)
    _ ≤ C * (1 + Real.log ((n : ℝ) + 7)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC

private theorem zeroOrdinateUnitBucketCoefficientMass_nonneg (n : ℕ) :
    0 ≤ zeroOrdinateUnitBucketCoefficientMass n := by
  unfold zeroOrdinateUnitBucketCoefficientMass
  exact Finset.sum_nonneg fun rho _ =>
    div_nonneg (Nat.cast_nonneg _) (norm_nonneg rho)

private theorem zeroOrdinateUnitBucketCoefficientMass_le_div_multiplicity
    (n : ℕ) (hn : 0 < n) :
    zeroOrdinateUnitBucketCoefficientMass n ≤
      zeroOrdinateUnitBucketMultiplicity n / (n : ℝ) := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold zeroOrdinateUnitBucketCoefficientMass
    zeroOrdinateUnitBucketMultiplicity
  calc
    (∑ rho ∈ zeroOrdinateUnitBucket n,
        (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) ≤
      ∑ rho ∈ zeroOrdinateUnitBucket n,
        (analyticOrderNatAt riemannZeta rho : ℝ) / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hbucket := (Finset.mem_filter.mp hrho).2
      have hnorm : (n : ℝ) ≤ ‖rho‖ :=
        hbucket.1.trans (Complex.abs_im_le_norm rho)
      exact div_le_div_of_nonneg_left
        (Nat.cast_nonneg _) hnReal hnorm
    _ = (∑ rho ∈ zeroOrdinateUnitBucket n,
          (analyticOrderNatAt riemannZeta rho : ℝ)) / (n : ℝ) := by
      rw [Finset.sum_div]

/-- Unit-bucket reciprocal coefficient mass is `O(log n / n)`. -/
theorem exists_zeroOrdinateUnitBucketCoefficientMass_le_log_div :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, 4 ≤ n →
        zeroOrdinateUnitBucketCoefficientMass n ≤
          C * (1 + Real.log ((n : ℝ) + 7)) / (n : ℝ) := by
  rcases exists_zeroOrdinateUnitBucketMultiplicity_le_log with
    ⟨C, hC, hmult⟩
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
  exact (zeroOrdinateUnitBucketCoefficientMass_le_div_multiplicity n hnPos).trans
    (div_le_div_of_nonneg_right (hmult n hn) hnReal.le)

private theorem summable_shifted_log_sq_div_sq :
    Summable (fun n : ℕ =>
      (1 + Real.log ((n : ℝ) + 11)) ^ 2 / ((n : ℝ) + 4) ^ 2) := by
  have hp :
      Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hpShift :
      Summable (fun n : ℕ =>
        1 / (((n + 11 : ℕ) : ℝ) ^ (3 / 2 : ℝ))) := by
    exact (summable_nat_add_iff 11).2 hp
  have hmajorant :
      ∀ n : ℕ,
        (1 + Real.log ((n : ℝ) + 11)) ^ 2 / ((n : ℝ) + 4) ^ 2 ≤
          225 * (1 / (((n + 11 : ℕ) : ℝ) ^ (3 / 2 : ℝ))) := by
    intro n
    let x : ℝ := (n : ℝ) + 11
    let d : ℝ := (n : ℝ) + 4
    have hx : 0 < x := by dsimp [x]; positivity
    have hd : 0 < d := by dsimp [d]; positivity
    have hxd : x ≤ 3 * d := by
      dsimp [x, d]
      nlinarith [(Nat.cast_nonneg n : 0 ≤ (n : ℝ))]
    have hlog :
        Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
      have := Real.log_le_rpow_div hx.le (show 0 < (1 / 4 : ℝ) by norm_num)
      convert this using 1
      ring
    have hxOne : 1 ≤ x := by
      dsimp [x]
      nlinarith [(Nat.cast_nonneg n : 0 ≤ (n : ℝ))]
    have hrpowOne : 1 ≤ x ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow hxOne (by norm_num)
    have hfactor : 1 + Real.log x ≤ 5 * x ^ (1 / 4 : ℝ) := by
      linarith
    have hnonneg : 0 ≤ 1 + Real.log x := by
      linarith [Real.log_nonneg hxOne]
    have hratio :
        (1 + Real.log x) / d ≤
          15 * x ^ (1 / 4 : ℝ) / x := by
      rw [div_le_div_iff₀ hd hx]
      nlinarith [Real.rpow_nonneg hx.le (1 / 4 : ℝ)]
    have hsquare :
        ((1 + Real.log x) / d) ^ 2 ≤
          (15 * x ^ (1 / 4 : ℝ) / x) ^ 2 := by
      have hrightNonneg :
          0 ≤ 15 * x ^ (1 / 4 : ℝ) / x := by
        exact div_nonneg
          (mul_nonneg (by norm_num)
            (Real.rpow_nonneg hx.le (1 / 4 : ℝ))) hx.le
      nlinarith [div_nonneg hnonneg hd.le, hrightNonneg]
    have hid :
        (15 * x ^ (1 / 4 : ℝ) / x) ^ 2 =
          225 * (1 / x ^ (3 / 2 : ℝ)) := by
      have hxne : x ≠ 0 := hx.ne'
      have hrpowne : x ^ (3 / 2 : ℝ) ≠ 0 :=
        (Real.rpow_pos_of_pos hx _).ne'
      rw [div_pow]
      have hquarterSq :
          (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hx.le]
        norm_num
      rw [mul_pow, hquarterSq]
      field_simp [hxne, hrpowne]
      have hprod :
          x ^ (1 / 2 : ℝ) * x ^ (3 / 2 : ℝ) = x ^ 2 := by
        rw [← Real.rpow_add hx]
        norm_num
      calc
        15 ^ 2 * x ^ (1 / 2 : ℝ) * x ^ (3 / 2 : ℝ) =
            225 * (x ^ (1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := by ring
        _ = 225 * x ^ 2 := by rw [hprod]
        _ = x ^ 2 * 225 := by ring
    rw [div_pow] at hsquare
    simpa only [x, d, Nat.cast_add, Nat.cast_ofNat] using
      hsquare.trans_eq hid
  apply Summable.of_nonneg_of_le
    (fun n => div_nonneg (sq_nonneg _) (sq_nonneg _))
    hmajorant
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hpShift.mul_left 225

/-- Squared unit-bucket reciprocal coefficient masses are summable.  This is
the diagonal energy input for a collision-safe Gaussian upper bound. -/
theorem summable_sq_zeroOrdinateUnitBucketCoefficientMass :
    Summable (fun n : ℕ =>
      zeroOrdinateUnitBucketCoefficientMass n ^ 2) := by
  rcases exists_zeroOrdinateUnitBucketCoefficientMass_le_log_div with
    ⟨C, hC, hmass⟩
  have htail :
      Summable (fun n : ℕ =>
        zeroOrdinateUnitBucketCoefficientMass (n + 4) ^ 2) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ =>
        C ^ 2 *
          ((1 + Real.log ((n : ℝ) + 11)) ^ 2 /
            ((n : ℝ) + 4) ^ 2))
      (fun n => sq_nonneg
        (zeroOrdinateUnitBucketCoefficientMass (n + 4)))
      (fun n => ?_) ?_
    · have hbound := hmass (n + 4) (by omega)
      have hmassNonneg :=
        zeroOrdinateUnitBucketCoefficientMass_nonneg (n + 4)
      have hmodelNonneg :
          0 ≤ C *
            (1 + Real.log (((n + 4 : ℕ) : ℝ) + 7)) /
              ((n + 4 : ℕ) : ℝ) := by
        have harg :
            1 ≤ (((n + 4 : ℕ) : ℝ) + 7) := by
          have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          norm_num [Nat.cast_add]
          linarith
        have hfactor :
            0 ≤ 1 + Real.log (((n + 4 : ℕ) : ℝ) + 7) := by
          linarith [Real.log_nonneg harg]
        exact div_nonneg (mul_nonneg hC hfactor) (by positivity)
      have hsquare :
          zeroOrdinateUnitBucketCoefficientMass (n + 4) ^ 2 ≤
            (C *
              (1 + Real.log (((n + 4 : ℕ) : ℝ) + 7)) /
                ((n + 4 : ℕ) : ℝ)) ^ 2 := by
        nlinarith
      calc
        zeroOrdinateUnitBucketCoefficientMass (n + 4) ^ 2 ≤
            (C *
              (1 + Real.log (((n + 4 : ℕ) : ℝ) + 7)) /
                ((n + 4 : ℕ) : ℝ)) ^ 2 := hsquare
        _ = C ^ 2 *
            ((1 + Real.log ((n : ℝ) + 11)) ^ 2 /
              ((n : ℝ) + 4) ^ 2) := by
          norm_num [Nat.cast_add]
          field_simp [show (n : ℝ) + 4 ≠ 0 by positivity]
          ring
    · exact summable_shifted_log_sq_div_sq.mul_left (C ^ 2)
  exact (summable_nat_add_iff 4).mp htail

/-- Every sufficiently high finite interval of unit buckets has arbitrarily
small total squared coefficient mass. -/
theorem eventually_sum_Icc_sq_zeroOrdinateUnitBucketCoefficientMass_lt
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ H : ℕ in atTop,
      ∀ N : ℕ, H ≤ N →
        (∑ n ∈ Finset.Icc H N,
          zeroOrdinateUnitBucketCoefficientMass n ^ 2) < eta := by
  have hsummable := summable_sq_zeroOrdinateUnitBucketCoefficientMass
  rw [summable_iff_vanishing_norm] at hsummable
  obtain ⟨cutoff, hcutoff⟩ := hsummable eta heta
  let H0 : ℕ :=
    if h : cutoff.Nonempty then cutoff.max' h + 1 else 0
  filter_upwards [eventually_ge_atTop H0] with H hH
  intro N hHN
  have hdisjoint : Disjoint (Finset.Icc H N) cutoff := by
    rw [Finset.disjoint_left]
    intro n hnIcc hnCutoff
    have hnLower : H ≤ n := (Finset.mem_Icc.mp hnIcc).1
    by_cases hne : cutoff.Nonempty
    · have hnMax : n ≤ cutoff.max' hne := Finset.le_max' cutoff n hnCutoff
      have hH0 : cutoff.max' hne + 1 ≤ H := by
        simpa [H0, hne] using hH
      omega
    · exact (hne ⟨n, hnCutoff⟩).elim
  have hsmall := hcutoff (Finset.Icc H N) hdisjoint
  rw [Real.norm_eq_abs, abs_of_nonneg] at hsmall
  · exact hsmall
  · exact Finset.sum_nonneg fun n _ => sq_nonneg _

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
