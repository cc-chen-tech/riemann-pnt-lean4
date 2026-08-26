import PrimeNumberTheorem.CarlsonTwoScaleDetector

open Complex
open scoped ArithmeticFunction BigOperators

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

private theorem summable_inv_nat_add_two_pow_three :
    Summable (fun n : ℕ => 1 / (n + 2 : ℝ) ^ (3 : ℝ)) := by
  have h := Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3)
  have hshift := (summable_nat_add_iff 2).mpr h
  simpa only [Real.rpow_natCast, Nat.cast_add, Nat.cast_ofNat] using hshift

private theorem summable_inv_nat_add_three_pow_four :
    Summable (fun n : ℕ => 1 / (n + 3 : ℝ) ^ (4 : ℝ)) := by
  have h := Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 4)
  have hshift := (summable_nat_add_iff 3).mpr h
  simpa only [Real.rpow_natCast, Nat.cast_add, Nat.cast_ofNat] using hshift

theorem tsum_inv_nat_add_three_pow_four_le :
    (∑' n : ℕ, 1 / (n + 3 : ℝ) ^ (4 : ℝ)) ≤ (1 / 24 : ℝ) := by
  let f : ℕ → ℝ := fun n => 1 / (n + 2 : ℝ) ^ (3 : ℝ)
  have hf : Summable f := by
    simpa [f] using summable_inv_nat_add_two_pow_three
  have hfshift : Summable (fun n => f (n + 1)) :=
    (summable_nat_add_iff 1).mpr hf
  have hdiff : Summable (fun n => f n - f (n + 1)) := hf.sub hfshift
  have hdiffSum : (∑' n : ℕ, (f n - f (n + 1))) = (1 / 8 : ℝ) := by
    rw [hf.tsum_sub hfshift]
    have hsplit := hf.sum_add_tsum_nat_add 1
    have hsplit' :
        f 0 + (∑' n : ℕ, f (n + 1)) = ∑' n : ℕ, f n := by
      simpa using hsplit
    have hf0 : f 0 = (1 / 8 : ℝ) := by
      norm_num [f, Real.rpow_natCast]
    rw [← hsplit', add_sub_cancel_right, hf0]
  have hg : Summable (fun n => (1 / 3 : ℝ) * (f n - f (n + 1))) :=
    hdiff.mul_left _
  have hgSum :
      (∑' n : ℕ, (1 / 3 : ℝ) * (f n - f (n + 1))) = (1 / 24 : ℝ) := by
    rw [tsum_mul_left, hdiffSum]
    norm_num
  have hpoint (n : ℕ) :
      1 / (n + 3 : ℝ) ^ (4 : ℝ) ≤
        (1 / 3 : ℝ) * (f n - f (n + 1)) := by
    have h2 : (0 : ℝ) < n + 2 := by positivity
    have h3 : (0 : ℝ) < n + 3 := by positivity
    dsimp [f]
    push_cast
    have hp2 : ((n : ℝ) + 2) ^ (3 : ℝ) = ((n : ℝ) + 2) ^ (3 : ℕ) := by
      exact Real.rpow_natCast ((n : ℝ) + 2) 3
    have hp3 :
        ((n : ℝ) + 1 + 2) ^ (3 : ℝ) =
          ((n : ℝ) + 1 + 2) ^ (3 : ℕ) := by
      exact Real.rpow_natCast ((n : ℝ) + 1 + 2) 3
    have hp4 : ((n : ℝ) + 3) ^ (4 : ℝ) = ((n : ℝ) + 3) ^ (4 : ℕ) := by
      exact Real.rpow_natCast ((n : ℝ) + 3) 4
    rw [hp2, hp3, hp4]
    rw [← sub_nonneg]
    have hid :
        (1 / 3 : ℝ) *
              (1 / ((n : ℝ) + 2) ^ 3 -
                1 / ((n : ℝ) + 1 + 2) ^ 3) -
            1 / ((n : ℝ) + 3) ^ 4 =
          (6 * (n : ℝ) ^ 2 + 28 * (n : ℝ) + 33) /
            (3 * ((n : ℝ) + 2) ^ 3 * ((n : ℝ) + 3) ^ 4) := by
      field_simp [h2.ne', h3.ne']
      ring
    calc
      0 ≤ (6 * (n : ℝ) ^ 2 + 28 * (n : ℝ) + 33) /
            (3 * ((n : ℝ) + 2) ^ 3 * ((n : ℝ) + 3) ^ 4) := by positivity
      _ ≤ (1 / 3 : ℝ) *
              (1 / ((n : ℝ) + 2) ^ 3 -
                1 / ((n : ℝ) + 1 + 2) ^ 3) -
            1 / ((n : ℝ) + 3) ^ 4 := hid.symm.le
  have htail := summable_inv_nat_add_three_pow_four
  calc
    (∑' n : ℕ, 1 / (n + 3 : ℝ) ^ (4 : ℝ)) ≤
        ∑' n : ℕ, (1 / 3 : ℝ) * (f n - f (n + 1)) :=
      htail.tsum_le_tsum hpoint hg
    _ = (1 / 24 : ℝ) := hgSum

/-- Every finite sub-tail beginning at three obeys the same explicit bound. -/
theorem sum_inv_rpow_four_Icc_three_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 3 N, 1 / (n : ℝ) ^ (4 : ℝ)) ≤
      (1 / 24 : ℝ) := by
  let S : Finset ℕ := Finset.Icc 3 N
  let q : ℕ → ℝ := fun k => 1 / (k + 3 : ℝ) ^ (4 : ℝ)
  have hinj : Set.InjOn (fun n : ℕ => n - 3) (S : Set ℕ) := by
    intro a ha b hb hab
    have ha3 : 3 ≤ a := (Finset.mem_Icc.mp ha).1
    have hb3 : 3 ≤ b := (Finset.mem_Icc.mp hb).1
    change a - 3 = b - 3 at hab
    omega
  have hsum :
      (∑ n ∈ S, 1 / (n : ℝ) ^ (4 : ℝ)) =
        ∑ k ∈ S.image (fun n : ℕ => n - 3), q k := by
    have himage :
        (∑ n ∈ S, q (n - 3)) =
          ∑ k ∈ S.image (fun n : ℕ => n - 3), q k :=
      (Finset.sum_image hinj).symm
    calc
      (∑ n ∈ S, 1 / (n : ℝ) ^ (4 : ℝ)) =
          ∑ n ∈ S, q (n - 3) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn3 : 3 ≤ n := (Finset.mem_Icc.mp hn).1
        dsimp [q]
        congr 2
        norm_cast
        omega
      _ = _ := himage
  have hq : Summable q := by
    simpa [q] using summable_inv_nat_add_three_pow_four
  rw [hsum]
  calc
    (∑ k ∈ S.image (fun n : ℕ => n - 3), q k) ≤ ∑' k : ℕ, q k :=
      hq.sum_le_tsum _ (fun k _hk => by dsimp [q]; positivity)
    _ ≤ (1 / 24 : ℝ) := by
      simpa [q] using tsum_inv_nat_add_three_pow_four_le

/-- The finite taper correction relative to the sharp plateau cutoff is at
most the same positive sub-tail 1/24. -/
theorem norm_twoScaleSelbergMollifier_sub_mobiusMollifier_le_one_div_twenty_four
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 4 ≤ s.re) :
    ‖HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s -
        mobiusMollifier Y0 s‖ ≤ (1 / 24 : ℝ) := by
  classical
  let f : ℕ → ℂ := fun n =>
    (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s
  have hfilter :
      (Finset.Icc 1 Y1).filter (fun n => n ≤ Y0) =
        Finset.Icc 1 Y0 := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hpad :
      mobiusMollifier Y0 s =
        ∑ n ∈ Finset.Icc 1 Y1, if n ≤ Y0 then f n else 0 := by
    unfold mobiusMollifier
    rw [← Finset.sum_filter, hfilter]
  have hmajor (n : ℕ) (hn : n ∈ Finset.Icc 1 Y1) :
      ‖(HardyTheorem.twoScaleSelbergCoeff Y0 Y1 n : ℂ) *
            (1 / (n : ℂ) ^ s) -
          (if n ≤ Y0 then f n else 0)‖ ≤
        if 3 ≤ n then 1 / (n : ℝ) ^ (4 : ℝ) else 0 := by
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnY1 := (Finset.mem_Icc.mp hn).2
    have hnpos : 0 < n := Nat.zero_lt_one.trans_le hn1
    by_cases hnY0 : n ≤ Y0
    · have hcoeff :=
        HardyTheorem.twoScaleSelbergCoeff_eq_moebius
          (Y1 := Y1) hnY0
      have hzero :
          (HardyTheorem.twoScaleSelbergCoeff Y0 Y1 n : ℂ) *
                (1 / (n : ℂ) ^ s) -
              f n = 0 := by
        dsimp [f]
        rw [hcoeff]
        push_cast
        ring
      simp only [if_pos hnY0]
      rw [hzero, norm_zero]
      positivity
    · have hn3 : 3 ≤ n := by omega
      simp only [if_neg hnY0, if_pos hn3, sub_zero]
      have hcoeff :
          ‖(HardyTheorem.twoScaleSelbergCoeff Y0 Y1 n : ℂ)‖ ≤ 1 := by
        simpa [Complex.norm_real, Real.norm_eq_abs] using
          HardyTheorem.abs_twoScaleSelbergCoeff_le_one
            (le_trans (by norm_num) hY0) hY01 hn1 hnY1
      have hpow :
          (n : ℝ) ^ (4 : ℝ) ≤ (n : ℝ) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast hn1) hs
      have hterm :
          ‖(1 : ℂ) / (n : ℂ) ^ s‖ ≤
            1 / (n : ℝ) ^ (4 : ℝ) := by
        rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hnpos]
        exact one_div_le_one_div_of_le
          (Real.rpow_pos_of_pos (by exact_mod_cast hnpos) 4) hpow
      rw [norm_mul]
      exact (mul_le_mul hcoeff hterm (norm_nonneg _) zero_le_one).trans_eq
        (one_mul _)
  have hmajorSum :
      (∑ n ∈ Finset.Icc 1 Y1,
          if 3 ≤ n then 1 / (n : ℝ) ^ (4 : ℝ) else 0) =
        ∑ n ∈ Finset.Icc 3 Y1, 1 / (n : ℝ) ^ (4 : ℝ) := by
    have hfilter3 :
        (Finset.Icc 1 Y1).filter (fun n => 3 ≤ n) =
          Finset.Icc 3 Y1 := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [← Finset.sum_filter, hfilter3]
  rw [hpad]
  unfold HardyTheorem.twoScaleSelbergMollifier
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ n ∈ Finset.Icc 1 Y1,
        ((HardyTheorem.twoScaleSelbergCoeff Y0 Y1 n : ℂ) *
            (1 / (n : ℂ) ^ s) -
          if n ≤ Y0 then f n else 0)‖ ≤
        ∑ n ∈ Finset.Icc 1 Y1,
          ‖(HardyTheorem.twoScaleSelbergCoeff Y0 Y1 n : ℂ) *
              (1 / (n : ℂ) ^ s) -
            (if n ≤ Y0 then f n else 0)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 Y1,
          if 3 ≤ n then 1 / (n : ℝ) ^ (4 : ℝ) else 0 :=
      Finset.sum_le_sum (fun n hn => hmajor n hn)
    _ = ∑ n ∈ Finset.Icc 3 Y1, 1 / (n : ℝ) ^ (4 : ℝ) :=
      hmajorSum
    _ ≤ (1 / 24 : ℝ) := sum_inv_rpow_four_Icc_three_le Y1

/-- A sharp Moebius cutoff at least two has an absolutely convergent
far-right tail bounded by 1/24. -/
theorem norm_LSeries_moebius_sub_mobiusMollifier_le_one_div_twenty_four
    {X : ℕ} (hX : 2 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s -
        mobiusMollifier X s‖ ≤ (1 / 24 : ℝ) := by
  let mu : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ)
  have hs1 : 1 < s.re := by linarith
  have hmu : Summable (LSeries.term mu s) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs1
  have htail : Summable
      (fun n : ℕ => LSeries.term mu s (n + X + 1)) := by
    simpa [add_assoc] using (summable_nat_add_iff (X + 1)).mpr hmu
  have hpoint (n : ℕ) :
      ‖LSeries.term mu s (n + X + 1)‖ ≤
        1 / (n + 3 : ℝ) ^ (4 : ℝ) := by
    have hk : n + X + 1 ≠ 0 := by omega
    have hkpos : (0 : ℝ) < ((n + X + 1 : ℕ) : ℝ) := by positivity
    have hn3pos : (0 : ℝ) < n + 3 := by positivity
    have hn3one : (1 : ℝ) ≤ n + 3 := by
      exact_mod_cast (show 1 ≤ n + 3 by omega)
    have hbase : (n + 3 : ℝ) ≤ ((n + X + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show n + 3 ≤ n + X + 1 by omega)
    have hpowExp :
        (n + 3 : ℝ) ^ (4 : ℝ) ≤ (n + 3 : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hn3one hs
    have hpowBase :
        (n + 3 : ℝ) ^ s.re ≤ ((n + X + 1 : ℕ) : ℝ) ^ s.re :=
      Real.rpow_le_rpow (by positivity) hbase (by linarith)
    have hden :
        (n + 3 : ℝ) ^ (4 : ℝ) ≤ ((n + X + 1 : ℕ) : ℝ) ^ s.re :=
      hpowExp.trans hpowBase
    have hmuInt := ArithmeticFunction.abs_moebius_le_one
      (n := n + X + 1)
    have hmuReal :
        |(ArithmeticFunction.moebius (n + X + 1) : ℝ)| ≤ 1 := by
      exact_mod_cast hmuInt
    have hmuNorm : ‖mu (n + X + 1)‖ ≤ 1 := by
      simpa [mu, Complex.norm_intCast] using hmuReal
    rw [LSeries.norm_term_eq, if_neg hk]
    calc
      ‖mu (n + X + 1)‖ / ((n + X + 1 : ℕ) : ℝ) ^ s.re ≤
          1 / ((n + X + 1 : ℕ) : ℝ) ^ s.re :=
        div_le_div_of_nonneg_right hmuNorm (Real.rpow_nonneg hkpos.le _)
      _ ≤ 1 / (n + 3 : ℝ) ^ (4 : ℝ) :=
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hn3pos 4) hden
  rw [LSeries_moebius_eq_mobiusMollifier_add_tail hs1]
  change ‖(mobiusMollifier X s + ∑' n : ℕ,
      LSeries.term mu s (n + X + 1)) - mobiusMollifier X s‖ ≤ _
  rw [add_sub_cancel_left]
  calc
    ‖∑' n : ℕ, LSeries.term mu s (n + X + 1)‖ ≤
        ∑' n : ℕ, ‖LSeries.term mu s (n + X + 1)‖ :=
      norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' n : ℕ, 1 / (n + 3 : ℝ) ^ (4 : ℝ) :=
      htail.norm.tsum_le_tsum hpoint summable_inv_nat_add_three_pow_four
    _ ≤ (1 / 24 : ℝ) := tsum_inv_nat_add_three_pow_four_le

/-- In absolute convergence, the two-scale mollified error is zeta times
the difference between the finite mollifier and the complete Moebius
Dirichlet series. -/
theorem twoScaleMollifiedZetaError_eq_riemannZeta_mul_moebius_difference
    {Y0 Y1 : ℕ} {s : ℂ} (hs : 1 < s.re) :
    twoScaleMollifiedZetaError Y0 Y1 s =
      riemannZeta s *
        (HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s) := by
  have hproduct := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hproduct
  unfold twoScaleMollifiedZetaError
  rw [← hproduct]
  ring

/-- The explicit fixed-right-line bound needed at every Jensen center. -/
theorem norm_twoScaleMollifiedZetaError_le_five_div_thirty_six_of_four_le_re
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 4 ≤ s.re) :
    ‖twoScaleMollifiedZetaError Y0 Y1 s‖ ≤ (5 / 36 : ℝ) := by
  have hs1 : 1 < s.re := by linarith
  have hcorrection :=
    norm_twoScaleSelbergMollifier_sub_mobiusMollifier_le_one_div_twenty_four
      hY0 hY01 hs
  have htail :=
    norm_LSeries_moebius_sub_mobiusMollifier_le_one_div_twenty_four hY0 hs
  have htail' :
      ‖mobiusMollifier Y0 s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤
        (1 / 24 : ℝ) := by
    calc
      ‖mobiusMollifier Y0 s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ =
          ‖-(LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s -
            mobiusMollifier Y0 s)‖ := by
              apply congrArg norm
              ring
      _ = ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s -
          mobiusMollifier Y0 s‖ := norm_neg _
      _ ≤ (1 / 24 : ℝ) := htail
  have hdifference :
      ‖HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤
        (1 / 12 : ℝ) := by
    calc
      ‖HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ =
          ‖(HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s -
              mobiusMollifier Y0 s) +
            (mobiusMollifier Y0 s -
              LSeries (fun n =>
                (ArithmeticFunction.moebius n : ℂ)) s)‖ := by
                  congr 1
                  ring
      _ ≤ ‖HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s -
              mobiusMollifier Y0 s‖ +
            ‖mobiusMollifier Y0 s -
              LSeries (fun n =>
                (ArithmeticFunction.moebius n : ℂ)) s‖ := norm_add_le _ _
      _ ≤ (1 / 24 : ℝ) + (1 / 24 : ℝ) :=
        add_le_add hcorrection htail'
      _ = (1 / 12 : ℝ) := by norm_num
  have hzetaNorm : ‖riemannZeta s‖ ≤ (5 / 3 : ℝ) :=
    (ZeroFreeRegion.norm_riemannZeta_le_re_zeta_two_of_two_le_re s
      (by linarith)).trans
        ZeroFreeRegion.riemannZeta_two_re_le_five_thirds
  rw [twoScaleMollifiedZetaError_eq_riemannZeta_mul_moebius_difference hs1,
    norm_mul]
  calc
    ‖riemannZeta s‖ *
        ‖HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤
        (5 / 3 : ℝ) * (1 / 12 : ℝ) :=
      mul_le_mul hzetaNorm hdifference (norm_nonneg _) (by norm_num)
    _ = (5 / 36 : ℝ) := by norm_num

/-- The numerical form consumed by the two-scale Jensen argument. -/
theorem norm_twoScaleMollifiedZetaError_le_one_div_three_of_four_le_re
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 4 ≤ s.re) :
    ‖twoScaleMollifiedZetaError Y0 Y1 s‖ ≤ (1 / 3 : ℝ) :=
  (norm_twoScaleMollifiedZetaError_le_five_div_thirty_six_of_four_le_re
    hY0 hY01 hs).trans (by norm_num)

end CarlsonZeroDensity
end PrimeNumberTheorem
