import PrimeNumberTheorem.CarlsonPoleFreeMollifiedError

open Complex Filter Topology
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

private theorem summable_inv_nat_add_one_pow_four (N : ℕ) :
    Summable (fun n : ℕ => 1 / (N + n + 1 : ℝ) ^ 4) := by
  have h := summable_pow_div_add (1 : ℝ) 4 (N + 1) (by norm_num)
  apply h.congr
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  congr 2
  push_cast
  ring

/-- A fourth-power tail after `N` is bounded by the telescoping inverse
cube at `N`.  The constant one is deliberately non-sharp but keeps the
later Carlson endpoint completely explicit. -/
theorem tsum_inv_nat_add_one_pow_four_le_inv_cube
    {N : ℕ} (hN : 0 < N) :
    (∑' n : ℕ, 1 / (N + n + 1 : ℝ) ^ 4) ≤
      1 / (N : ℝ) ^ 3 := by
  let f : ℕ → ℝ := fun n => 1 / (N + n : ℝ) ^ 3
  let g : ℕ → ℝ := fun n => f n - f (n + 1)
  have hdenTop : Tendsto (fun n : ℕ => (N + n : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono'
      (l := atTop) (f₁ := fun n : ℕ => (n : ℝ))
    · exact Eventually.of_forall fun n => by norm_num
    · exact tendsto_natCast_atTop_atTop
  have hbase0 : Tendsto (fun n : ℕ => 1 / (N + n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hdenTop
  have hf0 : Tendsto f atTop (nhds 0) := by
    have hpow := hbase0.pow 3
    simpa [f, one_div, inv_pow] using hpow
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    dsimp [g, f]
    have hA : 0 < (N + n : ℝ) := by positivity
    have hle : (N + n : ℝ) ≤ N + (n + 1 : ℕ) := by norm_num
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (pow_pos hA 3) (by gcongr))
  have hgHas : HasSum g (1 / (N : ℝ) ^ 3) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hg_nonneg]
    have htel : (fun m : ℕ => ∑ n ∈ Finset.range m, g n) =
        fun m => f 0 - f m := by
      funext m
      exact Finset.sum_range_sub' f m
    rw [htel]
    convert hf0.const_sub (1 / (N : ℝ) ^ 3) using 1 <;> simp [f]
  have hp := summable_inv_nat_add_one_pow_four N
  have hpoint : ∀ n : ℕ,
      1 / (N + n + 1 : ℝ) ^ 4 ≤ g n := by
    intro n
    dsimp [g, f]
    push_cast
    rw [show (N : ℝ) + (n + 1) = (N : ℝ) + n + 1 by ring]
    have hA : 0 < (N : ℝ) + n := by positivity
    have hB : 0 < (N : ℝ) + n + 1 := by positivity
    have hid :
        1 / ((N : ℝ) + n) ^ 3 -
              1 / ((N : ℝ) + n + 1) ^ 3 -
            1 / ((N : ℝ) + n + 1) ^ 4 =
          (2 * ((N : ℝ) + n) ^ 3 +
              6 * ((N : ℝ) + n) ^ 2 +
              4 * ((N : ℝ) + n) + 1) /
            (((N : ℝ) + n) ^ 3 * ((N : ℝ) + n + 1) ^ 4) := by
      field_simp [hA.ne', hB.ne']
      ring
    rw [← sub_nonneg, hid]
    positivity
  calc
    (∑' n : ℕ, 1 / (N + n + 1 : ℝ) ^ 4) ≤ ∑' n : ℕ, g n :=
      Summable.tsum_le_tsum hpoint hp hgHas.summable
    _ = 1 / (N : ℝ) ^ 3 := hgHas.tsum_eq

/-- A finite fourth-power interval immediately after `N` is bounded by the
same inverse cube as the complete tail. -/
theorem sum_inv_pow_four_Ioc_le_inv_cube
    {N U : ℕ} (hN : 0 < N) :
    (∑ n ∈ Finset.Ioc N U, 1 / (n : ℝ) ^ 4) ≤
      1 / (N : ℝ) ^ 3 := by
  let S : Finset ℕ := Finset.Ioc N U
  let q : ℕ → ℝ := fun k => 1 / (N + k + 1 : ℝ) ^ 4
  have hinj : Set.InjOn (fun n : ℕ => n - N - 1) (S : Set ℕ) := by
    intro a ha b hb hab
    have haN : N < a := (Finset.mem_Ioc.mp ha).1
    have hbN : N < b := (Finset.mem_Ioc.mp hb).1
    have hab' : a - N - 1 = b - N - 1 := by simpa only using hab
    have haeq : a = N + 1 + (a - N - 1) := by omega
    have hbeq : b = N + 1 + (b - N - 1) := by omega
    calc
      a = N + 1 + (a - N - 1) := haeq
      _ = N + 1 + (b - N - 1) := by rw [hab']
      _ = b := hbeq.symm
  have hsum :
      (∑ n ∈ S, 1 / (n : ℝ) ^ 4) =
        ∑ k ∈ S.image (fun n : ℕ => n - N - 1), q k := by
    have himage :
        (∑ n ∈ S, q (n - N - 1)) =
          ∑ k ∈ S.image (fun n : ℕ => n - N - 1), q k :=
      (Finset.sum_image hinj).symm
    calc
      (∑ n ∈ S, 1 / (n : ℝ) ^ 4) =
          ∑ n ∈ S, q (n - N - 1) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnN : N < n := (Finset.mem_Ioc.mp hn).1
        dsimp [q]
        congr 2
        norm_cast
        omega
      _ = _ := himage
  have hq : Summable q := by
    simpa [q, add_assoc, add_comm, add_left_comm] using
      summable_inv_nat_add_one_pow_four N
  rw [hsum]
  calc
    (∑ k ∈ S.image (fun n : ℕ => n - N - 1), q k) ≤ ∑' k : ℕ, q k :=
      hq.sum_le_tsum _ (fun k _hk => by dsimp [q]; positivity)
    _ ≤ 1 / (N : ℝ) ^ 3 := by
      simpa [q, add_assoc, add_comm, add_left_comm] using
        tsum_inv_nat_add_one_pow_four_le_inv_cube hN

/-- The taper correction beyond the exact Moebius plateau decays like the
inverse cube of the plateau length on `Re(s) ≥ 4`. -/
theorem norm_twoScaleSelbergMollifier_sub_mobiusMollifier_le_inv_cube
    {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 4 ≤ s.re) :
    ‖HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s -
        mobiusMollifier Y0 s‖ ≤ 1 / (Y0 : ℝ) ^ 3 := by
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
        if Y0 < n then 1 / (n : ℝ) ^ 4 else 0 := by
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnY1 := (Finset.mem_Icc.mp hn).2
    have hnpos : 0 < n := Nat.zero_lt_one.trans_le hn1
    by_cases hnY0 : n ≤ Y0
    · have hcoeff :=
        HardyTheorem.twoScaleSelbergCoeff_eq_moebius
          (Y1 := Y1) hnY0
      have hzero :
          (HardyTheorem.twoScaleSelbergCoeff Y0 Y1 n : ℂ) *
                (1 / (n : ℂ) ^ s) - f n = 0 := by
        dsimp [f]
        rw [hcoeff]
        push_cast
        ring
      rw [if_pos hnY0, hzero, norm_zero,
        if_neg (not_lt_of_ge hnY0)]
    · have hY0n : Y0 < n := Nat.lt_of_not_ge hnY0
      have hcoeff :
          ‖(HardyTheorem.twoScaleSelbergCoeff Y0 Y1 n : ℂ)‖ ≤ 1 := by
        simpa [Complex.norm_real, Real.norm_eq_abs] using
          HardyTheorem.abs_twoScaleSelbergCoeff_le_one
            hY0 hY01 hn1 hnY1
      have hpow : (n : ℝ) ^ (4 : ℝ) ≤ (n : ℝ) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast hn1) hs
      have hterm :
          ‖(1 : ℂ) / (n : ℂ) ^ s‖ ≤ 1 / (n : ℝ) ^ 4 := by
        rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hnpos,
          ← Real.rpow_natCast]
        exact one_div_le_one_div_of_le
          (Real.rpow_pos_of_pos (by exact_mod_cast hnpos) 4) hpow
      simp only [if_neg hnY0, if_pos hY0n, sub_zero]
      rw [norm_mul]
      exact (mul_le_mul hcoeff hterm (norm_nonneg _) zero_le_one).trans_eq
        (one_mul _)
  have hmajorSum :
      (∑ n ∈ Finset.Icc 1 Y1,
          if Y0 < n then 1 / (n : ℝ) ^ 4 else 0) =
        ∑ n ∈ Finset.Ioc Y0 Y1, 1 / (n : ℝ) ^ 4 := by
    have htailFilter :
        (Finset.Icc 1 Y1).filter (fun n => Y0 < n) =
          Finset.Ioc Y0 Y1 := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [← Finset.sum_filter, htailFilter]
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
          if Y0 < n then 1 / (n : ℝ) ^ 4 else 0 :=
      Finset.sum_le_sum (fun n hn => hmajor n hn)
    _ = ∑ n ∈ Finset.Ioc Y0 Y1, 1 / (n : ℝ) ^ 4 := hmajorSum
    _ ≤ 1 / (Y0 : ℝ) ^ 3 :=
      sum_inv_pow_four_Ioc_le_inv_cube (Nat.zero_lt_of_lt hY0)

/-- The omitted complete Moebius-series tail has the same inverse-cube
bound on `Re(s) ≥ 4`. -/
theorem norm_LSeries_moebius_sub_mobiusMollifier_le_inv_cube
    {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s -
        mobiusMollifier X s‖ ≤ 1 / (X : ℝ) ^ 3 := by
  let mu : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ)
  have hs1 : 1 < s.re := by linarith
  have hmu : Summable (LSeries.term mu s) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs1
  have htail : Summable
      (fun n : ℕ => LSeries.term mu s (n + X + 1)) := by
    simpa [add_assoc] using (summable_nat_add_iff (X + 1)).mpr hmu
  have hpoint (n : ℕ) :
      ‖LSeries.term mu s (n + X + 1)‖ ≤
        1 / (((n + X + 1 : ℕ) : ℝ) ^ 4) := by
    have hk : n + X + 1 ≠ 0 := by omega
    have hkpos : (0 : ℝ) < ((n + X + 1 : ℕ) : ℝ) := by positivity
    have hpow :
        ((n + X + 1 : ℕ) : ℝ) ^ (4 : ℝ) ≤
          ((n + X + 1 : ℕ) : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ n + X + 1 by omega)) hs
    have hpowNat :
        ((n + X + 1 : ℕ) : ℝ) ^ (4 : ℕ) ≤
          ((n + X + 1 : ℕ) : ℝ) ^ s.re := by
      rw [← Real.rpow_natCast]
      exact hpow
    have hmuInt := ArithmeticFunction.abs_moebius_le_one
      (n := n + X + 1)
    have hmuReal :
        |(ArithmeticFunction.moebius (n + X + 1) : ℝ)| ≤ 1 := by
      exact_mod_cast hmuInt
    have hmuNorm : ‖mu (n + X + 1)‖ ≤ 1 := by
      simpa [mu, Complex.norm_intCast] using hmuReal
    rw [LSeries.norm_term_eq, if_neg hk]
    calc
      ‖mu (n + X + 1)‖ /
            ((n + X + 1 : ℕ) : ℝ) ^ s.re ≤
          1 / ((n + X + 1 : ℕ) : ℝ) ^ s.re :=
        div_le_div_of_nonneg_right hmuNorm
          (Real.rpow_nonneg hkpos.le _)
      _ ≤ 1 / (((n + X + 1 : ℕ) : ℝ) ^ (4 : ℕ)) :=
        one_div_le_one_div_of_le
          (pow_pos hkpos 4) hpowNat
  rw [LSeries_moebius_eq_mobiusMollifier_add_tail hs1]
  change ‖(mobiusMollifier X s + ∑' n : ℕ,
      LSeries.term mu s (n + X + 1)) - mobiusMollifier X s‖ ≤ _
  rw [add_sub_cancel_left]
  calc
    ‖∑' n : ℕ, LSeries.term mu s (n + X + 1)‖ ≤
        ∑' n : ℕ, ‖LSeries.term mu s (n + X + 1)‖ :=
      norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' n : ℕ, 1 / (((n + X + 1 : ℕ) : ℝ) ^ 4) := by
      apply htail.norm.tsum_le_tsum hpoint
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
        add_left_comm] using
        summable_inv_nat_add_one_pow_four X
    _ ≤ 1 / (X : ℝ) ^ 3 := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
        add_left_comm] using
        tsum_inv_nat_add_one_pow_four_le_inv_cube
          (Nat.zero_lt_of_lt hX)

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

/-- Exact plateau cancellation gives a power-decaying right-boundary bound.
Both the finite taper correction and the omitted complete Moebius tail cost
at most `Y0⁻³`; no cancellation between those two pieces is assumed. -/
theorem norm_twoScaleMollifiedZetaError_le_ten_div_three_mul_inv_cube
    {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 4 ≤ s.re) :
    ‖twoScaleMollifiedZetaError Y0 Y1 s‖ ≤
      (10 / 3 : ℝ) * (1 / (Y0 : ℝ) ^ 3) := by
  have hs1 : 1 < s.re := by linarith
  have hcorrection :=
    norm_twoScaleSelbergMollifier_sub_mobiusMollifier_le_inv_cube
      hY0 hY01 hs
  have htail :=
    norm_LSeries_moebius_sub_mobiusMollifier_le_inv_cube hY0 hs
  have htail' :
      ‖mobiusMollifier Y0 s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤
        1 / (Y0 : ℝ) ^ 3 := by
    calc
      ‖mobiusMollifier Y0 s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ =
          ‖-(LSeries (fun n =>
              (ArithmeticFunction.moebius n : ℂ)) s -
            mobiusMollifier Y0 s)‖ := by
              apply congrArg norm
              ring
      _ = ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s -
          mobiusMollifier Y0 s‖ := norm_neg _
      _ ≤ 1 / (Y0 : ℝ) ^ 3 := htail
  have hdifference :
      ‖HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤
        2 * (1 / (Y0 : ℝ) ^ 3) := by
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
      _ ≤ 1 / (Y0 : ℝ) ^ 3 + 1 / (Y0 : ℝ) ^ 3 :=
        add_le_add hcorrection htail'
      _ = 2 * (1 / (Y0 : ℝ) ^ 3) := by ring
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
        (5 / 3 : ℝ) * (2 * (1 / (Y0 : ℝ) ^ 3)) :=
      mul_le_mul hzetaNorm hdifference (norm_nonneg _) (by norm_num)
    _ = (10 / 3 : ℝ) * (1 / (Y0 : ℝ) ^ 3) := by ring

/-- The pole-removal factor `(s-1)/(s+1)` has norm at most one throughout
the closed right half-plane. -/
theorem norm_sub_one_div_add_one_le_one_of_re_nonneg
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(s - 1) / (s + 1)‖ ≤ 1 := by
  have hden : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hsq : ‖s - 1‖ ^ 2 ≤ ‖s + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    nlinarith
  rw [norm_div, div_le_one (norm_pos_iff.mpr hden)]
  exact (sq_le_sq₀ (norm_nonneg (s - 1)) (norm_nonneg (s + 1))).mp hsq

/-- The pole-free error inherits the exact inverse-cube right-boundary
decay; the regularizing factor costs no power and no constant. -/
theorem norm_poleFreeTwoScaleMollifiedZetaError_le_ten_div_three_mul_inv_cube
    {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 4 ≤ s.re) :
    ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 s‖ ≤
      (10 / 3 : ℝ) * (1 / (Y0 : ℝ) ^ 3) := by
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hsneg1 : s ≠ -1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  rw [poleFreeTwoScaleMollifiedZetaError_eq_mul hs0 hs1 hsneg1, norm_mul]
  calc
    ‖(s - 1) / (s + 1)‖ * ‖twoScaleMollifiedZetaError Y0 Y1 s‖ ≤
        1 * ((10 / 3 : ℝ) * (1 / (Y0 : ℝ) ^ 3)) :=
      mul_le_mul
        (norm_sub_one_div_add_one_le_one_of_re_nonneg (by linarith))
        (norm_twoScaleMollifiedZetaError_le_ten_div_three_mul_inv_cube
          hY0 hY01 hs)
        (norm_nonneg _) zero_le_one
    _ = (10 / 3 : ℝ) * (1 / (Y0 : ℝ) ^ 3) := one_mul _

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

/-- The regularized two-scale detector is not locally identically zero at
any point of the right half-plane.  A quantitative nonzero value at s=4 is
propagated through the connected analytic domain. -/
theorem analyticOrderAt_regularizedTwoScaleCarlsonZeroDetector_ne_top
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt
        (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) s ≠ ⊤ := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  let x : ℂ := 4
  have hanalytic : AnalyticOnNhd ℂ
      (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) U :=
    analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl Y0 Y1
  have hxU : x ∈ U := by simp [x, U]
  have hsU : s ∈ U := by simpa [U] using hs
  have hxnorm :
      1 ≤ ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 x‖ := by
    apply one_le_norm_regularizedTwoScaleCarlsonZeroDetector_of_four_le_re
    · simp [x]
    · apply norm_twoScaleMollifiedZetaError_le_one_div_three_of_four_le_re
        hY0 hY01
      simp [x]
  have hxne : regularizedTwoScaleCarlsonZeroDetector Y0 Y1 x ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hxnorm
    norm_num at hxnorm
  have hxorder :
      analyticOrderAt
        (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) x ≠ ⊤ := by
    rw [(hanalytic x hxU).analyticOrderAt_eq_zero.mpr hxne]
    exact ENat.natCast_ne_top 0
  exact hanalytic.analyticOrderAt_ne_top_of_isPreconnected
    (convex_halfSpace_re_gt 0).isPreconnected hxU hsU hxorder

end CarlsonZeroDensity
end PrimeNumberTheorem
