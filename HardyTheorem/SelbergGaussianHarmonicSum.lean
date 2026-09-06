import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace HardyTheorem

/-! # The logarithmic damped Gaussian sum in Selberg's off-diagonal term. -/

noncomputable def selbergGaussianHarmonic (a : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-a * ((n + 1 : ℕ) : ℝ) ^ 2) / ((n + 1 : ℕ) : ℝ)

noncomputable def selbergGaussianMass (a : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-a * ((n + 1 : ℕ) : ℝ) ^ 2)

noncomputable def selbergGaussianLogHarmonic
    (a X : ℝ) (n : ℕ) : ℝ :=
  Real.log (((n + 1 : ℕ) : ℝ) * X) * selbergGaussianHarmonic a n

/-- The fixed-parameter bracket after summing the reciprocal gaps in one
residue class of step `d`; compare Titchmarsh 10.16. -/
noncomputable def selbergOffDiagonalDampedBracket
    (a X d : ℝ) (n : ℕ) : ℝ :=
  selbergGaussianHarmonic a n +
    d⁻¹ * selbergGaussianLogHarmonic a X n

noncomputable def selbergCappedGaussianParameter (a : ℝ) : ℝ := min a 1

private theorem selbergGaussianHarmonic_le_geometric
    {a : ℝ} (ha0 : 0 < a) (n : ℕ) :
    selbergGaussianHarmonic a n ≤
      Real.exp (-a) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  have hm : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left 1 n
  have hsq : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith
  have hexp :
      Real.exp (-a * ((n + 1 : ℕ) : ℝ) ^ 2) ≤
        Real.exp (-a * ((n + 1 : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hden : 0 ≤ (((n + 1 : ℕ) : ℝ))⁻¹ := by positivity
  unfold selbergGaussianHarmonic
  rw [div_eq_mul_inv, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ hden
  calc
    Real.exp (-a * ((n + 1 : ℕ) : ℝ) ^ 2) ≤
        Real.exp (-a * ((n + 1 : ℕ) : ℝ)) := hexp
    _ = Real.exp (-a) ^ (n + 1) := by
      rw [show -a * ((n + 1 : ℕ) : ℝ) =
        ((n + 1 : ℕ) : ℝ) * (-a) by ring, Real.exp_nat_mul]

theorem summable_selbergGaussianHarmonic
    {a : ℝ} (ha0 : 0 < a) :
    Summable (selbergGaussianHarmonic a) := by
  have hq0 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hq1 : Real.exp (-a) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha0)
  have hmajor : Summable (fun n : ℕ =>
      Real.exp (-a) ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) :=
    by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Real.hasSum_pow_div_log_of_abs_lt_one
          (by simpa [abs_of_nonneg hq0] using hq1)).summable
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro n
    unfold selbergGaussianHarmonic
    positivity
  · intro n
    exact selbergGaussianHarmonic_le_geometric ha0 n

private theorem selbergGaussianMass_le_geometric
    {a : ℝ} (ha0 : 0 < a) (n : ℕ) :
    selbergGaussianMass a n ≤ Real.exp (-a) ^ (n + 1) := by
  have hm : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left 1 n
  have hsq : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith
  unfold selbergGaussianMass
  calc
    Real.exp (-a * ((n + 1 : ℕ) : ℝ) ^ 2) ≤
        Real.exp (-a * ((n + 1 : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp (-a) ^ (n + 1) := by
      rw [show -a * ((n + 1 : ℕ) : ℝ) =
        ((n + 1 : ℕ) : ℝ) * (-a) by ring, Real.exp_nat_mul]

theorem summable_selbergGaussianMass {a : ℝ} (ha0 : 0 < a) :
    Summable (selbergGaussianMass a) := by
  let q : ℝ := Real.exp (-a)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha0)
  have hmajor : Summable (fun n : ℕ => q ^ (n + 1)) := by
    simpa only [pow_succ'] using
      (summable_geometric_of_lt_one hq0 hq1).mul_left q
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro n
    unfold selbergGaussianMass
    positivity
  · intro n
    simpa only [q] using selbergGaussianMass_le_geometric ha0 n

theorem mul_tsum_selbergGaussianMass_le_two
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    a * (∑' n : ℕ, selbergGaussianMass a n) ≤ 2 := by
  let q : ℝ := Real.exp (-a)
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha0)
  have hgeom : Summable (fun n : ℕ => q ^ (n + 1)) := by
    simpa only [pow_succ'] using
      (summable_geometric_of_lt_one hq0.le hq1).mul_left q
  have hmass :
      (∑' n : ℕ, selbergGaussianMass a n) ≤ q / (1 - q) := by
    calc
      (∑' n : ℕ, selbergGaussianMass a n) ≤
          ∑' n : ℕ, q ^ (n + 1) :=
        (summable_selbergGaussianMass ha0).tsum_le_tsum
          (fun n => by simpa only [q] using
            selbergGaussianMass_le_geometric ha0 n) hgeom
      _ = q / (1 - q) := by
        have hshift : (∑' n : ℕ, q ^ (n + 1)) =
            q * ∑' n : ℕ, q ^ n := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro n
          rw [pow_succ']
        rw [hshift, tsum_geometric_of_lt_one hq0.le hq1,
          div_eq_mul_inv]
  have haAdd0 : 0 < 1 + a := by linarith
  have hqInv : q ≤ (1 + a)⁻¹ := by
    dsimp [q]
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos a) haAdd0).2 (by
      simpa [add_comm] using Real.add_one_le_exp a)
  have hhalf : a / 2 ≤ 1 - q := by
    have hfrac : a / (1 + a) ≤ 1 - q := by
      have hid : 1 - (1 + a)⁻¹ = a / (1 + a) := by
        field_simp [haAdd0.ne']
        ring
      rw [← hid]
      linarith
    have haHalf : a / 2 ≤ a / (1 + a) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) haAdd0]
      nlinarith
    exact haHalf.trans hfrac
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hratio : a * (q / (1 - q)) ≤ 2 := by
    rw [show a * (q / (1 - q)) = (a * q) / (1 - q) by ring,
      div_le_iff₀ hden]
    have haq : a * q ≤ a := by
      exact mul_le_of_le_one_right ha0.le hq1.le
    nlinarith
  calc
    a * (∑' n : ℕ, selbergGaussianMass a n) ≤
        a * (q / (1 - q)) := mul_le_mul_of_nonneg_left hmass ha0.le
    _ ≤ 2 := hratio

theorem tsum_selbergGaussianHarmonic_le_log
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (∑' n : ℕ, selbergGaussianHarmonic a n) ≤ Real.log (2 / a) := by
  let q : ℝ := Real.exp (-a)
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha0)
  have hqabs : |q| < 1 := by simpa [abs_of_pos hq0] using hq1
  have hmajor : Summable (fun n : ℕ =>
      q ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) :=
    by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Real.hasSum_pow_div_log_of_abs_lt_one hqabs).summable
  have htsum :
      (∑' n : ℕ, selbergGaussianHarmonic a n) ≤ -Real.log (1 - q) := by
    calc
      (∑' n : ℕ, selbergGaussianHarmonic a n) ≤
          ∑' n : ℕ, q ^ (n + 1) / ((n + 1 : ℕ) : ℝ) :=
        (summable_selbergGaussianHarmonic ha0).tsum_le_tsum
          (fun n => by
            simpa only [q] using
              selbergGaussianHarmonic_le_geometric ha0 n)
          hmajor
      _ = -Real.log (1 - q) :=
        by
          simpa only [Nat.cast_add, Nat.cast_one] using
            (Real.hasSum_pow_div_log_of_abs_lt_one hqabs).tsum_eq
  have haAdd0 : 0 < 1 + a := by linarith
  have hqInv : q ≤ (1 + a)⁻¹ := by
    dsimp [q]
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos a) haAdd0).2 (by
      simpa [add_comm] using Real.add_one_le_exp a)
  have hfrac : a / (1 + a) ≤ 1 - q := by
    have hid : 1 - (1 + a)⁻¹ = a / (1 + a) := by
      field_simp [haAdd0.ne']
      ring
    rw [← hid]
    linarith
  have haHalf : a / 2 ≤ a / (1 + a) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) haAdd0]
    nlinarith
  have hhalf : a / 2 ≤ 1 - q := haHalf.trans hfrac
  have hhalf0 : 0 < a / 2 := by positivity
  have hlog : Real.log (a / 2) ≤ Real.log (1 - q) :=
    Real.log_le_log hhalf0 hhalf
  have hlogInv : -Real.log (a / 2) = Real.log (2 / a) := by
    rw [show 2 / a = (a / 2)⁻¹ by field_simp [ha0.ne'],
      Real.log_inv]
  calc
    (∑' n : ℕ, selbergGaussianHarmonic a n) ≤ -Real.log (1 - q) := htsum
    _ ≤ -Real.log (a / 2) := by linarith
    _ = Real.log (2 / a) := hlogInv

private theorem selberg_log_nat_le_inv_log_add_linear
    {a : ℝ} (ha0 : 0 < a) (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m : ℝ) ≤ Real.log (1 / a) + a * (m : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have ham0 : 0 < a * (m : ℝ) := mul_pos ha0 hm0
  have hlogam := Real.log_le_sub_one_of_pos ham0
  have hid : Real.log (m : ℝ) =
      Real.log (1 / a) + Real.log (a * (m : ℝ)) := by
    rw [← Real.log_mul (by positivity : 1 / a ≠ 0) ham0.ne']
    congr 1
    field_simp [ha0.ne']
  rw [hid]
  linarith

private theorem selbergGaussianLogHarmonic_le_majorant
    {a X : ℝ} (ha0 : 0 < a) (hX : 1 ≤ X) (n : ℕ) :
    selbergGaussianLogHarmonic a X n ≤
      (Real.log X + Real.log (1 / a)) * selbergGaussianHarmonic a n +
        a * selbergGaussianMass a n := by
  let m : ℕ := n + 1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hlogm := selberg_log_nat_le_inv_log_add_linear ha0 m hm
  have hlogmx : Real.log ((m : ℝ) * X) =
      Real.log (m : ℝ) + Real.log X := Real.log_mul hm0.ne' hX0.ne'
  have hlogBound : Real.log ((m : ℝ) * X) ≤
      Real.log X + Real.log (1 / a) + a * (m : ℝ) := by
    rw [hlogmx]
    linarith
  have hharm0 : 0 ≤ selbergGaussianHarmonic a n := by
    unfold selbergGaussianHarmonic
    positivity
  have hmul := mul_le_mul_of_nonneg_right hlogBound hharm0
  unfold selbergGaussianLogHarmonic
  calc
    Real.log (((n + 1 : ℕ) : ℝ) * X) *
        selbergGaussianHarmonic a n ≤
      (Real.log X + Real.log (1 / a) + a * (m : ℝ)) *
        selbergGaussianHarmonic a n := by simpa only [m] using hmul
    _ = (Real.log X + Real.log (1 / a)) *
          selbergGaussianHarmonic a n + a * selbergGaussianMass a n := by
      unfold selbergGaussianHarmonic selbergGaussianMass
      dsimp [m]
      field_simp

theorem summable_selbergGaussianLogHarmonic
    {a X : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hX : 1 ≤ X) :
    Summable (selbergGaussianLogHarmonic a X) := by
  let L : ℝ := Real.log X + Real.log (1 / a)
  have hL0 : 0 ≤ L := by
    have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
    have hinv : 1 ≤ 1 / a := (le_div_iff₀ ha0).2 (by simpa using ha1)
    have hlogInv : 0 ≤ Real.log (1 / a) := Real.log_nonneg hinv
    dsimp [L]
    positivity
  have hmajor : Summable (fun n : ℕ =>
      L * selbergGaussianHarmonic a n + a * selbergGaussianMass a n) :=
    (summable_selbergGaussianHarmonic ha0).mul_left L |>.add
      ((summable_selbergGaussianMass ha0).mul_left a)
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro n
    unfold selbergGaussianLogHarmonic
    have hmX : 1 ≤ (((n + 1 : ℕ) : ℝ) * X) := by
      have hm : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_left 1 n
      nlinarith
    exact mul_nonneg (Real.log_nonneg hmX) (by
      unfold selbergGaussianHarmonic
      positivity)
  · intro n
    simpa only [L] using selbergGaussianLogHarmonic_le_majorant ha0 hX n

theorem tsum_selbergGaussianLogHarmonic_le
    {a X : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hX : 1 ≤ X) :
    (∑' n : ℕ, selbergGaussianLogHarmonic a X n) ≤
      (Real.log X + Real.log (1 / a)) * Real.log (2 / a) + 2 := by
  let L : ℝ := Real.log X + Real.log (1 / a)
  have hL0 : 0 ≤ L := by
    have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
    have hinv : 1 ≤ 1 / a := (le_div_iff₀ ha0).2 (by simpa using ha1)
    have hlogInv : 0 ≤ Real.log (1 / a) := Real.log_nonneg hinv
    dsimp [L]
    positivity
  have hmajor : Summable (fun n : ℕ =>
      L * selbergGaussianHarmonic a n + a * selbergGaussianMass a n) :=
    (summable_selbergGaussianHarmonic ha0).mul_left L |>.add
      ((summable_selbergGaussianMass ha0).mul_left a)
  calc
    (∑' n : ℕ, selbergGaussianLogHarmonic a X n) ≤
        ∑' n : ℕ, (L * selbergGaussianHarmonic a n +
          a * selbergGaussianMass a n) :=
      (summable_selbergGaussianLogHarmonic ha0 ha1 hX).tsum_le_tsum
        (fun n => by simpa only [L] using
          selbergGaussianLogHarmonic_le_majorant ha0 hX n) hmajor
    _ = L * (∑' n : ℕ, selbergGaussianHarmonic a n) +
        a * (∑' n : ℕ, selbergGaussianMass a n) := by
      rw [(summable_selbergGaussianHarmonic ha0 |>.mul_left L).tsum_add
        (summable_selbergGaussianMass ha0 |>.mul_left a),
        tsum_mul_left, tsum_mul_left]
    _ ≤ L * Real.log (2 / a) + 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (tsum_selbergGaussianHarmonic_le_log ha0 ha1) hL0)
        (mul_tsum_selbergGaussianMass_le_two ha0 ha1)
    _ = (Real.log X + Real.log (1 / a)) * Real.log (2 / a) + 2 := rfl

theorem summable_selbergOffDiagonalDampedBracket
    {a X d : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hX : 1 ≤ X) :
    Summable (selbergOffDiagonalDampedBracket a X d) := by
  exact (summable_selbergGaussianHarmonic ha0).add
    ((summable_selbergGaussianLogHarmonic ha0 ha1 hX).mul_left d⁻¹)

theorem tsum_selbergOffDiagonalDampedBracket_le
    {a X d : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hX : 1 ≤ X) (hd0 : 0 < d) :
    (∑' n : ℕ, selbergOffDiagonalDampedBracket a X d n) ≤
      Real.log (2 / a) + d⁻¹ *
        ((Real.log X + Real.log (1 / a)) * Real.log (2 / a) + 2) := by
  unfold selbergOffDiagonalDampedBracket
  rw [(summable_selbergGaussianHarmonic ha0).tsum_add
      ((summable_selbergGaussianLogHarmonic ha0 ha1 hX).mul_left d⁻¹),
    tsum_mul_left]
  exact add_le_add
    (tsum_selbergGaussianHarmonic_le_log ha0 ha1)
    (mul_le_mul_of_nonneg_left
      (tsum_selbergGaussianLogHarmonic_le ha0 ha1 hX)
      (inv_nonneg.mpr hd0.le))

private theorem selbergGaussianHarmonic_mono_parameter
    {a b : ℝ} (_hb0 : 0 < b) (hba : b ≤ a) (n : ℕ) :
    selbergGaussianHarmonic a n ≤ selbergGaussianHarmonic b n := by
  unfold selbergGaussianHarmonic
  apply div_le_div_of_nonneg_right
  · apply Real.exp_le_exp.mpr
    have hsq : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ 2) := sq_nonneg _
    nlinarith
  · positivity

private theorem selbergGaussianLogHarmonic_mono_parameter
    {a b X : ℝ} (hb0 : 0 < b) (hba : b ≤ a) (hX : 1 ≤ X) (n : ℕ) :
    selbergGaussianLogHarmonic a X n ≤
      selbergGaussianLogHarmonic b X n := by
  unfold selbergGaussianLogHarmonic
  have hm : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left 1 n
  have hlog : 0 ≤ Real.log (((n + 1 : ℕ) : ℝ) * X) := by
    apply Real.log_nonneg
    nlinarith
  exact mul_le_mul_of_nonneg_left
    (selbergGaussianHarmonic_mono_parameter hb0 hba n) hlog

theorem tsum_selbergGaussianHarmonic_le_log_capped
    {a : ℝ} (ha0 : 0 < a) :
    (∑' n : ℕ, selbergGaussianHarmonic a n) ≤
      Real.log (2 / selbergCappedGaussianParameter a) := by
  let b := selbergCappedGaussianParameter a
  have hb0 : 0 < b := by
    dsimp [b, selbergCappedGaussianParameter]
    exact lt_min ha0 zero_lt_one
  have hb1 : b ≤ 1 := by
    dsimp [b, selbergCappedGaussianParameter]
    exact min_le_right _ _
  have hba : b ≤ a := by
    dsimp [b, selbergCappedGaussianParameter]
    exact min_le_left _ _
  have hsumA : Summable (selbergGaussianHarmonic a) :=
    summable_selbergGaussianHarmonic ha0
  have hsumB : Summable (selbergGaussianHarmonic b) :=
    summable_selbergGaussianHarmonic hb0
  calc
    (∑' n : ℕ, selbergGaussianHarmonic a n) ≤
        ∑' n : ℕ, selbergGaussianHarmonic b n :=
      hsumA.tsum_le_tsum
        (selbergGaussianHarmonic_mono_parameter hb0 hba) hsumB
    _ ≤ Real.log (2 / b) := tsum_selbergGaussianHarmonic_le_log hb0 hb1
    _ = Real.log (2 / selbergCappedGaussianParameter a) := rfl

theorem summable_selbergGaussianLogHarmonic_of_pos
    {a X : ℝ} (ha0 : 0 < a) (hX : 1 ≤ X) :
    Summable (selbergGaussianLogHarmonic a X) := by
  let b := selbergCappedGaussianParameter a
  have hb0 : 0 < b := by
    dsimp [b, selbergCappedGaussianParameter]
    exact lt_min ha0 zero_lt_one
  have hb1 : b ≤ 1 := by
    dsimp [b, selbergCappedGaussianParameter]
    exact min_le_right _ _
  have hba : b ≤ a := by
    dsimp [b, selbergCappedGaussianParameter]
    exact min_le_left _ _
  refine Summable.of_nonneg_of_le ?_ ?_
    (summable_selbergGaussianLogHarmonic hb0 hb1 hX)
  · intro n
    unfold selbergGaussianLogHarmonic
    have hm : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left 1 n
    exact mul_nonneg (Real.log_nonneg (by nlinarith)) (by
      unfold selbergGaussianHarmonic
      positivity)
  · intro n
    exact selbergGaussianLogHarmonic_mono_parameter hb0 hba hX n

theorem summable_selbergOffDiagonalDampedBracket_of_pos
    {a X d : ℝ} (ha0 : 0 < a) (hX : 1 ≤ X) :
    Summable (selbergOffDiagonalDampedBracket a X d) := by
  exact (summable_selbergGaussianHarmonic ha0).add
    ((summable_selbergGaussianLogHarmonic_of_pos ha0 hX).mul_left d⁻¹)

theorem tsum_selbergGaussianLogHarmonic_le_capped
    {a X : ℝ} (ha0 : 0 < a) (hX : 1 ≤ X) :
    (∑' n : ℕ, selbergGaussianLogHarmonic a X n) ≤
      (Real.log X + Real.log (1 / selbergCappedGaussianParameter a)) *
        Real.log (2 / selbergCappedGaussianParameter a) + 2 := by
  let b := selbergCappedGaussianParameter a
  have hb0 : 0 < b := by
    dsimp [b, selbergCappedGaussianParameter]
    exact lt_min ha0 zero_lt_one
  have hb1 : b ≤ 1 := by
    dsimp [b, selbergCappedGaussianParameter]
    exact min_le_right _ _
  have hba : b ≤ a := by
    dsimp [b, selbergCappedGaussianParameter]
    exact min_le_left _ _
  have hsumA : Summable (selbergGaussianLogHarmonic a X) :=
    summable_selbergGaussianLogHarmonic_of_pos ha0 hX
  have hsumB := summable_selbergGaussianLogHarmonic hb0 hb1 hX
  calc
    (∑' n : ℕ, selbergGaussianLogHarmonic a X n) ≤
        ∑' n : ℕ, selbergGaussianLogHarmonic b X n :=
      hsumA.tsum_le_tsum
        (selbergGaussianLogHarmonic_mono_parameter hb0 hba hX) hsumB
    _ ≤ (Real.log X + Real.log (1 / b)) * Real.log (2 / b) + 2 :=
      tsum_selbergGaussianLogHarmonic_le hb0 hb1 hX
    _ = (Real.log X + Real.log (1 / selbergCappedGaussianParameter a)) *
        Real.log (2 / selbergCappedGaussianParameter a) + 2 := rfl

end HardyTheorem
