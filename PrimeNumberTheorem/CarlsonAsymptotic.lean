import PrimeNumberTheorem.CarlsonHorizontalContour

open Complex Set Filter Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Carlson's optimized mollifier length, rounded down and clamped away from
zero so that all finite Dirichlet-polynomial estimates apply uniformly. -/
noncomputable def carlsonMollifierLength (sigma T : ℝ) : ℕ :=
  max 1 (Nat.floor (T ^ (2 * sigma - 1)))

theorem one_le_carlsonMollifierLength (sigma T : ℝ) :
    1 ≤ carlsonMollifierLength sigma T := by
  simp [carlsonMollifierLength]

/-- Rounding Carlson's real-valued optimal length down changes it by at most
a factor of two once the target length is at least one. -/
theorem carlsonMollifierLength_bounds {sigma T : ℝ}
    (hpower : 1 ≤ T ^ (2 * sigma - 1)) :
    T ^ (2 * sigma - 1) / 2 ≤ (carlsonMollifierLength sigma T : ℝ) ∧
      (carlsonMollifierLength sigma T : ℝ) ≤ T ^ (2 * sigma - 1) := by
  let Y : ℝ := T ^ (2 * sigma - 1)
  have hY0 : 0 ≤ Y := zero_le_one.trans hpower
  have hfloorOne : 1 ≤ Nat.floor Y := (Nat.one_le_floor_iff Y).2 hpower
  have hlength : carlsonMollifierLength sigma T = Nat.floor Y := by
    simp [carlsonMollifierLength, Y, max_eq_right hfloorOne]
  have hfloorUpper : ((Nat.floor Y : ℕ) : ℝ) ≤ Y := Nat.floor_le hY0
  have hYlt : Y < ((Nat.floor Y : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one Y
  have hfloorOneReal : (1 : ℝ) ≤ (Nat.floor Y : ℕ) := by
    exact_mod_cast hfloorOne
  rw [hlength]
  constructor
  · linarith
  · exact hfloorUpper

/-- Moving a real exponent by `b - a` costs at most `exp C` whenever the
corresponding logarithmic displacement is at most `C`. -/
theorem rpow_le_exp_mul_rpow_of_exponent_gap {T a b C : ℝ}
    (hT : 0 < T) (hgap : (b - a) * Real.log T ≤ C) :
    T ^ b ≤ Real.exp C * T ^ a := by
  rw [Real.rpow_def_of_pos hT, Real.rpow_def_of_pos hT, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The lower-endpoint mean-square term has Carlson's exponent after the
choice `X = T^(2 sigma - 1)`. -/
theorem carlson_lower_endpoint_exponent (sigma : ℝ) :
    1 + (2 * sigma - 1) * (1 - 2 * sigma) =
      4 * sigma * (1 - sigma) := by
  ring

/-- The upper-endpoint mean-square term has the same optimized exponent. -/
theorem carlson_upper_endpoint_exponent (sigma : ℝ) :
    (1 + (2 * sigma - 1)) * (2 - 2 * sigma) =
      4 * sigma * (1 - sigma) := by
  ring

/-- Replacing the selected auxiliary line by the target line in the lower
mean-square exponent costs at most the fixed factor `exp 4`. -/
theorem carlson_lower_endpoint_rpow_le {sigma x0 T : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hT : 0 < T) (hlog : 0 < Real.log T)
    (hx0 : x0 < sigma) (hgap : sigma - x0 < 2 / Real.log T) :
    T ^ (1 + (2 * sigma - 1) * (1 - 2 * x0)) ≤
      Real.exp 4 * T ^ (4 * sigma * (1 - sigma)) := by
  apply rpow_le_exp_mul_rpow_of_exponent_gap hT
  have hgapLog : (sigma - x0) * Real.log T ≤ 2 :=
    ((lt_div_iff₀ hlog).mp hgap).le
  have hgapLog0 : 0 ≤ (sigma - x0) * Real.log T :=
    mul_nonneg (sub_nonneg.mpr hx0.le) hlog.le
  have hfactor0 : 0 ≤ 2 * sigma - 1 := by linarith
  have hfactor1 : 2 * sigma - 1 ≤ 1 := by linarith
  have hproduct :
      (2 * sigma - 1) * ((sigma - x0) * Real.log T) ≤ 2 := by
    nlinarith [mul_le_mul hfactor1 hgapLog hgapLog0 (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← carlson_lower_endpoint_exponent sigma]
  nlinarith

/-- The corresponding upper mean-square exponent costs at most `exp 8`. -/
theorem carlson_upper_endpoint_rpow_le {sigma x0 T : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hT : 0 < T) (hlog : 0 < Real.log T)
    (hx0 : x0 < sigma) (hgap : sigma - x0 < 2 / Real.log T) :
    T ^ ((1 + (2 * sigma - 1)) * (2 - 2 * x0)) ≤
      Real.exp 8 * T ^ (4 * sigma * (1 - sigma)) := by
  apply rpow_le_exp_mul_rpow_of_exponent_gap hT
  have hgapLog : (sigma - x0) * Real.log T ≤ 2 :=
    ((lt_div_iff₀ hlog).mp hgap).le
  have hgapLog0 : 0 ≤ (sigma - x0) * Real.log T :=
    mul_nonneg (sub_nonneg.mpr hx0.le) hlog.le
  have hsigma0 : 0 ≤ sigma := by linarith
  have hproduct : sigma * ((sigma - x0) * Real.log T) ≤ 2 := by
    nlinarith [mul_le_mul hsigmaOne.le hgapLog hgapLog0
      (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← carlson_upper_endpoint_exponent sigma]
  nlinarith

/-- A finite geometric progression with ratio greater than one is controlled
by its next term, with no factor proportional to the number of summands. -/
theorem sum_range_pow_le_pow_div_sub_one {r : ℝ} (hr : 1 < r) (n : ℕ) :
    (∑ k ∈ Finset.range n, r ^ k) ≤ r ^ n / (r - 1) := by
  induction n with
  | zero =>
      simp [hr.le]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ k ∈ Finset.range n, r ^ k) + r ^ n ≤
            r ^ n / (r - 1) + r ^ n := add_le_add ih le_rfl
        _ = r ^ (n + 1) / (r - 1) := by
          rw [pow_succ]
          field_simp [ne_of_gt (sub_pos.mpr hr)]
          ring

/-- Positive real powers along a dyadic cover form a genuine geometric
progression, so their sum has no extra logarithmic loss. -/
theorem sum_dyadic_rpow_le {q : ℝ} (hq : 0 < q) (n : ℕ) :
    (∑ k ∈ Finset.range n, ((2 : ℝ) ^ k) ^ q) ≤
      ((2 : ℝ) ^ n) ^ q / ((2 : ℝ) ^ q - 1) := by
  have h := sum_range_pow_le_pow_div_sub_one
    (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hq) n
  simpa only [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)] using h

/-- Scaled dyadic powers are likewise controlled by the final scale. -/
theorem sum_scaled_dyadic_rpow_le {u q : ℝ} (hu : 0 ≤ u)
    (hq : 0 < q) (n : ℕ) :
    (∑ k ∈ Finset.range n, (u * (2 : ℝ) ^ k) ^ q) ≤
      u ^ q * (((2 : ℝ) ^ n) ^ q / ((2 : ℝ) ^ q - 1)) := by
  calc
    (∑ k ∈ Finset.range n, (u * (2 : ℝ) ^ k) ^ q) =
        ∑ k ∈ Finset.range n, u ^ q * (((2 : ℝ) ^ k) ^ q) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Real.mul_rpow hu (pow_nonneg (by norm_num) k)]
    _ = u ^ q * (∑ k ∈ Finset.range n, ((2 : ℝ) ^ k) ^ q) := by
      rw [Finset.mul_sum]
    _ ≤ u ^ q * (((2 : ℝ) ^ n) ^ q / ((2 : ℝ) ^ q - 1)) :=
      mul_le_mul_of_nonneg_left (sum_dyadic_rpow_le hq n)
        (Real.rpow_nonneg hu q)

/-- Negative dyadic powers are controlled by the first scale. -/
theorem sum_dyadic_rpow_le_of_neg {q : ℝ} (hq : q < 0) (n : ℕ) :
    (∑ k ∈ Finset.range n, ((2 : ℝ) ^ k) ^ q) ≤
      (1 - (2 : ℝ) ^ q)⁻¹ := by
  have hrPos : 0 < (2 : ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) q
  have hrOne : (2 : ℝ) ^ q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hq
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hrPos.le hrOne
  simpa only [Nat.Ico_zero_eq_range, pow_zero, Real.one_rpow, one_div,
    Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)] using h

/-- Scaled negative dyadic powers have the same first-scale bound. -/
theorem sum_scaled_dyadic_rpow_le_of_neg {u q : ℝ} (hu : 0 < u)
    (hq : q < 0) (n : ℕ) :
    (∑ k ∈ Finset.range n, (u * (2 : ℝ) ^ k) ^ q) ≤
      u ^ q * (1 - (2 : ℝ) ^ q)⁻¹ := by
  calc
    (∑ k ∈ Finset.range n, (u * (2 : ℝ) ^ k) ^ q) =
        ∑ k ∈ Finset.range n, u ^ q * (((2 : ℝ) ^ k) ^ q) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Real.mul_rpow hu.le (pow_nonneg (by norm_num) k)]
    _ = u ^ q * (∑ k ∈ Finset.range n, ((2 : ℝ) ^ k) ^ q) := by
      rw [Finset.mul_sum]
    _ ≤ u ^ q * (1 - (2 : ℝ) ^ q)⁻¹ :=
      mul_le_mul_of_nonneg_left (sum_dyadic_rpow_le_of_neg hq n)
        (Real.rpow_nonneg hu.le q)

/-- The negative-power cutoff in a sharp Carlson endpoint is bounded without
locating the exact dyadic interval where the height crosses the mollifier
length.  The first term handles scales below `X`; the second handles scales
above `X`. -/
theorem carlson_min_scale_negative_power_le {X : ℕ} {u x0 : ℝ}
    (hX : 1 ≤ X) (hu : 1 ≤ u) (hx0 : 1 / 2 < x0) :
    u * (((min X (Nat.floor (4 * u)) + 1 : ℕ) : ℝ) ^ (1 - 2 * x0)) ≤
      u ^ (2 - 2 * x0) + u * (X : ℝ) ^ (1 - 2 * x0) := by
  have huPos : 0 < u := zero_lt_one.trans_le hu
  have hXPos : 0 < (X : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hX)
  have hp : 1 - 2 * x0 < 0 := by linarith
  by_cases hcut : X ≤ Nat.floor (4 * u)
  · rw [Nat.min_eq_left hcut]
    have hbase : (X : ℝ) ≤ ((X + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ X
    have hpow : (((X + 1 : ℕ) : ℝ) ^ (1 - 2 * x0)) ≤
        (X : ℝ) ^ (1 - 2 * x0) :=
      Real.rpow_le_rpow_of_nonpos hXPos hbase hp.le
    calc
      u * (((X + 1 : ℕ) : ℝ) ^ (1 - 2 * x0)) ≤
          u * (X : ℝ) ^ (1 - 2 * x0) :=
        mul_le_mul_of_nonneg_left hpow huPos.le
      _ ≤ u ^ (2 - 2 * x0) + u * (X : ℝ) ^ (1 - 2 * x0) :=
        le_add_of_nonneg_left (Real.rpow_nonneg huPos.le _)
  · have hfloorLe : Nat.floor (4 * u) ≤ X := (Nat.le_of_lt (lt_of_not_ge hcut))
    rw [Nat.min_eq_right hfloorLe]
    have hfour : 4 * u < ((Nat.floor (4 * u) + 1 : ℕ) : ℝ) := by
      simpa using Nat.lt_floor_add_one (4 * u)
    have huBase : u ≤ ((Nat.floor (4 * u) + 1 : ℕ) : ℝ) := by
      linarith
    have hpow :
        (((Nat.floor (4 * u) + 1 : ℕ) : ℝ) ^ (1 - 2 * x0)) ≤
          u ^ (1 - 2 * x0) :=
      Real.rpow_le_rpow_of_nonpos huPos huBase hp.le
    calc
      u * (((Nat.floor (4 * u) + 1 : ℕ) : ℝ) ^ (1 - 2 * x0)) ≤
          u * u ^ (1 - 2 * x0) :=
        mul_le_mul_of_nonneg_left hpow huPos.le
      _ = u ^ (2 - 2 * x0) := by
        calc
          u * u ^ (1 - 2 * x0) = u ^ (1 + (1 - 2 * x0)) := by
            rw [Real.rpow_add huPos, Real.rpow_one]
          _ = u ^ (2 - 2 * x0) := by ring_nf
      _ ≤ u ^ (2 - 2 * x0) + u * (X : ℝ) ^ (1 - 2 * x0) :=
        le_add_of_nonneg_right
          (mul_nonneg huPos.le (Real.rpow_nonneg (Nat.cast_nonneg X) _))

/-- Summing the sharp cutoff term over a dyadic prefix costs only the final
positive scale and the total length of the cover.  In particular, no factor
proportional to the number of dyadic intervals appears. -/
theorem sum_carlson_min_scale_negative_power_le {X n : ℕ} {u x0 : ℝ}
    (hX : 1 ≤ X) (hu : 1 ≤ u) (hx0 : 1 / 2 < x0) (hx0One : x0 < 1) :
    (∑ k ∈ Finset.range n,
      (u * (2 : ℝ) ^ k) *
        (((min X (Nat.floor (4 * (u * (2 : ℝ) ^ k))) + 1 : ℕ) : ℝ) ^
          (1 - 2 * x0))) ≤
      u ^ (2 - 2 * x0) *
          (((2 : ℝ) ^ n) ^ (2 - 2 * x0) /
            ((2 : ℝ) ^ (2 - 2 * x0) - 1)) +
        (X : ℝ) ^ (1 - 2 * x0) * (u * (2 : ℝ) ^ n) := by
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hq : 0 < 2 - 2 * x0 := by linarith
  have hpoint : ∀ k ∈ Finset.range n,
      (u * (2 : ℝ) ^ k) *
          (((min X (Nat.floor (4 * (u * (2 : ℝ) ^ k))) + 1 : ℕ) : ℝ) ^
            (1 - 2 * x0)) ≤
        (u * (2 : ℝ) ^ k) ^ (2 - 2 * x0) +
          (u * (2 : ℝ) ^ k) * (X : ℝ) ^ (1 - 2 * x0) := by
    intro k _hk
    apply carlson_min_scale_negative_power_le hX
    · exact one_le_mul_of_one_le_of_one_le hu (one_le_pow₀ (by norm_num))
    · exact hx0
  have hsumPoint := Finset.sum_le_sum hpoint
  have hpositive := sum_scaled_dyadic_rpow_le hu0 hq n
  have hlinear :
      (∑ k ∈ Finset.range n, u * (2 : ℝ) ^ k) ≤ u * (2 : ℝ) ^ n := by
    have h := sum_scaled_dyadic_rpow_le hu0 (by norm_num : (0 : ℝ) < 1) n
    calc
      (∑ k ∈ Finset.range n, u * (2 : ℝ) ^ k) ≤
          u ^ (1 : ℝ) *
            (((2 : ℝ) ^ n) ^ (1 : ℝ) /
              ((2 : ℝ) ^ (1 : ℝ) - 1)) := by
        simpa only [Real.rpow_one] using h
      _ = u * (2 : ℝ) ^ n := by norm_num [Real.rpow_one]
  calc
    (∑ k ∈ Finset.range n,
      (u * (2 : ℝ) ^ k) *
        (((min X (Nat.floor (4 * (u * (2 : ℝ) ^ k))) + 1 : ℕ) : ℝ) ^
          (1 - 2 * x0))) ≤
        ∑ k ∈ Finset.range n,
          ((u * (2 : ℝ) ^ k) ^ (2 - 2 * x0) +
            (u * (2 : ℝ) ^ k) * (X : ℝ) ^ (1 - 2 * x0)) := hsumPoint
    _ = (∑ k ∈ Finset.range n, (u * (2 : ℝ) ^ k) ^ (2 - 2 * x0)) +
          (X : ℝ) ^ (1 - 2 * x0) *
            (∑ k ∈ Finset.range n, u * (2 : ℝ) ^ k) := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ ≤ u ^ (2 - 2 * x0) *
          (((2 : ℝ) ^ n) ^ (2 - 2 * x0) /
            ((2 : ℝ) ^ (2 - 2 * x0) - 1)) +
        (X : ℝ) ^ (1 - 2 * x0) * (u * (2 : ℝ) ^ n) :=
      add_le_add hpositive
        (mul_le_mul_of_nonneg_left hlinear
          (Real.rpow_nonneg (Nat.cast_nonneg X) _))

/-- Replacing the floor in Carlson's upper endpoint by its real scale only
increases a nonnegative power. -/
theorem carlson_floor_product_rpow_le {X : ℕ} {u q : ℝ}
    (hu : 0 ≤ u) (hq : 0 ≤ q) :
    ((((Nat.floor (4 * u)) * X : ℕ) : ℝ) ^ q) ≤
      (4 * u * (X : ℝ)) ^ q := by
  have hfloor : ((Nat.floor (4 * u) : ℕ) : ℝ) ≤ 4 * u :=
    Nat.floor_le (mul_nonneg (by norm_num) hu)
  have hproduct : (((Nat.floor (4 * u)) * X : ℕ) : ℝ) ≤
      4 * u * (X : ℝ) := by
    push_cast
    exact mul_le_mul_of_nonneg_right hfloor (Nat.cast_nonneg X)
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) hproduct hq

/-- The upper sharp endpoint terms also form a positive geometric series
after removing the floor. -/
theorem sum_carlson_floor_product_rpow_le {X n : ℕ} {u q : ℝ}
    (hu : 0 ≤ u) (hq : 0 < q) :
    (∑ k ∈ Finset.range n,
      ((((Nat.floor (4 * (u * (2 : ℝ) ^ k))) * X : ℕ) : ℝ) ^ q)) ≤
      (4 * u * (X : ℝ)) ^ q *
        (((2 : ℝ) ^ n) ^ q / ((2 : ℝ) ^ q - 1)) := by
  have hbase0 : 0 ≤ 4 * u * (X : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) hu) (Nat.cast_nonneg X)
  calc
    (∑ k ∈ Finset.range n,
      ((((Nat.floor (4 * (u * (2 : ℝ) ^ k))) * X : ℕ) : ℝ) ^ q)) ≤
        ∑ k ∈ Finset.range n,
          (4 * (u * (2 : ℝ) ^ k) * (X : ℝ)) ^ q := by
      apply Finset.sum_le_sum
      intro k _hk
      exact carlson_floor_product_rpow_le
        (mul_nonneg hu (pow_nonneg (by norm_num) k)) hq.le
    _ = ∑ k ∈ Finset.range n,
          ((4 * u * (X : ℝ)) * (2 : ℝ) ^ k) ^ q := by
      apply Finset.sum_congr rfl
      intro k _hk
      congr 1
      ring
    _ ≤ (4 * u * (X : ℝ)) ^ q *
          (((2 : ℝ) ^ n) ^ q / ((2 : ℝ) ^ q - 1)) :=
      sum_scaled_dyadic_rpow_le hbase0 hq n

/-- The canonical-remainder contribution on a doubling interval decays like
`a^(1 - 2 x0)`.  The additive `4π` in the interval estimate is absorbed
using `a ≥ 1`. -/
theorem carlson_remainder_scale_le {A a x0 : ℝ} (ha : 1 ≤ a) :
    (((A + 4) * (4 * a) ^ (-x0)) ^ 2) * (a + 4 * Real.pi) ≤
      (A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
        (1 + 4 * Real.pi) * a ^ (1 - 2 * x0) := by
  have haPos : 0 < a := zero_lt_one.trans_le ha
  have hfoura0 : 0 ≤ 4 * a := mul_nonneg (by norm_num) haPos.le
  have hscaleSquare :
      ((4 * a) ^ (-x0)) ^ 2 =
        (4 : ℝ) ^ (-2 * x0) * a ^ (-2 * x0) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hfoura0,
      Real.mul_rpow (by norm_num) haPos.le]
    congr 2 <;> ring
  have hlinear : a + 4 * Real.pi ≤ (1 + 4 * Real.pi) * a := by
    have hpi : 0 ≤ Real.pi := Real.pi_pos.le
    nlinarith
  have hcombine : a ^ (-2 * x0) * a = a ^ (1 - 2 * x0) := by
    calc
      a ^ (-2 * x0) * a = a ^ (-2 * x0) * a ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = a ^ (-2 * x0 + 1) := by rw [← Real.rpow_add haPos]
      _ = a ^ (1 - 2 * x0) := by ring_nf
  rw [mul_pow, hscaleSquare]
  calc
    ((A + 4) ^ 2 * ((4 : ℝ) ^ (-2 * x0) * a ^ (-2 * x0))) *
        (a + 4 * Real.pi) ≤
      ((A + 4) ^ 2 * ((4 : ℝ) ^ (-2 * x0) * a ^ (-2 * x0))) *
        ((1 + 4 * Real.pi) * a) :=
      mul_le_mul_of_nonneg_left hlinear
        (mul_nonneg (sq_nonneg _) (mul_nonneg
          (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg haPos.le _)))
    _ = (A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
        (1 + 4 * Real.pi) * a ^ (1 - 2 * x0) := by
      rw [← hcombine]
      ring

/-- The canonical-remainder scales are summable over a dyadic prefix because
`1 - 2 x0 < 0`. -/
theorem sum_carlson_remainder_scale_le {n : ℕ} {A u x0 : ℝ}
    (hu : 1 ≤ u) (hx0 : 1 / 2 < x0) :
    (∑ k ∈ Finset.range n,
      (((A + 4) * (4 * (u * (2 : ℝ) ^ k)) ^ (-x0)) ^ 2) *
        ((u * (2 : ℝ) ^ k) + 4 * Real.pi)) ≤
      (A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
        (1 + 4 * Real.pi) *
          (u ^ (1 - 2 * x0) *
            (1 - (2 : ℝ) ^ (1 - 2 * x0))⁻¹) := by
  let C : ℝ := (A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
    (1 + 4 * Real.pi)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hp : 1 - 2 * x0 < 0 := by linarith
  have hpoint : ∀ k ∈ Finset.range n,
      (((A + 4) * (4 * (u * (2 : ℝ) ^ k)) ^ (-x0)) ^ 2) *
          ((u * (2 : ℝ) ^ k) + 4 * Real.pi) ≤
        C * (u * (2 : ℝ) ^ k) ^ (1 - 2 * x0) := by
    intro k _hk
    simpa [C, mul_assoc] using
      (carlson_remainder_scale_le (A := A) (x0 := x0)
        (one_le_mul_of_one_le_of_one_le hu (one_le_pow₀ (by norm_num))))
  calc
    (∑ k ∈ Finset.range n,
      (((A + 4) * (4 * (u * (2 : ℝ) ^ k)) ^ (-x0)) ^ 2) *
        ((u * (2 : ℝ) ^ k) + 4 * Real.pi)) ≤
        ∑ k ∈ Finset.range n,
          C * (u * (2 : ℝ) ^ k) ^ (1 - 2 * x0) :=
      Finset.sum_le_sum hpoint
    _ = C * (∑ k ∈ Finset.range n,
          (u * (2 : ℝ) ^ k) ^ (1 - 2 * x0)) := by
      rw [Finset.mul_sum]
    _ ≤ C * (u ^ (1 - 2 * x0) *
          (1 - (2 : ℝ) ^ (1 - 2 * x0))⁻¹) :=
      mul_le_mul_of_nonneg_left
        (sum_scaled_dyadic_rpow_le_of_neg
          (zero_lt_one.trans_le hu) hp n) hC
    _ = (A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
        (1 + 4 * Real.pi) *
          (u ^ (1 - 2 * x0) *
            (1 - (2 : ℝ) ^ (1 - 2 * x0))⁻¹) := by
      rfl

/-- A dyadic-interval majorant for the arithmetic sharp endpoint.  Its three
summands are arranged so that the geometric-series lemmas above apply
directly. -/
noncomputable def carlsonSharpEndpointDyadicMajorant
    (A L : ℝ) (X : ℕ) (x0 a : ℝ) : ℝ :=
  2 * (L * (2 + 1 / (2 * x0 - 1)) *
        (a * (((min X (Nat.floor (4 * a)) + 1 : ℕ) : ℝ) ^ (1 - 2 * x0))) +
      8 * Real.pi * L * (2 + 1 / (2 - 2 * x0)) *
        (4 * a * (X : ℝ)) ^ (2 - 2 * x0)) +
    4 * ((A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
        (1 + 4 * Real.pi) * a ^ (1 - 2 * x0)) *
      (1 + (X : ℝ) ^ (2 - 2 * x0) / (2 - 2 * x0))

/-- On a doubling interval, the explicit sharp endpoint is bounded by the
dyadic majorant once its logarithmic factor is bounded by `L`. -/
theorem carlsonLogNormSharpEndpointExplicit_le_dyadicMajorant
    {A L x0 a b : ℝ} {X : ℕ}
    (hX : 1 ≤ X) (ha : 1 ≤ a) (hab : a ≤ b) (hba : b ≤ 2 * a)
    (hx0 : 1 / 2 < x0) (hx0One : x0 < 1) (hL : 0 ≤ L)
    (hlog : (1 + Real.log (Nat.floor (4 * a) * X)) ^ 3 ≤ L) :
    carlsonLogNormSharpEndpointExplicit A 4 X x0 a b (4 * a) ≤
      carlsonSharpEndpointDyadicMajorant A L X x0 a := by
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hlen0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hlen : b - a ≤ a := by linarith
  have hfloorFour : 4 ≤ Nat.floor (4 * a) := by
    exact Nat.le_floor (show (4 : ℝ) ≤ 4 * a by linarith)
  have hproductOne : 1 ≤ Nat.floor (4 * a) * X := by
    nlinarith
  have hproductOneReal : (1 : ℝ) ≤
      (Nat.floor (4 * a) : ℝ) * (X : ℝ) := by
    exact_mod_cast hproductOne
  have hlogBase : 0 ≤ 1 + Real.log (Nat.floor (4 * a) * X) :=
    add_nonneg (by norm_num) (Real.log_nonneg hproductOneReal)
  have hlog0 : 0 ≤ (1 + Real.log (Nat.floor (4 * a) * X)) ^ 3 :=
    pow_nonneg hlogBase _
  have hminusDen : 0 < 2 * x0 - 1 := by linarith
  have hplusDen : 0 < 2 - 2 * x0 := by linarith
  have hminusCoef : 0 ≤ 2 + 1 / (2 * x0 - 1) := by positivity
  have hplusCoef : 0 ≤ 2 + 1 / (2 - 2 * x0) := by positivity
  have hminPow0 : 0 ≤
      (((min X (Nat.floor (4 * a)) + 1 : ℕ) : ℝ) ^ (1 - 2 * x0)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlower :
      (b - a) * (1 + Real.log (Nat.floor (4 * a) * X)) ^ 3 *
          ((2 + 1 / (2 * x0 - 1)) *
            (((min X (Nat.floor (4 * a)) + 1 : ℕ) : ℝ) ^ (1 - 2 * x0))) ≤
        L * (2 + 1 / (2 * x0 - 1)) *
          (a * (((min X (Nat.floor (4 * a)) + 1 : ℕ) : ℝ) ^
            (1 - 2 * x0))) := by
    have hlenLog :
        (b - a) * (1 + Real.log (Nat.floor (4 * a) * X)) ^ 3 ≤ a * L :=
      mul_le_mul hlen hlog hlog0 ha0
    calc
      (b - a) * (1 + Real.log (Nat.floor (4 * a) * X)) ^ 3 *
          ((2 + 1 / (2 * x0 - 1)) *
            (((min X (Nat.floor (4 * a)) + 1 : ℕ) : ℝ) ^ (1 - 2 * x0))) ≤
        (a * L) * ((2 + 1 / (2 * x0 - 1)) *
          (((min X (Nat.floor (4 * a)) + 1 : ℕ) : ℝ) ^ (1 - 2 * x0))) :=
        mul_le_mul_of_nonneg_right hlenLog (mul_nonneg hminusCoef hminPow0)
      _ = L * (2 + 1 / (2 * x0 - 1)) *
          (a * (((min X (Nat.floor (4 * a)) + 1 : ℕ) : ℝ) ^
            (1 - 2 * x0))) := by ring
  have hfloorPow := carlson_floor_product_rpow_le
    (X := X) ha0 hplusDen.le
  have huppper :
      8 * Real.pi * (1 + Real.log (Nat.floor (4 * a) * X)) ^ 3 *
          ((2 + 1 / (2 - 2 * x0)) *
            (((Nat.floor (4 * a)) * X : ℕ) : ℝ) ^ (2 - 2 * x0)) ≤
        8 * Real.pi * L * (2 + 1 / (2 - 2 * x0)) *
          (4 * a * (X : ℝ)) ^ (2 - 2 * x0) := by
    have hcoeff : 0 ≤ 8 * Real.pi * (2 + 1 / (2 - 2 * x0)) := by positivity
    calc
      8 * Real.pi * (1 + Real.log (Nat.floor (4 * a) * X)) ^ 3 *
          ((2 + 1 / (2 - 2 * x0)) *
            (((Nat.floor (4 * a)) * X : ℕ) : ℝ) ^ (2 - 2 * x0)) =
        (8 * Real.pi * (2 + 1 / (2 - 2 * x0))) *
          ((1 + Real.log (Nat.floor (4 * a) * X)) ^ 3 *
            ((((Nat.floor (4 * a)) * X : ℕ) : ℝ) ^ (2 - 2 * x0))) := by ring
      _ ≤ (8 * Real.pi * (2 + 1 / (2 - 2 * x0))) *
          (L * (4 * a * (X : ℝ)) ^ (2 - 2 * x0)) := by
        apply mul_le_mul_of_nonneg_left _ hcoeff
        exact mul_le_mul hlog hfloorPow
          (Real.rpow_nonneg (Nat.cast_nonneg _) _) hL
      _ = 8 * Real.pi * L * (2 + 1 / (2 - 2 * x0)) *
          (4 * a * (X : ℝ)) ^ (2 - 2 * x0) := by ring
  have hbracket0 : 0 ≤
      1 + ((X : ℝ) ^ (2 - 2 * x0) - 1) / (2 - 2 * x0) := by
    have hXReal : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hpowOne : 1 ≤ (X : ℝ) ^ (2 - 2 * x0) :=
      Real.one_le_rpow hXReal hplusDen.le
    exact add_nonneg (by norm_num)
      (div_nonneg (sub_nonneg.mpr hpowOne) hplusDen.le)
  have hbracket :
      1 + ((X : ℝ) ^ (2 - 2 * x0) - 1) / (2 - 2 * x0) ≤
        1 + (X : ℝ) ^ (2 - 2 * x0) / (2 - 2 * x0) := by
    have hdiv := (div_le_div_iff_of_pos_right hplusDen).2
      (show (X : ℝ) ^ (2 - 2 * x0) - 1 ≤
        (X : ℝ) ^ (2 - 2 * x0) by linarith)
    linarith
  have hremScale :
      (((A + 4) * (4 * a) ^ (-x0)) ^ 2) * ((b - a) + 4 * Real.pi) ≤
        (A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
          (1 + 4 * Real.pi) * a ^ (1 - 2 * x0) := by
    calc
      (((A + 4) * (4 * a) ^ (-x0)) ^ 2) * ((b - a) + 4 * Real.pi) ≤
          (((A + 4) * (4 * a) ^ (-x0)) ^ 2) * (a + 4 * Real.pi) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      _ ≤ _ := carlson_remainder_scale_le ha
  have hremRhs0 : 0 ≤
      (A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
        (1 + 4 * Real.pi) * a ^ (1 - 2 * x0) := by positivity
  have hrem :
      2 * (((((A + 4) * (4 * a) ^ (-x0)) ^ 2)) *
          (((b - a) + 4 * Real.pi) *
            (2 * (1 + ((X : ℝ) ^ (2 - 2 * x0) - 1) /
              (2 - 2 * x0))))) ≤
        4 * ((A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
          (1 + 4 * Real.pi) * a ^ (1 - 2 * x0)) *
            (1 + (X : ℝ) ^ (2 - 2 * x0) / (2 - 2 * x0)) := by
    have hproduct := mul_le_mul hremScale hbracket hbracket0 hremRhs0
    nlinarith
  unfold carlsonLogNormSharpEndpointExplicit carlsonSharpEndpointDyadicMajorant
  nlinarith

/-- Closed-form majorant for a finite dyadic sum of sharp endpoints. -/
noncomputable def carlsonSharpDyadicSumMajorant
    (A L : ℝ) (X : ℕ) (x0 u : ℝ) (n : ℕ) : ℝ :=
  (2 * L * (2 + 1 / (2 * x0 - 1))) *
      (u ^ (2 - 2 * x0) *
          (((2 : ℝ) ^ n) ^ (2 - 2 * x0) /
            ((2 : ℝ) ^ (2 - 2 * x0) - 1)) +
        (X : ℝ) ^ (1 - 2 * x0) * (u * (2 : ℝ) ^ n)) +
    (16 * Real.pi * L * (2 + 1 / (2 - 2 * x0))) *
      ((4 * u * (X : ℝ)) ^ (2 - 2 * x0) *
        (((2 : ℝ) ^ n) ^ (2 - 2 * x0) /
          ((2 : ℝ) ^ (2 - 2 * x0) - 1))) +
    (4 * ((A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
        (1 + 4 * Real.pi)) *
      (1 + (X : ℝ) ^ (2 - 2 * x0) / (2 - 2 * x0))) *
        (u ^ (1 - 2 * x0) *
          (1 - (2 : ℝ) ^ (1 - 2 * x0))⁻¹)

/-- Summing the dyadic endpoint majorants introduces no interval-count loss. -/
theorem sum_carlsonSharpEndpointDyadicMajorant_le
    {A L x0 u : ℝ} {X n : ℕ}
    (hX : 1 ≤ X) (hu : 1 ≤ u) (hx0 : 1 / 2 < x0)
    (hx0One : x0 < 1) (hL : 0 ≤ L) :
    (∑ k ∈ Finset.range n,
      carlsonSharpEndpointDyadicMajorant A L X x0
        (u * (2 : ℝ) ^ k)) ≤
      carlsonSharpDyadicSumMajorant A L X x0 u n := by
  let c₁ : ℝ := 2 * L * (2 + 1 / (2 * x0 - 1))
  let c₂ : ℝ := 16 * Real.pi * L * (2 + 1 / (2 - 2 * x0))
  let c₃ : ℝ := 4 * ((A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
    (1 + 4 * Real.pi)) *
      (1 + (X : ℝ) ^ (2 - 2 * x0) / (2 - 2 * x0))
  let f₁ : ℕ → ℝ := fun k =>
    (u * (2 : ℝ) ^ k) *
      (((min X (Nat.floor (4 * (u * (2 : ℝ) ^ k))) + 1 : ℕ) : ℝ) ^
        (1 - 2 * x0))
  let f₂ : ℕ → ℝ := fun k =>
    (4 * (u * (2 : ℝ) ^ k) * (X : ℝ)) ^ (2 - 2 * x0)
  let f₃ : ℕ → ℝ := fun k => (u * (2 : ℝ) ^ k) ^ (1 - 2 * x0)
  have hminusDen : 0 < 2 * x0 - 1 := by linarith
  have hplusDen : 0 < 2 - 2 * x0 := by linarith
  have hXReal : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpow : 0 ≤ (X : ℝ) ^ (2 - 2 * x0) :=
    Real.rpow_nonneg (Nat.cast_nonneg X) _
  have hc₁ : 0 ≤ c₁ := by
    dsimp [c₁]
    exact mul_nonneg (mul_nonneg (by norm_num) hL)
      (add_nonneg (by norm_num) (one_div_nonneg.mpr hminusDen.le))
  have hc₂ : 0 ≤ c₂ := by
    dsimp [c₂]
    positivity
  have hc₃ : 0 ≤ c₃ := by
    dsimp [c₃]
    have hbracket : 0 ≤
        1 + (X : ℝ) ^ (2 - 2 * x0) / (2 - 2 * x0) :=
      add_nonneg (by norm_num) (div_nonneg hXpow hplusDen.le)
    positivity
  have h₁ := sum_carlson_min_scale_negative_power_le
    (X := X) (n := n) hX hu hx0 hx0One
  have hbase0 : 0 ≤ 4 * u * (X : ℝ) := by positivity
  have h₂ :
      (∑ k ∈ Finset.range n, f₂ k) ≤
        (4 * u * (X : ℝ)) ^ (2 - 2 * x0) *
          (((2 : ℝ) ^ n) ^ (2 - 2 * x0) /
            ((2 : ℝ) ^ (2 - 2 * x0) - 1)) := by
    calc
      (∑ k ∈ Finset.range n, f₂ k) =
          ∑ k ∈ Finset.range n,
            ((4 * u * (X : ℝ)) * (2 : ℝ) ^ k) ^ (2 - 2 * x0) := by
        apply Finset.sum_congr rfl
        intro k _hk
        dsimp [f₂]
        congr 1
        ring
      _ ≤ _ := sum_scaled_dyadic_rpow_le hbase0 hplusDen n
  have h₃ := sum_scaled_dyadic_rpow_le_of_neg
    (u := u) (q := 1 - 2 * x0) (zero_lt_one.trans_le hu)
      (by linarith) n
  change (∑ k ∈ Finset.range n,
      carlsonSharpEndpointDyadicMajorant A L X x0
        (u * (2 : ℝ) ^ k)) ≤ _
  calc
    (∑ k ∈ Finset.range n,
      carlsonSharpEndpointDyadicMajorant A L X x0
        (u * (2 : ℝ) ^ k)) =
        ∑ k ∈ Finset.range n, (c₁ * f₁ k + c₂ * f₂ k + c₃ * f₃ k) := by
      apply Finset.sum_congr rfl
      intro k _hk
      dsimp [c₁, c₂, c₃, f₁, f₂, f₃,
        carlsonSharpEndpointDyadicMajorant]
      ring
    _ = c₁ * (∑ k ∈ Finset.range n, f₁ k) +
        c₂ * (∑ k ∈ Finset.range n, f₂ k) +
        c₃ * (∑ k ∈ Finset.range n, f₃ k) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    _ ≤ c₁ *
          (u ^ (2 - 2 * x0) *
              (((2 : ℝ) ^ n) ^ (2 - 2 * x0) /
                ((2 : ℝ) ^ (2 - 2 * x0) - 1)) +
            (X : ℝ) ^ (1 - 2 * x0) * (u * (2 : ℝ) ^ n)) +
        c₂ * ((4 * u * (X : ℝ)) ^ (2 - 2 * x0) *
          (((2 : ℝ) ^ n) ^ (2 - 2 * x0) /
            ((2 : ℝ) ^ (2 - 2 * x0) - 1))) +
        c₃ * (u ^ (1 - 2 * x0) *
          (1 - (2 : ℝ) ^ (1 - 2 * x0))⁻¹) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left (by simpa [f₁] using h₁) hc₁
        · exact mul_le_mul_of_nonneg_left h₂ hc₂
      · exact mul_le_mul_of_nonneg_left (by simpa [f₃] using h₃) hc₃
    _ = carlsonSharpDyadicSumMajorant A L X x0 u n := by
      rfl

/-- The complete geometric cover, including its final partial interval, is
bounded by the closed dyadic sum with `n + 1` scales. -/
theorem carlsonSharpGeometricCoverExplicitBound_le_dyadicSumMajorant
    {A L x0 u v : ℝ} {X n : ℕ}
    (hX : 1 ≤ X) (hu : 1 ≤ u) (hx0 : 1 / 2 < x0)
    (hx0One : x0 < 1) (hL : 0 ≤ L)
    (hnv : u * (2 : ℝ) ^ n ≤ v)
    (hvn : v ≤ u * (2 : ℝ) ^ (n + 1))
    (hlog : ∀ k ∈ Finset.range (n + 1),
      (1 + Real.log (Nat.floor (4 * (u * (2 : ℝ) ^ k)) * X)) ^ 3 ≤ L) :
    carlsonSharpGeometricCoverExplicitBound A X x0 u v n ≤
      carlsonSharpDyadicSumMajorant A L X x0 u (n + 1) := by
  have hscaleOne (k : ℕ) : 1 ≤ u * (2 : ℝ) ^ k :=
    one_le_mul_of_one_le_of_one_le hu (one_le_pow₀ (by norm_num))
  have hdouble (k : ℕ) :
      u * (2 : ℝ) ^ (k + 1) = 2 * (u * (2 : ℝ) ^ k) := by
    rw [pow_succ]
    ring
  have hprefix :
      (∑ k ∈ Finset.range n,
        carlsonLogNormSharpEndpointExplicit
          A 4 X x0 (u * (2 : ℝ) ^ k)
            (u * (2 : ℝ) ^ (k + 1))
            (4 * (u * (2 : ℝ) ^ k))) ≤
        ∑ k ∈ Finset.range n,
          carlsonSharpEndpointDyadicMajorant A L X x0
            (u * (2 : ℝ) ^ k) := by
    apply Finset.sum_le_sum
    intro k hk
    apply carlsonLogNormSharpEndpointExplicit_le_dyadicMajorant
      hX (hscaleOne k)
    · rw [hdouble]
      linarith [hscaleOne k]
    · rw [hdouble]
    · exact hx0
    · exact hx0One
    · exact hL
    · exact hlog k (Finset.mem_range.mpr
        (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)))
  have hfinal :
      carlsonLogNormSharpEndpointExplicit
          A 4 X x0 (u * (2 : ℝ) ^ n) v
            (4 * (u * (2 : ℝ) ^ n)) ≤
        carlsonSharpEndpointDyadicMajorant A L X x0
          (u * (2 : ℝ) ^ n) := by
    apply carlsonLogNormSharpEndpointExplicit_le_dyadicMajorant
      hX (hscaleOne n) hnv
    · simpa [hdouble n] using hvn
    · exact hx0
    · exact hx0One
    · exact hL
    · exact hlog n (Finset.mem_range.mpr (Nat.lt_succ_self n))
  calc
    carlsonSharpGeometricCoverExplicitBound A X x0 u v n =
        (∑ k ∈ Finset.range n,
          carlsonLogNormSharpEndpointExplicit
            A 4 X x0 (u * (2 : ℝ) ^ k)
              (u * (2 : ℝ) ^ (k + 1))
              (4 * (u * (2 : ℝ) ^ k))) +
          carlsonLogNormSharpEndpointExplicit
            A 4 X x0 (u * (2 : ℝ) ^ n) v
              (4 * (u * (2 : ℝ) ^ n)) := rfl
    _ ≤ (∑ k ∈ Finset.range n,
          carlsonSharpEndpointDyadicMajorant A L X x0
            (u * (2 : ℝ) ^ k)) +
        carlsonSharpEndpointDyadicMajorant A L X x0
          (u * (2 : ℝ) ^ n) := add_le_add hprefix hfinal
    _ = ∑ k ∈ Finset.range (n + 1),
          carlsonSharpEndpointDyadicMajorant A L X x0
            (u * (2 : ℝ) ^ k) := by
      rw [Finset.sum_range_succ]
    _ ≤ carlsonSharpDyadicSumMajorant A L X x0 u (n + 1) :=
      sum_carlsonSharpEndpointDyadicMajorant_le hX hu hx0 hx0One hL

/-- A single logarithmic factor controls every interval in a Carlson cover
whose height and mollifier length are both at most the ambient height. -/
theorem carlson_cover_log_factor_le
    {T u v : ℝ} {X n k : ℕ}
    (hX : 1 ≤ X) (hu : 1 ≤ u) (hT : 6 ≤ T)
    (hnv : u * (2 : ℝ) ^ n ≤ v) (hvT : v ≤ T + 5 / 4)
    (hXT : (X : ℝ) ≤ T) (hk : k ∈ Finset.range (n + 1)) :
    (1 + Real.log (Nat.floor (4 * (u * (2 : ℝ) ^ k)) * X)) ^ 3 ≤
      (1 + Real.log (4 * (T + 5 / 4) * T)) ^ 3 := by
  have hT0 : 0 ≤ T := by linarith
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hkn
  have hscale : u * (2 : ℝ) ^ k ≤ T + 5 / 4 := by
    calc
      u * (2 : ℝ) ^ k ≤ u * (2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left hpow hu0
      _ ≤ v := hnv
      _ ≤ T + 5 / 4 := hvT
  have hscale0 : 0 ≤ u * (2 : ℝ) ^ k :=
    mul_nonneg hu0 (pow_nonneg (by norm_num) k)
  have hfloor : ((Nat.floor (4 * (u * (2 : ℝ) ^ k)) : ℕ) : ℝ) ≤
      4 * (u * (2 : ℝ) ^ k) :=
    Nat.floor_le (mul_nonneg (by norm_num) hscale0)
  have hproduct :
      (Nat.floor (4 * (u * (2 : ℝ) ^ k)) : ℝ) * (X : ℝ) ≤
        4 * (T + 5 / 4) * T := by
    calc
      (Nat.floor (4 * (u * (2 : ℝ) ^ k)) : ℝ) * (X : ℝ) ≤
          (4 * (u * (2 : ℝ) ^ k)) * (X : ℝ) :=
        mul_le_mul_of_nonneg_right hfloor (Nat.cast_nonneg X)
      _ ≤ (4 * (T + 5 / 4)) * T := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hscale (by norm_num)) hXT
          (Nat.cast_nonneg X) (by positivity)
      _ = 4 * (T + 5 / 4) * T := by ring
  have hfloorFour : 4 ≤ Nat.floor (4 * (u * (2 : ℝ) ^ k)) := by
    apply Nat.le_floor
    have hscaleOne : 1 ≤ u * (2 : ℝ) ^ k :=
      one_le_mul_of_one_le_of_one_le hu (one_le_pow₀ (by norm_num))
    show (4 : ℝ) ≤ 4 * (u * (2 : ℝ) ^ k)
    nlinarith
  have hproductOne : 1 ≤ Nat.floor (4 * (u * (2 : ℝ) ^ k)) * X := by
    nlinarith
  have hproductOneReal : (1 : ℝ) ≤
      (Nat.floor (4 * (u * (2 : ℝ) ^ k)) : ℝ) * (X : ℝ) := by
    exact_mod_cast hproductOne
  have htargetOne : (1 : ℝ) ≤ 4 * (T + 5 / 4) * T := by
    nlinarith [sq_nonneg T]
  have hlog := Real.log_le_log (by positivity) hproduct
  have hleft0 : 0 ≤ 1 +
      Real.log ((Nat.floor (4 * (u * (2 : ℝ) ^ k)) : ℝ) * (X : ℝ)) :=
    add_nonneg (by norm_num) (Real.log_nonneg hproductOneReal)
  exact pow_le_pow_left₀ hleft0 (by linarith) 3

/-- Carlson's optimized mollifier length is at most the ambient height in the
critical strip. -/
theorem carlsonMollifierLength_le_height {sigma T : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hT : 1 ≤ T) (hpower : 1 ≤ T ^ (2 * sigma - 1)) :
    (carlsonMollifierLength sigma T : ℝ) ≤ T := by
  have hlength := (carlsonMollifierLength_bounds hpower).2
  have htarget : T ^ (2 * sigma - 1) ≤ T ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  simpa only [Real.rpow_one] using hlength.trans htarget

/-- Uniform logarithmic cube used for the full Carlson cover at height `T`. -/
noncomputable def carlsonAmbientLogCube (T : ℝ) : ℝ :=
  (1 + Real.log (4 * (T + 5 / 4) * T)) ^ 3

/-- The actual optimized Carlson cover is bounded by the closed dyadic
majorant with the ambient logarithmic cube installed. -/
theorem carlson_parameterized_geometric_cover_le_dyadicSumMajorant
    {A sigma T x0 u v : ℝ} {n : ℕ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hT : 6 ≤ T) (hpower : 1 ≤ T ^ (2 * sigma - 1))
    (hx0 : 1 / 2 < x0) (hx0One : x0 < 1)
    (hu : 1 ≤ u) (hnv : u * (2 : ℝ) ^ n ≤ v)
    (hvn : v ≤ u * (2 : ℝ) ^ (n + 1)) (hvT : v ≤ T + 5 / 4) :
    carlsonSharpGeometricCoverExplicitBound A
        (carlsonMollifierLength sigma T) x0 u v n ≤
      carlsonSharpDyadicSumMajorant A (carlsonAmbientLogCube T)
        (carlsonMollifierLength sigma T) x0 u (n + 1) := by
  have hTOne : 1 ≤ T := by linarith
  have hXT : (carlsonMollifierLength sigma T : ℝ) ≤ T :=
    carlsonMollifierLength_le_height hsigma hsigmaOne hTOne hpower
  have hargOne : (1 : ℝ) ≤ 4 * (T + 5 / 4) * T := by
    nlinarith [sq_nonneg T]
  have hL : 0 ≤ carlsonAmbientLogCube T := by
    dsimp [carlsonAmbientLogCube]
    exact pow_nonneg
      (add_nonneg (by norm_num) (Real.log_nonneg hargOne)) _
  apply carlsonSharpGeometricCoverExplicitBound_le_dyadicSumMajorant
    (one_le_carlsonMollifierLength sigma T) hu hx0 hx0One hL hnv hvn
  intro k hk
  exact carlson_cover_log_factor_le
    (one_le_carlsonMollifierLength sigma T) hu hT hnv hvT hXT hk

/-- A scaled terminal geometric term is controlled by any upper bound for
the terminal scale. -/
theorem scaled_dyadic_terminal_rpow_div_le
    {u B q : ℝ} {n : ℕ} (hu : 0 ≤ u) (hB : 0 ≤ B)
    (hterminal : u * (2 : ℝ) ^ n ≤ B) (hq : 0 < q) :
    u ^ q * (((2 : ℝ) ^ n) ^ q / ((2 : ℝ) ^ q - 1)) ≤
      B ^ q / ((2 : ℝ) ^ q - 1) := by
  have hden : 0 < (2 : ℝ) ^ q - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) hq)
  have hpow : (u * (2 : ℝ) ^ n) ^ q ≤ B ^ q :=
    Real.rpow_le_rpow
      (mul_nonneg hu (pow_nonneg (by norm_num) n)) hterminal hq.le
  calc
    u ^ q * (((2 : ℝ) ^ n) ^ q / ((2 : ℝ) ^ q - 1)) =
        (u * (2 : ℝ) ^ n) ^ q / ((2 : ℝ) ^ q - 1) := by
      rw [Real.mul_rpow hu (pow_nonneg (by norm_num) n)]
      ring
    _ ≤ B ^ q / ((2 : ℝ) ^ q - 1) :=
      (div_le_div_iff_of_pos_right hden).2 hpow

/-- The next dyadic scale after the last full interval is at most twice the
top of the cover. -/
theorem carlson_cover_next_scale_le {T u v : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hnv : u * (2 : ℝ) ^ n ≤ v)
    (hvT : v ≤ T + 5 / 4) :
    u * (2 : ℝ) ^ (n + 1) ≤ 2 * (T + 5 / 4) := by
  rw [pow_succ]
  nlinarith

/-- The dyadic sharp endpoint majorant after replacing its terminal scale by
an ambient upper bound `B`. -/
noncomputable def carlsonSharpAmbientMajorant
    (A L : ℝ) (X : ℕ) (x0 u B : ℝ) : ℝ :=
  (2 * L * (2 + 1 / (2 * x0 - 1))) *
      (B ^ (2 - 2 * x0) / ((2 : ℝ) ^ (2 - 2 * x0) - 1) +
        (X : ℝ) ^ (1 - 2 * x0) * B) +
    (16 * Real.pi * L * (2 + 1 / (2 - 2 * x0))) *
      ((4 * (X : ℝ) * B) ^ (2 - 2 * x0) /
        ((2 : ℝ) ^ (2 - 2 * x0) - 1)) +
    (4 * ((A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
        (1 + 4 * Real.pi)) *
      (1 + (X : ℝ) ^ (2 - 2 * x0) / (2 - 2 * x0))) *
        (u ^ (1 - 2 * x0) *
          (1 - (2 : ℝ) ^ (1 - 2 * x0))⁻¹)

/-- Eliminating the final dyadic index in favor of an ambient scale bound. -/
theorem carlsonSharpDyadicSumMajorant_le_ambient
    {A L x0 u B : ℝ} {X n : ℕ}
    (hL : 0 ≤ L) (hu : 0 ≤ u) (hB : 0 ≤ B)
    (hterminal : u * (2 : ℝ) ^ n ≤ B)
    (hx0 : 1 / 2 < x0) (hx0One : x0 < 1) :
    carlsonSharpDyadicSumMajorant A L X x0 u n ≤
      carlsonSharpAmbientMajorant A L X x0 u B := by
  have hminusDen : 0 < 2 * x0 - 1 := by linarith
  have hplusDen : 0 < 2 - 2 * x0 := by linarith
  have hp : 1 - 2 * x0 < 0 := by linarith
  have hX0 : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  have hc₁ : 0 ≤ 2 * L * (2 + 1 / (2 * x0 - 1)) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hL)
      (add_nonneg (by norm_num) (one_div_nonneg.mpr hminusDen.le))
  have hc₂ : 0 ≤ 16 * Real.pi * L * (2 + 1 / (2 - 2 * x0)) := by
    positivity
  have hXpow : 0 ≤ (X : ℝ) ^ (2 - 2 * x0) :=
    Real.rpow_nonneg hX0 _
  have hc₃ : 0 ≤
      4 * ((A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
          (1 + 4 * Real.pi)) *
        (1 + (X : ℝ) ^ (2 - 2 * x0) / (2 - 2 * x0)) := by
    positivity
  have hfirst := scaled_dyadic_terminal_rpow_div_le
    hu hB hterminal hplusDen
  have hlinear :
      (X : ℝ) ^ (1 - 2 * x0) * (u * (2 : ℝ) ^ n) ≤
        (X : ℝ) ^ (1 - 2 * x0) * B :=
    mul_le_mul_of_nonneg_left hterminal (Real.rpow_nonneg hX0 _)
  have hscaled :
      (4 * u * (X : ℝ)) * (2 : ℝ) ^ n ≤ 4 * (X : ℝ) * B := by
    calc
      (4 * u * (X : ℝ)) * (2 : ℝ) ^ n =
          (4 * (X : ℝ)) * (u * (2 : ℝ) ^ n) := by ring
      _ ≤ (4 * (X : ℝ)) * B :=
        mul_le_mul_of_nonneg_left hterminal (mul_nonneg (by norm_num) hX0)
  have hsecond := scaled_dyadic_terminal_rpow_div_le
    (u := 4 * u * (X : ℝ)) (B := 4 * (X : ℝ) * B)
    (q := 2 - 2 * x0) (n := n)
    (mul_nonneg (mul_nonneg (by norm_num) hu) hX0)
    (mul_nonneg (mul_nonneg (by norm_num) hX0) hB)
    hscaled hplusDen
  unfold carlsonSharpDyadicSumMajorant carlsonSharpAmbientMajorant
  apply add_le_add
  · apply add_le_add
    · exact mul_le_mul_of_nonneg_left (add_le_add hfirst hlinear) hc₁
    · exact mul_le_mul_of_nonneg_left hsecond hc₂
  · exact le_rfl

/-- The arithmetic part of the optimized contour certificate with both the
dyadic index and the local logarithmic factors eliminated. -/
theorem carlson_parameterized_geometric_cover_le_ambient
    {A sigma T x0 u v : ℝ} {n : ℕ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hT : 6 ≤ T) (hpower : 1 ≤ T ^ (2 * sigma - 1))
    (hx0 : 1 / 2 < x0) (hx0One : x0 < 1)
    (hu : 1 ≤ u) (hnv : u * (2 : ℝ) ^ n ≤ v)
    (hvn : v ≤ u * (2 : ℝ) ^ (n + 1)) (hvT : v ≤ T + 5 / 4) :
    carlsonSharpGeometricCoverExplicitBound A
        (carlsonMollifierLength sigma T) x0 u v n ≤
      carlsonSharpAmbientMajorant A (carlsonAmbientLogCube T)
        (carlsonMollifierLength sigma T) x0 u (2 * (T + 5 / 4)) := by
  have hcover := carlson_parameterized_geometric_cover_le_dyadicSumMajorant
    (A := A) hsigma hsigmaOne hT hpower hx0 hx0One hu hnv hvn hvT
  have hB : 0 ≤ 2 * (T + 5 / 4) := by linarith
  have hargOne : (1 : ℝ) ≤ 4 * (T + 5 / 4) * T := by
    nlinarith [sq_nonneg T]
  have hterminal : u * (2 : ℝ) ^ (n + 1) ≤ 2 * (T + 5 / 4) :=
    carlson_cover_next_scale_le (zero_le_one.trans hu) hnv hvT
  exact hcover.trans (carlsonSharpDyadicSumMajorant_le_ambient
    (A := A) (L := carlsonAmbientLogCube T)
    (X := carlsonMollifierLength sigma T) (x0 := x0) (u := u)
    (B := 2 * (T + 5 / 4)) (n := n + 1)
    (by
      dsimp [carlsonAmbientLogCube]
      exact pow_nonneg
        (add_nonneg (by norm_num) (Real.log_nonneg hargOne)) _)
    (zero_le_one.trans hu) hB hterminal hx0 hx0One)

/-- On the interval of exponents relevant to Carlson's auxiliary line, the
factor introduced by rounding the mollifier length down is at most two. -/
theorem half_rpow_le_two_of_neg_one_le {p : ℝ} (hp : -1 ≤ p) :
    (1 / 2 : ℝ) ^ p ≤ 2 := by
  calc
    (1 / 2 : ℝ) ^ p ≤ (1 / 2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hp
    _ = 2 := by norm_num [Real.rpow_neg_one]

/-- The negative power of the rounded Carlson mollifier length differs from
the ideal real-valued length by at most a factor of two. -/
theorem carlsonMollifierLength_negative_rpow_le
    {sigma T x0 : ℝ} (hT : 0 < T)
    (hpower : 1 ≤ T ^ (2 * sigma - 1))
    (hx0 : 1 / 2 < x0) (hx0One : x0 < 1) :
    (carlsonMollifierLength sigma T : ℝ) ^ (1 - 2 * x0) ≤
      2 * T ^ ((2 * sigma - 1) * (1 - 2 * x0)) := by
  let Y : ℝ := T ^ (2 * sigma - 1)
  have hYOne : 1 ≤ Y := by simpa [Y] using hpower
  have hY0 : 0 ≤ Y := zero_le_one.trans hYOne
  have hhalfPos : 0 < Y / 2 := div_pos (zero_lt_one.trans_le hYOne) (by norm_num)
  have hlengthLower : Y / 2 ≤ (carlsonMollifierLength sigma T : ℝ) := by
    simpa [Y] using (carlsonMollifierLength_bounds hpower).1
  have hp : 1 - 2 * x0 < 0 := by linarith
  have hround :
      (carlsonMollifierLength sigma T : ℝ) ^ (1 - 2 * x0) ≤
        (Y / 2) ^ (1 - 2 * x0) :=
    Real.rpow_le_rpow_of_nonpos hhalfPos hlengthLower hp.le
  have hhalf : (1 / 2 : ℝ) ^ (1 - 2 * x0) ≤ 2 :=
    half_rpow_le_two_of_neg_one_le (by linarith)
  calc
    (carlsonMollifierLength sigma T : ℝ) ^ (1 - 2 * x0) ≤
        (Y / 2) ^ (1 - 2 * x0) := hround
    _ = Y ^ (1 - 2 * x0) * (1 / 2 : ℝ) ^ (1 - 2 * x0) := by
      rw [show Y / 2 = Y * (1 / 2 : ℝ) by ring,
        Real.mul_rpow hY0 (by norm_num)]
    _ ≤ Y ^ (1 - 2 * x0) * 2 :=
      mul_le_mul_of_nonneg_left hhalf (Real.rpow_nonneg hY0 _)
    _ = 2 * T ^ ((2 * sigma - 1) * (1 - 2 * x0)) := by
      dsimp [Y]
      rw [← Real.rpow_mul hT.le]
      ring

/-- The optimized lower-endpoint term in the ambient majorant has Carlson's
target exponent, up to an absolute constant. -/
theorem carlson_optimized_lower_ambient_term_le
    {sigma T x0 : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1) (hT : 6 ≤ T) (hlog : 0 < Real.log T)
    (hpower : 1 ≤ T ^ (2 * sigma - 1))
    (hx0 : 1 / 2 < x0) (hx0One : x0 < 1)
    (hx0Sigma : x0 < sigma) (hgap : sigma - x0 < 2 / Real.log T) :
    (carlsonMollifierLength sigma T : ℝ) ^ (1 - 2 * x0) *
        (2 * (T + 5 / 4)) ≤
      6 * Real.exp 4 * T ^ (4 * sigma * (1 - sigma)) := by
  have hTPos : 0 < T := by linarith
  have hB : 2 * (T + 5 / 4) ≤ 3 * T := by linarith
  have hX := carlsonMollifierLength_negative_rpow_le
    hTPos hpower hx0 hx0One
  have hX0 : 0 ≤
      (carlsonMollifierLength sigma T : ℝ) ^ (1 - 2 * x0) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hB0 : 0 ≤ 2 * (T + 5 / 4) := by linarith
  have hproduct := mul_le_mul hX hB hB0
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hTPos.le _))
  have hexponent := carlson_lower_endpoint_rpow_le
    hsigma hsigmaOne hTPos hlog hx0Sigma hgap
  calc
    (carlsonMollifierLength sigma T : ℝ) ^ (1 - 2 * x0) *
        (2 * (T + 5 / 4)) ≤
      (2 * T ^ ((2 * sigma - 1) * (1 - 2 * x0))) * (3 * T) :=
        hproduct
    _ = 6 * T ^ (1 + (2 * sigma - 1) * (1 - 2 * x0)) := by
      calc
        (2 * T ^ ((2 * sigma - 1) * (1 - 2 * x0))) * (3 * T) =
            6 * (T ^ ((2 * sigma - 1) * (1 - 2 * x0)) * T) := by ring
        _ = 6 * T ^ ((2 * sigma - 1) * (1 - 2 * x0) + 1) := by
          rw [Real.rpow_add hTPos, Real.rpow_one]
        _ = 6 * T ^ (1 + (2 * sigma - 1) * (1 - 2 * x0)) := by
          congr 2
          ring
    _ ≤ 6 * (Real.exp 4 * T ^ (4 * sigma * (1 - sigma))) :=
      mul_le_mul_of_nonneg_left hexponent (by norm_num)
    _ = 6 * Real.exp 4 * T ^ (4 * sigma * (1 - sigma)) := by ring

/-- The optimized upper-endpoint term in the ambient majorant has Carlson's
target exponent, up to an absolute constant. -/
theorem carlson_optimized_upper_ambient_term_le
    {sigma T x0 : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1) (hT : 6 ≤ T) (hlog : 0 < Real.log T)
    (hpower : 1 ≤ T ^ (2 * sigma - 1))
    (hx0 : 1 / 2 < x0) (hx0One : x0 < 1)
    (hx0Sigma : x0 < sigma) (hgap : sigma - x0 < 2 / Real.log T) :
    (4 * (carlsonMollifierLength sigma T : ℝ) *
        (2 * (T + 5 / 4))) ^ (2 - 2 * x0) ≤
      144 * Real.exp 8 * T ^ (4 * sigma * (1 - sigma)) := by
  have hTPos : 0 < T := by linarith
  have hB0 : 0 ≤ 2 * (T + 5 / 4) := by linarith
  have hB : 2 * (T + 5 / 4) ≤ 3 * T := by linarith
  have hX := (carlsonMollifierLength_bounds hpower).2
  have hY0 : 0 ≤ T ^ (2 * sigma - 1) := Real.rpow_nonneg hTPos.le _
  have hbase0 : 0 ≤ 4 * (carlsonMollifierLength sigma T : ℝ) *
      (2 * (T + 5 / 4)) := by positivity
  have hbase :
      4 * (carlsonMollifierLength sigma T : ℝ) *
          (2 * (T + 5 / 4)) ≤
        12 * T ^ (1 + (2 * sigma - 1)) := by
    have hproduct := mul_le_mul hX hB hB0 hY0
    calc
      4 * (carlsonMollifierLength sigma T : ℝ) *
          (2 * (T + 5 / 4)) ≤
          12 * (T ^ (2 * sigma - 1) * T) := by nlinarith
      _ = 12 * T ^ ((2 * sigma - 1) + 1) := by
        rw [Real.rpow_add hTPos, Real.rpow_one]
      _ = 12 * T ^ (1 + (2 * sigma - 1)) := by ring
  have hq0 : 0 ≤ 2 - 2 * x0 := by linarith
  have hqTwo : 2 - 2 * x0 ≤ 2 := by linarith
  have hconstant : (12 : ℝ) ^ (2 - 2 * x0) ≤ 144 := by
    calc
      (12 : ℝ) ^ (2 - 2 * x0) ≤ (12 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hqTwo
      _ = 144 := by norm_num [Real.rpow_two]
  have hexponent := carlson_upper_endpoint_rpow_le
    hsigma hsigmaOne hTPos hlog hx0Sigma hgap
  calc
    (4 * (carlsonMollifierLength sigma T : ℝ) *
        (2 * (T + 5 / 4))) ^ (2 - 2 * x0) ≤
        (12 * T ^ (1 + (2 * sigma - 1))) ^ (2 - 2 * x0) :=
      Real.rpow_le_rpow hbase0 hbase hq0
    _ = (12 : ℝ) ^ (2 - 2 * x0) *
        T ^ ((1 + (2 * sigma - 1)) * (2 - 2 * x0)) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hTPos.le _),
        ← Real.rpow_mul hTPos.le]
    _ ≤ 144 * (Real.exp 8 * T ^ (4 * sigma * (1 - sigma))) :=
      mul_le_mul hconstant hexponent
        (Real.rpow_nonneg hTPos.le _) (by norm_num)
    _ = 144 * Real.exp 8 * T ^ (4 * sigma * (1 - sigma)) := by ring

/-- Once the height is large relative to fixed `sigma`, Carlson's selected
auxiliary line stays a fixed positive distance from both strip boundaries. -/
theorem carlson_auxiliary_line_fixed_gap
    {sigma T x0 : ℝ} (hlog : 0 < Real.log T)
    (hlarge : 4 / Real.log T < sigma - 1 / 2)
    (hx0Sigma : x0 < sigma) (hgap : sigma - x0 < 2 / Real.log T) :
    sigma - 1 / 2 < 2 * x0 - 1 ∧
      2 - 2 * sigma < 2 - 2 * x0 ∧
      1 - 2 * x0 < 1 / 2 - sigma := by
  have hdouble : 4 / Real.log T = 2 * (2 / Real.log T) := by
    field_simp
    ring
  have hmid : 2 * (sigma - x0) < sigma - 1 / 2 := by
    calc
      2 * (sigma - x0) < 2 * (2 / Real.log T) := by linarith
      _ < sigma - 1 / 2 := by simpa [hdouble] using hlarge
  constructor
  · linarith
  constructor <;> linarith

/-- Every reciprocal denominator in the closed Carlson ambient majorant is
uniformly bounded by a constant depending only on the fixed `sigma`. -/
theorem carlson_auxiliary_line_denominator_bounds
    {sigma T x0 : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1) (hlog : 0 < Real.log T)
    (hlarge : 4 / Real.log T < sigma - 1 / 2)
    (hx0Sigma : x0 < sigma) (hgap : sigma - x0 < 2 / Real.log T) :
    1 / (2 * x0 - 1) ≤ 1 / (sigma - 1 / 2) ∧
      1 / (2 - 2 * x0) ≤ 1 / (2 - 2 * sigma) ∧
      1 / ((2 : ℝ) ^ (2 - 2 * x0) - 1) ≤
        1 / ((2 : ℝ) ^ (2 - 2 * sigma) - 1) ∧
      (1 - (2 : ℝ) ^ (1 - 2 * x0))⁻¹ ≤
        (1 - (2 : ℝ) ^ (1 / 2 - sigma))⁻¹ := by
  rcases carlson_auxiliary_line_fixed_gap hlog hlarge hx0Sigma hgap with
    ⟨hleft, hright, hnegative⟩
  have hdeltaPos : 0 < sigma - 1 / 2 := by linarith
  have hrightPos : 0 < 2 - 2 * sigma := by linarith
  have htwoPow :
      (2 : ℝ) ^ (2 - 2 * sigma) ≤ (2 : ℝ) ^ (2 - 2 * x0) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hright.le
  have htwoDenPos : 0 < (2 : ℝ) ^ (2 - 2 * sigma) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) hrightPos)
  have hnegativePow :
      (2 : ℝ) ^ (1 - 2 * x0) ≤ (2 : ℝ) ^ (1 / 2 - sigma) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hnegative.le
  have hnegativeDenPos : 0 < 1 - (2 : ℝ) ^ (1 / 2 - sigma) :=
    sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  constructor
  · exact one_div_le_one_div_of_le hdeltaPos hleft.le
  constructor
  · exact one_div_le_one_div_of_le hrightPos hright.le
  constructor
  · exact one_div_le_one_div_of_le htwoDenPos (by linarith)
  · simpa only [one_div] using
      one_div_le_one_div_of_le hnegativeDenPos (by linarith)

/-- Both exponents left after choosing `X = T^(2*sigma-1)` differ from
Carlson's target exponent by at most twice the auxiliary-line gap. -/
theorem carlson_auxiliary_exponents_le_target_plus_gap
    {sigma x0 : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1) (hx0 : 1 / 2 < x0)
    (hx0Sigma : x0 < sigma) :
    2 - 2 * x0 ≤ 4 * sigma * (1 - sigma) + 2 * (sigma - x0) ∧
      (2 * sigma - 1) * (2 - 2 * x0) ≤
        4 * sigma * (1 - sigma) + 2 * (sigma - x0) := by
  have hstrip : 0 ≤ 2 * (1 - sigma) * (2 * sigma - 1) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  have htarget : 2 - 2 * sigma ≤ 4 * sigma * (1 - sigma) := by
    nlinarith
  have hq0 : 0 ≤ 2 - 2 * x0 := by linarith
  have halpha0 : 0 ≤ 2 * sigma - 1 := by linarith
  have halphaOne : 2 * sigma - 1 ≤ 1 := by linarith
  have honeMinusAlpha : 0 ≤ 1 - (2 * sigma - 1) := by linarith
  have hscaled :
      (2 * sigma - 1) * (2 - 2 * x0) ≤ 2 - 2 * x0 := by
    nlinarith [mul_nonneg honeMinusAlpha hq0]
  constructor
  · nlinarith
  · exact hscaled.trans (by nlinarith)

/-- The terminal positive power in the first ambient summand is absorbed by
Carlson's target exponent, with only an absolute exponential loss. -/
theorem carlson_terminal_rpow_le
    {sigma T x0 : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1) (hT : 6 ≤ T) (hlog : 0 < Real.log T)
    (hx0 : 1 / 2 < x0) (hx0One : x0 < 1)
    (hx0Sigma : x0 < sigma) (hgap : sigma - x0 < 2 / Real.log T) :
    (2 * (T + 5 / 4)) ^ (2 - 2 * x0) ≤
      9 * Real.exp 4 * T ^ (4 * sigma * (1 - sigma)) := by
  have hTPos : 0 < T := by linarith
  have hB0 : 0 ≤ 2 * (T + 5 / 4) := by linarith
  have hB : 2 * (T + 5 / 4) ≤ 3 * T := by linarith
  have hq0 : 0 ≤ 2 - 2 * x0 := by linarith
  have hqTwo : 2 - 2 * x0 ≤ 2 := by linarith
  have hthree : (3 : ℝ) ^ (2 - 2 * x0) ≤ 9 := by
    calc
      (3 : ℝ) ^ (2 - 2 * x0) ≤ (3 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hqTwo
      _ = 9 := by norm_num [Real.rpow_two]
  have hexponent :=
    (carlson_auxiliary_exponents_le_target_plus_gap
      hsigma hsigmaOne hx0 hx0Sigma).1
  have hgapMul : (sigma - x0) * Real.log T < 2 :=
    (lt_div_iff₀ hlog).mp hgap
  have hexponentGap :
      ((2 - 2 * x0) - 4 * sigma * (1 - sigma)) * Real.log T ≤ 4 := by
    calc
      ((2 - 2 * x0) - 4 * sigma * (1 - sigma)) * Real.log T ≤
          (2 * (sigma - x0)) * Real.log T :=
        mul_le_mul_of_nonneg_right (by linarith) hlog.le
      _ ≤ 4 := by nlinarith
  have hTpow := rpow_le_exp_mul_rpow_of_exponent_gap hTPos hexponentGap
  calc
    (2 * (T + 5 / 4)) ^ (2 - 2 * x0) ≤
        (3 * T) ^ (2 - 2 * x0) :=
      Real.rpow_le_rpow hB0 hB hq0
    _ = (3 : ℝ) ^ (2 - 2 * x0) * T ^ (2 - 2 * x0) := by
      rw [Real.mul_rpow (by norm_num) hTPos.le]
    _ ≤ 9 * (Real.exp 4 * T ^ (4 * sigma * (1 - sigma))) :=
      mul_le_mul hthree hTpow (Real.rpow_nonneg hTPos.le _) (by norm_num)
    _ = 9 * Real.exp 4 * T ^ (4 * sigma * (1 - sigma)) := by ring

/-- The positive power of the rounded optimized mollifier length is likewise
absorbed by Carlson's target exponent. -/
theorem carlsonMollifierLength_positive_rpow_le
    {sigma T x0 : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1) (hT : 6 ≤ T) (hlog : 0 < Real.log T)
    (hpower : 1 ≤ T ^ (2 * sigma - 1))
    (hx0 : 1 / 2 < x0) (hx0One : x0 < 1)
    (hx0Sigma : x0 < sigma) (hgap : sigma - x0 < 2 / Real.log T) :
    (carlsonMollifierLength sigma T : ℝ) ^ (2 - 2 * x0) ≤
      Real.exp 4 * T ^ (4 * sigma * (1 - sigma)) := by
  have hTPos : 0 < T := by linarith
  have hq0 : 0 ≤ 2 - 2 * x0 := by linarith
  have hX0 : 0 ≤ (carlsonMollifierLength sigma T : ℝ) := Nat.cast_nonneg _
  have hX := (carlsonMollifierLength_bounds hpower).2
  have hexponent :=
    (carlson_auxiliary_exponents_le_target_plus_gap
      hsigma hsigmaOne hx0 hx0Sigma).2
  have hgapMul : (sigma - x0) * Real.log T < 2 :=
    (lt_div_iff₀ hlog).mp hgap
  have hexponentGap :
      ((2 * sigma - 1) * (2 - 2 * x0) -
          4 * sigma * (1 - sigma)) * Real.log T ≤ 4 := by
    calc
      ((2 * sigma - 1) * (2 - 2 * x0) -
          4 * sigma * (1 - sigma)) * Real.log T ≤
          (2 * (sigma - x0)) * Real.log T :=
        mul_le_mul_of_nonneg_right (by linarith) hlog.le
      _ ≤ 4 := by nlinarith
  have hTpow := rpow_le_exp_mul_rpow_of_exponent_gap hTPos hexponentGap
  calc
    (carlsonMollifierLength sigma T : ℝ) ^ (2 - 2 * x0) ≤
        (T ^ (2 * sigma - 1)) ^ (2 - 2 * x0) :=
      Real.rpow_le_rpow hX0 hX hq0
    _ = T ^ ((2 * sigma - 1) * (2 - 2 * x0)) := by
      rw [← Real.rpow_mul hTPos.le]
    _ ≤ Real.exp 4 * T ^ (4 * sigma * (1 - sigma)) := hTpow

/-- The ambient logarithmic cube is at least one at every height used by the
Carlson contour. -/
theorem one_le_carlsonAmbientLogCube {T : ℝ} (hT : 6 ≤ T) :
    1 ≤ carlsonAmbientLogCube T := by
  have hargOne : (1 : ℝ) ≤ 4 * (T + 5 / 4) * T := by
    nlinarith [sq_nonneg T]
  have hbase : 1 ≤ 1 + Real.log (4 * (T + 5 / 4) * T) := by
    linarith [Real.log_nonneg hargOne]
  dsimp [carlsonAmbientLogCube]
  nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hbase 3]

/-- Carlson's target power is at least one in the large-height regime. -/
theorem one_le_carlson_target_rpow {sigma T : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) (hT : 6 ≤ T) :
    1 ≤ T ^ (4 * sigma * (1 - sigma)) := by
  have hTOne : 1 ≤ T := by linarith
  have hexponent : 0 ≤ 4 * sigma * (1 - sigma) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  exact Real.one_le_rpow hTOne hexponent

/-- The first bracket in the closed ambient majorant has Carlson's optimized
growth, with all geometric denominators frozen at fixed `sigma`. -/
theorem carlson_ambient_first_bracket_le
    {sigma T x0 : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1) (hT : 6 ≤ T) (hlog : 0 < Real.log T)
    (hlarge : 4 / Real.log T < sigma - 1 / 2)
    (hpower : 1 ≤ T ^ (2 * sigma - 1))
    (hx0 : 1 / 2 < x0) (hx0One : x0 < 1)
    (hx0Sigma : x0 < sigma) (hgap : sigma - x0 < 2 / Real.log T) :
    (2 * (T + 5 / 4)) ^ (2 - 2 * x0) /
          ((2 : ℝ) ^ (2 - 2 * x0) - 1) +
        (carlsonMollifierLength sigma T : ℝ) ^ (1 - 2 * x0) *
          (2 * (T + 5 / 4)) ≤
      (9 * Real.exp 4 /
          ((2 : ℝ) ^ (2 - 2 * sigma) - 1) + 6 * Real.exp 4) *
        T ^ (4 * sigma * (1 - sigma)) := by
  have hTPos : 0 < T := by linarith
  have hqPos : 0 < 2 - 2 * x0 := by linarith
  have hdenPos : 0 < (2 : ℝ) ^ (2 - 2 * x0) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) hqPos)
  have hfixedQPos : 0 < 2 - 2 * sigma := by linarith
  have hfixedDenPos : 0 < (2 : ℝ) ^ (2 - 2 * sigma) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) hfixedQPos)
  have hdenInv :=
    (carlson_auxiliary_line_denominator_bounds hsigma hsigmaOne hlog
      hlarge hx0Sigma hgap).2.2.1
  have hterminal := carlson_terminal_rpow_le hsigma hsigmaOne hT hlog
    hx0 hx0One hx0Sigma hgap
  have hquotient :
      (2 * (T + 5 / 4)) ^ (2 - 2 * x0) /
          ((2 : ℝ) ^ (2 - 2 * x0) - 1) ≤
        (9 * Real.exp 4 /
            ((2 : ℝ) ^ (2 - 2 * sigma) - 1)) *
          T ^ (4 * sigma * (1 - sigma)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      (2 * (T + 5 / 4)) ^ (2 - 2 * x0) *
          ((2 : ℝ) ^ (2 - 2 * x0) - 1)⁻¹ ≤
          (9 * Real.exp 4 * T ^ (4 * sigma * (1 - sigma))) *
            ((2 : ℝ) ^ (2 - 2 * sigma) - 1)⁻¹ :=
        mul_le_mul hterminal (by simpa only [one_div] using hdenInv)
          (inv_nonneg.mpr hdenPos.le) (by positivity)
      _ = (9 * Real.exp 4 *
            ((2 : ℝ) ^ (2 - 2 * sigma) - 1)⁻¹) *
          T ^ (4 * sigma * (1 - sigma)) := by ring
  have hlower := carlson_optimized_lower_ambient_term_le
    hsigma hsigmaOne hT hlog hpower hx0 hx0One hx0Sigma hgap
  nlinarith

/-- The second bracket in the closed ambient majorant has the same optimized
power after freezing its positive geometric denominator. -/
theorem carlson_ambient_second_bracket_le
    {sigma T x0 : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1) (hT : 6 ≤ T) (hlog : 0 < Real.log T)
    (hlarge : 4 / Real.log T < sigma - 1 / 2)
    (hpower : 1 ≤ T ^ (2 * sigma - 1))
    (hx0 : 1 / 2 < x0) (hx0One : x0 < 1)
    (hx0Sigma : x0 < sigma) (hgap : sigma - x0 < 2 / Real.log T) :
    (4 * (carlsonMollifierLength sigma T : ℝ) *
        (2 * (T + 5 / 4))) ^ (2 - 2 * x0) /
          ((2 : ℝ) ^ (2 - 2 * x0) - 1) ≤
      (144 * Real.exp 8 /
          ((2 : ℝ) ^ (2 - 2 * sigma) - 1)) *
        T ^ (4 * sigma * (1 - sigma)) := by
  have hqPos : 0 < 2 - 2 * x0 := by linarith
  have hdenPos : 0 < (2 : ℝ) ^ (2 - 2 * x0) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) hqPos)
  have hdenInv :=
    (carlson_auxiliary_line_denominator_bounds hsigma hsigmaOne hlog
      hlarge hx0Sigma hgap).2.2.1
  have hupper := carlson_optimized_upper_ambient_term_le
    hsigma hsigmaOne hT hlog hpower hx0 hx0One hx0Sigma hgap
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    (4 * (carlsonMollifierLength sigma T : ℝ) *
        (2 * (T + 5 / 4))) ^ (2 - 2 * x0) *
          ((2 : ℝ) ^ (2 - 2 * x0) - 1)⁻¹ ≤
        (144 * Real.exp 8 * T ^ (4 * sigma * (1 - sigma))) *
          ((2 : ℝ) ^ (2 - 2 * sigma) - 1)⁻¹ :=
      mul_le_mul hupper (by simpa only [one_div] using hdenInv)
        (inv_nonneg.mpr hdenPos.le) (by positivity)
    _ = (144 * Real.exp 8 *
          ((2 : ℝ) ^ (2 - 2 * sigma) - 1)⁻¹) *
        T ^ (4 * sigma * (1 - sigma)) := by ring

/-- The fixed-start remainder bracket is lower order than Carlson's target
power after all auxiliary-line denominators are frozen at fixed `sigma`. -/
theorem carlson_ambient_remainder_bracket_le
    {sigma T x0 u : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1) (hT : 6 ≤ T) (hlog : 0 < Real.log T)
    (hlarge : 4 / Real.log T < sigma - 1 / 2)
    (hpower : 1 ≤ T ^ (2 * sigma - 1))
    (hx0 : 1 / 2 < x0) (hx0One : x0 < 1)
    (hx0Sigma : x0 < sigma) (hgap : sigma - x0 < 2 / Real.log T)
    (hu : 1 ≤ u) :
    (1 + (carlsonMollifierLength sigma T : ℝ) ^ (2 - 2 * x0) /
          (2 - 2 * x0)) *
        (u ^ (1 - 2 * x0) *
          (1 - (2 : ℝ) ^ (1 - 2 * x0))⁻¹) ≤
      ((1 + Real.exp 4 / (2 - 2 * sigma)) *
          (1 - (2 : ℝ) ^ (1 / 2 - sigma))⁻¹) *
        T ^ (4 * sigma * (1 - sigma)) := by
  have hqPos : 0 < 2 - 2 * x0 := by linarith
  have hfixedQPos : 0 < 2 - 2 * sigma := by linarith
  have hp : 1 - 2 * x0 ≤ 0 := by linarith
  have hactualNegDenPos : 0 < 1 - (2 : ℝ) ^ (1 - 2 * x0) :=
    sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hfixedNegDenPos : 0 < 1 - (2 : ℝ) ^ (1 / 2 - sigma) :=
    sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  rcases carlson_auxiliary_line_denominator_bounds hsigma hsigmaOne hlog
      hlarge hx0Sigma hgap with ⟨_hleft, hqInv, _hpositive, hnegativeInv⟩
  have hXpow := carlsonMollifierLength_positive_rpow_le
    hsigma hsigmaOne hT hlog hpower hx0 hx0One hx0Sigma hgap
  have hXquot :
      (carlsonMollifierLength sigma T : ℝ) ^ (2 - 2 * x0) /
          (2 - 2 * x0) ≤
        (Real.exp 4 / (2 - 2 * sigma)) *
          T ^ (4 * sigma * (1 - sigma)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      (carlsonMollifierLength sigma T : ℝ) ^ (2 - 2 * x0) *
          (2 - 2 * x0)⁻¹ ≤
          (Real.exp 4 * T ^ (4 * sigma * (1 - sigma))) *
            (2 - 2 * sigma)⁻¹ :=
        mul_le_mul hXpow (by simpa only [one_div] using hqInv)
          (inv_nonneg.mpr hqPos.le) (by positivity)
      _ = (Real.exp 4 * (2 - 2 * sigma)⁻¹) *
          T ^ (4 * sigma * (1 - sigma)) := by ring
  have htargetOne := one_le_carlson_target_rpow hsigma hsigmaOne hT
  have hcoefficientNonneg : 0 ≤ Real.exp 4 / (2 - 2 * sigma) := by
    positivity
  have hsum :
      1 + (carlsonMollifierLength sigma T : ℝ) ^ (2 - 2 * x0) /
          (2 - 2 * x0) ≤
        (1 + Real.exp 4 / (2 - 2 * sigma)) *
          T ^ (4 * sigma * (1 - sigma)) := by
    calc
      1 + (carlsonMollifierLength sigma T : ℝ) ^ (2 - 2 * x0) /
          (2 - 2 * x0) ≤
          1 + (Real.exp 4 / (2 - 2 * sigma)) *
            T ^ (4 * sigma * (1 - sigma)) := by
        simpa only [add_comm] using add_le_add_left hXquot 1
      _ ≤ T ^ (4 * sigma * (1 - sigma)) +
          (Real.exp 4 / (2 - 2 * sigma)) *
            T ^ (4 * sigma * (1 - sigma)) :=
        by simpa only [add_comm] using
          add_le_add_right htargetOne
            ((Real.exp 4 / (2 - 2 * sigma)) *
              T ^ (4 * sigma * (1 - sigma)))
      _ = (1 + Real.exp 4 / (2 - 2 * sigma)) *
          T ^ (4 * sigma * (1 - sigma)) := by ring
  have huPow : u ^ (1 - 2 * x0) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu hp
  have htail :
      u ^ (1 - 2 * x0) *
          (1 - (2 : ℝ) ^ (1 - 2 * x0))⁻¹ ≤
        (1 - (2 : ℝ) ^ (1 / 2 - sigma))⁻¹ := by
    calc
      u ^ (1 - 2 * x0) *
          (1 - (2 : ℝ) ^ (1 - 2 * x0))⁻¹ ≤
          1 * (1 - (2 : ℝ) ^ (1 / 2 - sigma))⁻¹ :=
        mul_le_mul huPow hnegativeInv
          (inv_nonneg.mpr hactualNegDenPos.le) (by positivity)
      _ = (1 - (2 : ℝ) ^ (1 / 2 - sigma))⁻¹ := one_mul _
  calc
    (1 + (carlsonMollifierLength sigma T : ℝ) ^ (2 - 2 * x0) /
          (2 - 2 * x0)) *
        (u ^ (1 - 2 * x0) *
          (1 - (2 : ℝ) ^ (1 - 2 * x0))⁻¹) ≤
        ((1 + Real.exp 4 / (2 - 2 * sigma)) *
          T ^ (4 * sigma * (1 - sigma))) *
            (1 - (2 : ℝ) ^ (1 / 2 - sigma))⁻¹ :=
      mul_le_mul hsum htail (by positivity) (by positivity)
    _ = ((1 + Real.exp 4 / (2 - 2 * sigma)) *
          (1 - (2 : ℝ) ^ (1 / 2 - sigma))⁻¹) *
        T ^ (4 * sigma * (1 - sigma)) := by ring

private noncomputable def carlsonAmbientFirstCoefficient (sigma : ℝ) : ℝ :=
  2 * (2 + 1 / (sigma - 1 / 2)) *
    (9 * Real.exp 4 / ((2 : ℝ) ^ (2 - 2 * sigma) - 1) +
      6 * Real.exp 4)

private noncomputable def carlsonAmbientSecondCoefficient (sigma : ℝ) : ℝ :=
  16 * Real.pi * (2 + 1 / (2 - 2 * sigma)) *
    (144 * Real.exp 8 / ((2 : ℝ) ^ (2 - 2 * sigma) - 1))

private noncomputable def carlsonAmbientRemainderCoefficient
    (A sigma : ℝ) : ℝ :=
  4 * ((A + 4) ^ 2 * (1 + 4 * Real.pi)) *
    ((1 + Real.exp 4 / (2 - 2 * sigma)) *
      (1 - (2 : ℝ) ^ (1 / 2 - sigma))⁻¹)

/-- Fixed coefficient obtained after optimizing the mollifier length and
freezing every auxiliary-line denominator at `sigma`. -/
noncomputable def carlsonSharpAmbientCoefficient (A sigma : ℝ) : ℝ :=
  carlsonAmbientFirstCoefficient sigma +
    carlsonAmbientSecondCoefficient sigma +
    carlsonAmbientRemainderCoefficient A sigma

/-- The complete closed Carlson ambient majorant has the desired power of
`T`, with one ambient logarithmic cube and a fixed coefficient. -/
theorem carlsonSharpAmbientMajorant_optimized_le
    {A sigma T x0 u : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1) (hT : 6 ≤ T) (hlog : 0 < Real.log T)
    (hlarge : 4 / Real.log T < sigma - 1 / 2)
    (hpower : 1 ≤ T ^ (2 * sigma - 1))
    (hx0 : 1 / 2 < x0) (hx0One : x0 < 1)
    (hx0Sigma : x0 < sigma) (hgap : sigma - x0 < 2 / Real.log T)
    (hu : 1 ≤ u) :
    carlsonSharpAmbientMajorant A (carlsonAmbientLogCube T)
        (carlsonMollifierLength sigma T) x0 u (2 * (T + 5 / 4)) ≤
      carlsonSharpAmbientCoefficient A sigma * carlsonAmbientLogCube T *
        T ^ (4 * sigma * (1 - sigma)) := by
  have hLone := one_le_carlsonAmbientLogCube hT
  have hL0 : 0 ≤ carlsonAmbientLogCube T := zero_le_one.trans hLone
  have htargetOne := one_le_carlson_target_rpow hsigma hsigmaOne hT
  have htarget0 : 0 ≤ T ^ (4 * sigma * (1 - sigma)) :=
    zero_le_one.trans htargetOne
  have hqPos : 0 < 2 - 2 * x0 := by linarith
  have hpositiveDenPos : 0 < (2 : ℝ) ^ (2 - 2 * x0) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) hqPos)
  have hnegativeDenPos : 0 < 1 - (2 : ℝ) ^ (1 - 2 * x0) :=
    sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hfixedQPos : 0 < 2 - 2 * sigma := by linarith
  have hfixedPositiveDenPos :
      0 < (2 : ℝ) ^ (2 - 2 * sigma) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) hfixedQPos)
  have hfixedNegativeDenPos :
      0 < 1 - (2 : ℝ) ^ (1 / 2 - sigma) :=
    sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  rcases carlson_auxiliary_line_denominator_bounds hsigma hsigmaOne hlog
      hlarge hx0Sigma hgap with ⟨hleftInv, hqInv, _hgeometric, _hnegative⟩
  have hfirst := carlson_ambient_first_bracket_le hsigma hsigmaOne hT hlog
    hlarge hpower hx0 hx0One hx0Sigma hgap
  have hsecond := carlson_ambient_second_bracket_le hsigma hsigmaOne hT hlog
    hlarge hpower hx0 hx0One hx0Sigma hgap
  have hthird := carlson_ambient_remainder_bracket_le hsigma hsigmaOne hT hlog
    hlarge hpower hx0 hx0One hx0Sigma hgap hu
  have hfirstCoefficient :
      2 * carlsonAmbientLogCube T * (2 + 1 / (2 * x0 - 1)) ≤
        2 * carlsonAmbientLogCube T *
          (2 + 1 / (sigma - 1 / 2)) :=
    mul_le_mul_of_nonneg_left
      (by simpa only [add_comm] using add_le_add_left hleftInv 2)
      (mul_nonneg (by norm_num) hL0)
  have hsecondCoefficient :
      16 * Real.pi * carlsonAmbientLogCube T *
          (2 + 1 / (2 - 2 * x0)) ≤
        16 * Real.pi * carlsonAmbientLogCube T *
          (2 + 1 / (2 - 2 * sigma)) :=
    mul_le_mul_of_nonneg_left
      (by simpa only [add_comm] using add_le_add_left hqInv 2) (by positivity)
  have hfourPow : (4 : ℝ) ^ (-2 * x0) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hthirdCoefficient :
      4 * ((A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
          (1 + 4 * Real.pi)) ≤
        4 * ((A + 4) ^ 2 * (1 + 4 * Real.pi)) := by
    have hcore : 0 ≤ (A + 4) ^ 2 * (1 + 4 * Real.pi) := by positivity
    calc
      4 * ((A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
          (1 + 4 * Real.pi)) =
          4 * (((A + 4) ^ 2 * (1 + 4 * Real.pi)) *
            (4 : ℝ) ^ (-2 * x0)) := by ring
      _ ≤ 4 * (((A + 4) ^ 2 * (1 + 4 * Real.pi)) * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hfourPow hcore) (by norm_num)
      _ = 4 * ((A + 4) ^ 2 * (1 + 4 * Real.pi)) := by ring
  have hfirstBracket0 : 0 ≤
      (2 * (T + 5 / 4)) ^ (2 - 2 * x0) /
          ((2 : ℝ) ^ (2 - 2 * x0) - 1) +
        (carlsonMollifierLength sigma T : ℝ) ^ (1 - 2 * x0) *
          (2 * (T + 5 / 4)) := by
    exact add_nonneg
      (div_nonneg (Real.rpow_nonneg (by linarith) _) hpositiveDenPos.le)
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by linarith))
  have hfirstFrozenCoefficient0 : 0 ≤
      2 * carlsonAmbientLogCube T *
        (2 + 1 / (sigma - 1 / 2)) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hL0)
      (add_nonneg (by norm_num) (one_div_nonneg.mpr (by linarith)))
  have hsecondBracket0 : 0 ≤
      (4 * (carlsonMollifierLength sigma T : ℝ) *
          (2 * (T + 5 / 4))) ^ (2 - 2 * x0) /
        ((2 : ℝ) ^ (2 - 2 * x0) - 1) := by
    exact div_nonneg (Real.rpow_nonneg (by positivity) _) hpositiveDenPos.le
  have hsecondFrozenCoefficient0 : 0 ≤
      16 * Real.pi * carlsonAmbientLogCube T *
        (2 + 1 / (2 - 2 * sigma)) := by positivity
  have hfirstTerm :
      (2 * carlsonAmbientLogCube T * (2 + 1 / (2 * x0 - 1))) *
          ((2 * (T + 5 / 4)) ^ (2 - 2 * x0) /
              ((2 : ℝ) ^ (2 - 2 * x0) - 1) +
            (carlsonMollifierLength sigma T : ℝ) ^ (1 - 2 * x0) *
              (2 * (T + 5 / 4))) ≤
        carlsonAmbientFirstCoefficient sigma * carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma)) := by
    calc
      _ ≤ (2 * carlsonAmbientLogCube T *
            (2 + 1 / (sigma - 1 / 2))) *
          ((9 * Real.exp 4 /
              ((2 : ℝ) ^ (2 - 2 * sigma) - 1) + 6 * Real.exp 4) *
            T ^ (4 * sigma * (1 - sigma))) :=
        mul_le_mul hfirstCoefficient hfirst hfirstBracket0
          hfirstFrozenCoefficient0
      _ = carlsonAmbientFirstCoefficient sigma * carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma)) := by
        dsimp [carlsonAmbientFirstCoefficient]
        ring
  have hsecondTerm :
      (16 * Real.pi * carlsonAmbientLogCube T *
          (2 + 1 / (2 - 2 * x0))) *
        ((4 * (carlsonMollifierLength sigma T : ℝ) *
            (2 * (T + 5 / 4))) ^ (2 - 2 * x0) /
          ((2 : ℝ) ^ (2 - 2 * x0) - 1)) ≤
        carlsonAmbientSecondCoefficient sigma * carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma)) := by
    calc
      _ ≤ (16 * Real.pi * carlsonAmbientLogCube T *
            (2 + 1 / (2 - 2 * sigma))) *
          ((144 * Real.exp 8 /
              ((2 : ℝ) ^ (2 - 2 * sigma) - 1)) *
            T ^ (4 * sigma * (1 - sigma))) :=
        mul_le_mul hsecondCoefficient hsecond hsecondBracket0
          hsecondFrozenCoefficient0
      _ = carlsonAmbientSecondCoefficient sigma * carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma)) := by
        dsimp [carlsonAmbientSecondCoefficient]
        ring
  have hthirdBase : 0 ≤
      carlsonAmbientRemainderCoefficient A sigma := by
    dsimp [carlsonAmbientRemainderCoefficient]
    positivity
  have hthirdTerm :
      (4 * ((A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
          (1 + 4 * Real.pi)) *
        (1 + (carlsonMollifierLength sigma T : ℝ) ^ (2 - 2 * x0) /
          (2 - 2 * x0))) *
        (u ^ (1 - 2 * x0) *
          (1 - (2 : ℝ) ^ (1 - 2 * x0))⁻¹) ≤
        carlsonAmbientRemainderCoefficient A sigma *
          carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma)) := by
    calc
      _ = (4 * ((A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
          (1 + 4 * Real.pi))) *
        ((1 + (carlsonMollifierLength sigma T : ℝ) ^ (2 - 2 * x0) /
            (2 - 2 * x0)) *
          (u ^ (1 - 2 * x0) *
            (1 - (2 : ℝ) ^ (1 - 2 * x0))⁻¹)) := by ring
      _ ≤ (4 * ((A + 4) ^ 2 * (1 + 4 * Real.pi))) *
          (((1 + Real.exp 4 / (2 - 2 * sigma)) *
              (1 - (2 : ℝ) ^ (1 / 2 - sigma))⁻¹) *
            T ^ (4 * sigma * (1 - sigma))) :=
        mul_le_mul hthirdCoefficient hthird (by positivity) (by positivity)
      _ = carlsonAmbientRemainderCoefficient A sigma *
          T ^ (4 * sigma * (1 - sigma)) := by
        dsimp [carlsonAmbientRemainderCoefficient]
        ring
      _ ≤ carlsonAmbientRemainderCoefficient A sigma *
          carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma)) := by
        nlinarith [mul_nonneg hthirdBase htarget0,
          mul_nonneg hthirdBase
            (mul_nonneg hL0 htarget0)]
  calc
    carlsonSharpAmbientMajorant A (carlsonAmbientLogCube T)
        (carlsonMollifierLength sigma T) x0 u (2 * (T + 5 / 4)) ≤
      carlsonAmbientFirstCoefficient sigma * carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma)) +
        carlsonAmbientSecondCoefficient sigma * carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma)) +
        carlsonAmbientRemainderCoefficient A sigma *
          carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma)) := by
      exact add_le_add (add_le_add hfirstTerm hsecondTerm) hthirdTerm
    _ = carlsonSharpAmbientCoefficient A sigma * carlsonAmbientLogCube T *
        T ^ (4 * sigma * (1 - sigma)) := by
      dsimp [carlsonSharpAmbientCoefficient]
      ring

/-- The actual geometric cover selected by the Carlson contour has the
optimized fixed-`sigma` growth bound. -/
theorem carlson_parameterized_geometric_cover_optimized_le
    {A sigma T x0 u v : ℝ} {n : ℕ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hT : 6 ≤ T) (hlog : 0 < Real.log T)
    (hlarge : 4 / Real.log T < sigma - 1 / 2)
    (hpower : 1 ≤ T ^ (2 * sigma - 1))
    (hx0 : 1 / 2 < x0) (hx0One : x0 < 1)
    (hx0Sigma : x0 < sigma) (hgap : sigma - x0 < 2 / Real.log T)
    (hu : 1 ≤ u) (hnv : u * (2 : ℝ) ^ n ≤ v)
    (hvn : v ≤ u * (2 : ℝ) ^ (n + 1)) (hvT : v ≤ T + 5 / 4) :
    carlsonSharpGeometricCoverExplicitBound A
        (carlsonMollifierLength sigma T) x0 u v n ≤
      carlsonSharpAmbientCoefficient A sigma * carlsonAmbientLogCube T *
        T ^ (4 * sigma * (1 - sigma)) := by
  exact (carlson_parameterized_geometric_cover_le_ambient
    hsigma hsigmaOne hT hpower hx0 hx0One hu hnv hvn hvT).trans
      (carlsonSharpAmbientMajorant_optimized_le hsigma hsigmaOne hT hlog
        hlarge hpower hx0 hx0One hx0Sigma hgap hu)

/-- Stronger eventual side conditions used to freeze every auxiliary-line
denominator while retaining Carlson's dynamic line-selection certificate. -/
theorem eventually_carlson_optimized_parameter_conditions {sigma : ℝ}
    (hsigma : 1 / 2 < sigma) :
    ∀ᶠ T : ℝ in atTop,
      6 ≤ T ∧ 1 ≤ Real.log T ∧
        4 / Real.log T < sigma - 1 / 2 ∧
        1 ≤ T ^ (2 * sigma - 1) := by
  have hdelta : 0 < sigma - 1 / 2 := sub_pos.mpr hsigma
  have hratio : Tendsto (fun T : ℝ => 4 / Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hsmall : ∀ᶠ T : ℝ in atTop,
      4 / Real.log T < sigma - 1 / 2 :=
    (tendsto_order.1 hratio).2 _ hdelta
  filter_upwards [eventually_ge_atTop (6 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1, hsmall] with T hT hlog hsmallT
  have hTOne : 1 ≤ T := by linarith
  have hexponent : 0 ≤ 2 * sigma - 1 := by linarith
  exact ⟨hT, hlog, hsmallT, Real.one_le_rpow hTOne hexponent⟩

/-- Every logarithmic polynomial entering the selected horizontal-edge
majorant is controlled by one ambient logarithm. -/
theorem carlson_logPolynomial_le_ambientLinear
    {C T S : ℝ} {X : ℕ} (hC : 1 ≤ C) (hCT : C ≤ T)
    (hX : 1 ≤ X) (hXT : (X : ℝ) ≤ T) (hT : 6 ≤ T)
    (hS : 0 ≤ S) (hST : S + 14 ≤ 4 * T) :
    Real.log (C * (X : ℝ) ^ 2 * (S + 14) ^ 10) ≤
      33 * (1 + Real.log (4 * (T + 5 / 4) * T)) := by
  have hTPos : 0 < T := by linarith
  have hXReal : 1 ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : 0 ≤ (X : ℝ) := zero_le_one.trans hXReal
  have hSPos : 0 < S + 14 := by linarith
  have hXsq : (X : ℝ) ^ 2 ≤ T ^ 2 :=
    pow_le_pow_left₀ hX0 hXT 2
  have hSpow : (S + 14) ^ 10 ≤ (4 * T) ^ 10 :=
    pow_le_pow_left₀ hSPos.le hST 10
  have hCX : C * (X : ℝ) ^ 2 ≤ T * T ^ 2 :=
    mul_le_mul hCT hXsq (sq_nonneg _) (by linarith)
  have hpoly : C * (X : ℝ) ^ 2 * (S + 14) ^ 10 ≤
      (4 : ℝ) ^ 10 * T ^ 13 := by
    calc
      C * (X : ℝ) ^ 2 * (S + 14) ^ 10 ≤
          (T * T ^ 2) * (4 * T) ^ 10 :=
        mul_le_mul hCX hSpow (pow_nonneg hSPos.le 10) (by positivity)
      _ = (4 : ℝ) ^ 10 * T ^ 13 := by ring
  have hpolyPos : 0 < C * (X : ℝ) ^ 2 * (S + 14) ^ 10 := by positivity
  have hlogPoly := Real.log_le_log hpolyPos hpoly
  have hlogUpper :
      Real.log ((4 : ℝ) ^ 10 * T ^ 13) =
        10 * Real.log 4 + 13 * Real.log T := by
    rw [Real.log_mul (pow_ne_zero 10 (by norm_num))
      (pow_ne_zero 13 hTPos.ne'), Real.log_pow, Real.log_pow]
    norm_num
  have hQOne : (1 : ℝ) ≤ 4 * (T + 5 / 4) * T := by
    nlinarith [sq_nonneg T]
  have hTQ : T ≤ 4 * (T + 5 / 4) * T := by
    nlinarith [sq_nonneg T]
  have hlogTQ : Real.log T ≤ Real.log (4 * (T + 5 / 4) * T) :=
    Real.log_le_log hTPos hTQ
  have hlogQ0 : 0 ≤ Real.log (4 * (T + 5 / 4) * T) :=
    Real.log_nonneg hQOne
  have hlogFour : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at h ⊢
    exact h
  rw [hlogUpper] at hlogPoly
  nlinarith

/-- Fixed conversion factor from the Jensen logarithmic denominator to the
ambient logarithm. -/
noncomputable def carlsonZeroLogCoefficient : ℝ :=
  33 / Real.log ((31 / 8 : ℝ) / (123 / 32 : ℝ))

/-- The explicit Jensen zero-mass majorant is nonnegative and grows at most
linearly in the ambient logarithm. -/
theorem regularizedCarlsonFactorZeroLogMajorant_bounds
    {C T S : ℝ} {X : ℕ} (hC : 1 ≤ C) (hCT : C ≤ T)
    (hX : 1 ≤ X) (hXT : (X : ℝ) ≤ T) (hT : 6 ≤ T)
    (hS : 0 ≤ S) (hST : S + 14 ≤ 4 * T) :
    0 ≤ regularizedCarlsonFactorZeroLogMajorant C X S ∧
      regularizedCarlsonFactorZeroLogMajorant C X S ≤
        carlsonZeroLogCoefficient *
          (1 + Real.log (4 * (T + 5 / 4) * T)) := by
  have hXReal : 1 ≤ (X : ℝ) := by exact_mod_cast hX
  have hSpow : 1 ≤ (S + 14) ^ 10 := by
    exact one_le_pow₀ (by linarith)
  have hXpow : 1 ≤ (X : ℝ) ^ 2 := one_le_pow₀ hXReal
  have hCX : 1 ≤ C * (X : ℝ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le hC hXpow
  have hpolyOne : 1 ≤ C * (X : ℝ) ^ 2 * (S + 14) ^ 10 :=
    one_le_mul_of_one_le_of_one_le hCX hSpow
  have hdenPos : 0 < Real.log ((31 / 8 : ℝ) / (123 / 32 : ℝ)) :=
    Real.log_pos (by norm_num)
  have hpoly := carlson_logPolynomial_le_ambientLinear
    hC hCT hX hXT hT hS hST
  constructor
  · dsimp [regularizedCarlsonFactorZeroLogMajorant]
    exact div_nonneg (Real.log_nonneg hpolyOne) hdenPos.le
  · dsimp [regularizedCarlsonFactorZeroLogMajorant]
    calc
      Real.log (C * (X : ℝ) ^ 2 * (S + 14) ^ 10) /
          Real.log ((31 / 8 : ℝ) / (123 / 32 : ℝ)) ≤
          (33 * (1 + Real.log (4 * (T + 5 / 4) * T))) /
            Real.log ((31 / 8 : ℝ) / (123 / 32 : ℝ)) :=
        div_le_div_of_nonneg_right hpoly hdenPos.le
      _ = carlsonZeroLogCoefficient *
          (1 + Real.log (4 * (T + 5 / 4) * T)) := by
        dsimp [carlsonZeroLogCoefficient]
        ring

/-- Coarse fixed coefficient for the quadratic logarithmic variation bound
on a selected horizontal side. -/
noncomputable def carlsonHorizontalVariationCoefficient : ℝ :=
  33 + 131 * carlsonZeroLogCoefficient +
    128 * carlsonZeroLogCoefficient ^ 2

/-- The zero-removed factor's explicit logarithmic variation grows at most
quadratically in the ambient logarithm. -/
theorem regularizedCarlsonFactorLogVariationMajorant_le_ambientSquare
    {C₁ C₂ T S : ℝ} {X : ℕ}
    (hC₁ : 1 ≤ C₁) (hC₁T : C₁ ≤ T)
    (hC₂ : 1 ≤ C₂) (hC₂T : C₂ ≤ T)
    (hX : 1 ≤ X) (hXT : (X : ℝ) ≤ T) (hT : 6 ≤ T)
    (hS : 0 ≤ S) (hST : S + 14 ≤ 4 * T) :
    regularizedCarlsonFactorLogVariationMajorant C₁ X S
        (regularizedCarlsonFactorZeroLogMajorant C₂ X S) ≤
      carlsonHorizontalVariationCoefficient *
        (1 + Real.log (4 * (T + 5 / 4) * T)) ^ 2 := by
  let L : ℝ := 1 + Real.log (4 * (T + 5 / 4) * T)
  let Z : ℝ := regularizedCarlsonFactorZeroLogMajorant C₂ X S
  have hQOne : (1 : ℝ) ≤ 4 * (T + 5 / 4) * T := by
    nlinarith [sq_nonneg T]
  have hLone : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg hQOne]
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hK0 : 0 ≤ carlsonZeroLogCoefficient := by
    dsimp [carlsonZeroLogCoefficient]
    exact div_nonneg (by norm_num)
      (Real.log_pos (by norm_num : (1 : ℝ) < (31 / 8) / (123 / 32))).le
  have hZbounds := regularizedCarlsonFactorZeroLogMajorant_bounds
    hC₂ hC₂T hX hXT hT hS hST
  have hZ0 : 0 ≤ Z := by simpa [Z] using hZbounds.1
  have hZ : Z ≤ carlsonZeroLogCoefficient * L := by
    simpa [Z, L] using hZbounds.2
  have hW0 : 0 ≤ carlsonZeroLogCoefficient * L := mul_nonneg hK0 hL0
  have hZsq : Z ^ 2 ≤ (carlsonZeroLogCoefficient * L) ^ 2 :=
    (sq_le_sq₀ hZ0 hW0).2 hZ
  have hpoly :
      Real.log (C₁ * (X : ℝ) ^ 2 * (S + 14) ^ 10) ≤ 33 * L := by
    simpa [L] using carlson_logPolynomial_le_ambientLinear
      hC₁ hC₁T hX hXT hT hS hST
  have hYPos : 0 < 128 * (Z + 1) := by positivity
  have hlogInv :
      -Real.log (1 / (128 * (Z + 1))) = Real.log (128 * (Z + 1)) := by
    rw [one_div, Real.log_inv]
    ring
  have hlogY : Real.log (128 * (Z + 1)) ≤ 128 * (Z + 1) := by
    have h := Real.log_le_sub_one_of_pos hYPos
    linarith
  have hconstant : Real.log (123 / 32 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 123 / 32)
    norm_num at h ⊢
    linarith
  have hfactor :
      Real.log (128 * (Z + 1)) + Real.log (123 / 32 : ℝ) ≤
        128 * (Z + 1) + 3 := by linarith
  have hfactorMul :
      (Real.log (128 * (Z + 1)) + Real.log (123 / 32 : ℝ)) * Z ≤
        (128 * (Z + 1) + 3) * Z :=
    mul_le_mul_of_nonneg_right hfactor hZ0
  calc
    regularizedCarlsonFactorLogVariationMajorant C₁ X S
        (regularizedCarlsonFactorZeroLogMajorant C₂ X S) =
        Real.log (C₁ * (X : ℝ) ^ 2 * (S + 14) ^ 10) +
          (-Real.log (1 / (128 * (Z + 1))) +
            Real.log (123 / 32 : ℝ)) * Z := by
      rfl
    _ = Real.log (C₁ * (X : ℝ) ^ 2 * (S + 14) ^ 10) +
          (Real.log (128 * (Z + 1)) + Real.log (123 / 32 : ℝ)) * Z := by
      rw [hlogInv]
    _ ≤ 33 * L + (128 * (Z + 1) + 3) * Z :=
      add_le_add hpoly hfactorMul
    _ ≤ carlsonHorizontalVariationCoefficient * L ^ 2 := by
      dsimp [carlsonHorizontalVariationCoefficient]
      nlinarith [sq_nonneg L, sq_nonneg carlsonZeroLogCoefficient]
    _ = carlsonHorizontalVariationCoefficient *
        (1 + Real.log (4 * (T + 5 / 4) * T)) ^ 2 := by rfl

/-- Fixed coefficient for the complete explicit horizontal logarithmic-
derivative majorant. -/
noncomputable def carlsonHorizontalMajorantCoefficient : ℝ :=
  4 * (carlsonHorizontalVariationCoefficient + 1) * 7744 +
    4 * carlsonZeroLogCoefficient * (carlsonZeroLogCoefficient + 1)

/-- The complete explicit horizontal logarithmic-derivative majorant is
controlled by the ambient logarithmic cube. -/
theorem regularizedCarlsonHorizontalLogDerivMajorant_le_ambientCube
    {C₁ C₂ T S : ℝ} {X : ℕ}
    (hC₁ : 1 ≤ C₁) (hC₁T : C₁ ≤ T)
    (hC₂ : 1 ≤ C₂) (hC₂T : C₂ ≤ T)
    (hX : 1 ≤ X) (hXT : (X : ℝ) ≤ T) (hT : 6 ≤ T)
    (hS : 0 ≤ S) (hST : S + 14 ≤ 4 * T) :
    regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X S ≤
      carlsonHorizontalMajorantCoefficient * carlsonAmbientLogCube T := by
  let L : ℝ := 1 + Real.log (4 * (T + 5 / 4) * T)
  let Z : ℝ := regularizedCarlsonFactorZeroLogMajorant C₂ X S
  let V : ℝ := regularizedCarlsonFactorLogVariationMajorant C₁ X S Z
  have hQOne : (1 : ℝ) ≤ 4 * (T + 5 / 4) * T := by
    nlinarith [sq_nonneg T]
  have hLone : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg hQOne]
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hLsqOne : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg L]
  have hK0 : 0 ≤ carlsonZeroLogCoefficient := by
    dsimp [carlsonZeroLogCoefficient]
    exact div_nonneg (by norm_num)
      (Real.log_pos (by norm_num : (1 : ℝ) < (31 / 8) / (123 / 32))).le
  have hVcoeff0 : 0 ≤ carlsonHorizontalVariationCoefficient := by
    dsimp [carlsonHorizontalVariationCoefficient]
    positivity
  have hZbounds := regularizedCarlsonFactorZeroLogMajorant_bounds
    hC₂ hC₂T hX hXT hT hS hST
  have hZ0 : 0 ≤ Z := by simpa [Z] using hZbounds.1
  have hZ : Z ≤ carlsonZeroLogCoefficient * L := by
    simpa [Z, L] using hZbounds.2
  have hW0 : 0 ≤ carlsonZeroLogCoefficient * L := mul_nonneg hK0 hL0
  have hZsq : Z ^ 2 ≤ (carlsonZeroLogCoefficient * L) ^ 2 :=
    (sq_le_sq₀ hZ0 hW0).2 hZ
  have hV : V ≤ carlsonHorizontalVariationCoefficient * L ^ 2 := by
    simpa [V, Z, L] using
      regularizedCarlsonFactorLogVariationMajorant_le_ambientSquare
        hC₁ hC₁T hC₂ hC₂T hX hXT hT hS hST
  have hmax : max V 1 ≤
      (carlsonHorizontalVariationCoefficient + 1) * L ^ 2 := by
    apply max_le
    · exact hV.trans (by
        have : 0 ≤ L ^ 2 := sq_nonneg L
        nlinarith)
    · nlinarith [mul_nonneg hVcoeff0 (sq_nonneg L)]
  have hZrational :
      Z / (1 / (4 * (Z + 1))) ≤
        4 * carlsonZeroLogCoefficient *
          (carlsonZeroLogCoefficient + 1) * L ^ 2 := by
    have hdenNe : 4 * (Z + 1) ≠ 0 := by positivity
    have hrewrite : Z / (1 / (4 * (Z + 1))) = 4 * Z * (Z + 1) := by
      field_simp
    rw [hrewrite]
    have hKLsq : carlsonZeroLogCoefficient * L ≤
        carlsonZeroLogCoefficient * L ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg L]) hK0
    nlinarith [sq_nonneg L, sq_nonneg carlsonZeroLogCoefficient]
  have hsquare :
      4 * max V 1 * 7744 + Z / (1 / (4 * (Z + 1))) ≤
        carlsonHorizontalMajorantCoefficient * L ^ 2 := by
    have hmaxScaled := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmax (by norm_num : (0 : ℝ) ≤ 4))
      (by norm_num : (0 : ℝ) ≤ 7744)
    dsimp [carlsonHorizontalMajorantCoefficient]
    nlinarith
  have hcube : L ^ 2 ≤ L ^ 3 := by
    nlinarith [sq_nonneg L, mul_nonneg (sq_nonneg L) hL0]
  have hcoefficient0 : 0 ≤ carlsonHorizontalMajorantCoefficient := by
    dsimp [carlsonHorizontalMajorantCoefficient]
    positivity
  calc
    regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X S =
        4 * max V 1 * 7744 + Z / (1 / (4 * (Z + 1))) := by rfl
    _ ≤ carlsonHorizontalMajorantCoefficient * L ^ 2 := hsquare
    _ ≤ carlsonHorizontalMajorantCoefficient * L ^ 3 :=
      mul_le_mul_of_nonneg_left hcube hcoefficient0
    _ = carlsonHorizontalMajorantCoefficient * carlsonAmbientLogCube T := by
      rfl

/-- All elementary side conditions needed by Carlson's dynamic parameter
certificate hold for sufficiently large height. -/
theorem eventually_carlson_parameter_conditions {sigma : ℝ}
    (hsigma : 1 / 2 < sigma) :
    ∀ᶠ T : ℝ in atTop,
      6 ≤ T ∧ 0 < Real.log T ∧
        2 / Real.log T < sigma - 1 / 2 ∧
        1 ≤ T ^ (2 * sigma - 1) := by
  have hdelta : 0 < sigma - 1 / 2 := sub_pos.mpr hsigma
  have hratio : Tendsto (fun T : ℝ => 2 / Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hsmall : ∀ᶠ T : ℝ in atTop,
      2 / Real.log T < sigma - 1 / 2 :=
    (tendsto_order.1 hratio).2 _ hdelta
  filter_upwards [eventually_ge_atTop (6 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1, hsmall] with T hT hlog hsmallT
  have hTOne : 1 ≤ T := by linarith
  have hexponent : 0 ≤ 2 * sigma - 1 := by linarith
  exact ⟨hT, zero_lt_one.trans_le hlog, hsmallT,
    Real.one_le_rpow hTOne hexponent⟩

/-- The cancelled pre-asymptotic contour certificate with Carlson's dynamic
left window and optimized mollifier length installed.  The selected auxiliary
line lies at distance between `1 / log T` and `2 / log T` from the target
line; dividing the weighted count by that distance is the source of the
fourth logarithm in the final zero-density estimate. -/
theorem exists_carlson_parameterized_count_certificate :
    ∃ A C₁ C₂ : ℝ, 0 ≤ A ∧ 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {sigma T : ℝ},
        1 / 2 < sigma → sigma < 1 → 6 ≤ T →
        0 < Real.log T → 2 / Real.log T < sigma - 1 / 2 →
        ∃ x0 y0 y1 : ℝ, ∃ n : ℕ,
          1 / Real.log T < sigma - x0 ∧
          sigma - x0 < 2 / Real.log T ∧
          1 / 2 < x0 ∧ x0 < sigma ∧ x0 < 4 ∧
          5 ≤ y0 ∧ y0 ≤ 6 ∧
          T < y1 ∧ y1 ≤ T + 5 / 4 ∧ y0 < y1 ∧
          y0 * (2 : ℝ) ^ n ≤ y1 ∧
          y1 ≤ y0 * (2 : ℝ) ^ (n + 1) ∧
          (2 * Real.pi) * (sigma - x0) *
              (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
            (2 * Real.pi) * (sigma - x0) *
                ExplicitFormulaAux.globalZeroMultiplicity 6 +
              carlsonSharpGeometricCoverExplicitBound
                A (carlsonMollifierLength sigma T) x0 y0 y1 n +
              (4 - x0) ^ 2 *
                (regularizedCarlsonHorizontalLogDerivMajorant
                    C₁ C₂ (carlsonMollifierLength sigma T) 5 +
                  regularizedCarlsonHorizontalLogDerivMajorant
                    C₁ C₂ (carlsonMollifierLength sigma T) (T + 1 / 4)) +
              (4 - x0) * (3 * Real.pi) +
              125 / 18 := by
  obtain ⟨A, C₁, C₂, hA, hC₁, hC₂, hcertificate⟩ :=
    exists_regularizedCarlson_fixedRight_count_le_cancelledSharpGeometricCover_add_explicit_boundary_of_leftWindow_constantRight
  refine ⟨A, C₁, C₂, hA, hC₁, hC₂, ?_⟩
  intro sigma T hsigmaHalf hsigmaOne hT hlog hwindow
  let theta := sigma - 2 / Real.log T
  let eta := sigma - 1 / Real.log T
  have hthetaHalf : 1 / 2 < theta := by
    dsimp [theta]
    linarith
  have hthetaEta : theta < eta := by
    dsimp [theta, eta]
    have hinvPos : 0 < 1 / Real.log T := one_div_pos.mpr hlog
    have htwo : 2 / Real.log T = 2 * (1 / Real.log T) := by ring
    rw [htwo]
    linarith
  have hetaSigma : eta ≤ sigma := by
    dsimp [eta]
    have hinvNonneg : 0 ≤ 1 / Real.log T := (one_div_pos.mpr hlog).le
    linarith
  rcases hcertificate
      (one_le_carlsonMollifierLength sigma T)
      hthetaHalf hthetaEta hetaSigma hsigmaOne hT with
    ⟨x0, y0, y1, n,
      hx0Theta, hx0Eta, hx0Sigma, hx04,
      hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
      hnv, hvn, hcount⟩
  refine ⟨x0, y0, y1, n, ?_, ?_, ?_, hx0Sigma, hx04,
    hy0Lower, hy0Upper, hTy1, hy1Upper, hy01, hnv, hvn, hcount⟩
  · dsimp [eta] at hx0Eta
    linarith
  · dsimp [theta] at hx0Theta
    linarith
  · exact hthetaHalf.trans hx0Theta

/-- The ambient logarithmic cube used by the explicit contour estimates is,
up to a fixed factor, the ordinary cube of `log T`. -/
theorem carlsonAmbientLogCube_le_logCube {T : ℝ}
    (hT : 6 ≤ T) (hlog : 1 ≤ Real.log T) :
    carlsonAmbientLogCube T ≤ 125 * (Real.log T) ^ 3 := by
  have hT0 : 0 ≤ T := by linarith
  have hshift : T + 5 / 4 ≤ 2 * T := by linarith
  have harg : 4 * (T + 5 / 4) * T ≤ 8 * T ^ 2 := by
    nlinarith
  have hsquare : 8 ≤ T ^ 2 := by nlinarith [sq_nonneg T]
  have hfourth : 8 * T ^ 2 ≤ T ^ 4 := by
    have hproduct : 0 ≤ (T ^ 2 - 8) * T ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hsquare) (sq_nonneg T)
    nlinarith
  have hargPos : 0 < 4 * (T + 5 / 4) * T := by positivity
  have hlogArg :
      Real.log (4 * (T + 5 / 4) * T) ≤ Real.log (T ^ 4) :=
    Real.log_le_log hargPos (harg.trans hfourth)
  have hbase :
      1 + Real.log (4 * (T + 5 / 4) * T) ≤ 5 * Real.log T := by
    rw [Real.log_pow] at hlogArg
    norm_num at hlogArg
    linarith
  have hbase0 : 0 ≤ 1 + Real.log (4 * (T + 5 / 4) * T) := by
    have hargOne : (1 : ℝ) ≤ 4 * (T + 5 / 4) * T := by
      nlinarith [sq_nonneg T]
    linarith [Real.log_nonneg hargOne]
  dsimp [carlsonAmbientLogCube]
  calc
    (1 + Real.log (4 * (T + 5 / 4) * T)) ^ 3 ≤
        (5 * Real.log T) ^ 3 := pow_le_pow_left₀ hbase0 hbase 3
    _ = 125 * (Real.log T) ^ 3 := by ring

/-- A fixed coefficient absorbing the low zeros, the optimized left edge,
both horizontal edges, and the height-uniform right edge. -/
noncomputable def carlsonFinalCoefficient (A sigma : ℝ) : ℝ :=
  4 * Real.pi * ExplicitFormulaAux.globalZeroMultiplicity 6 +
    carlsonSharpAmbientCoefficient A sigma +
    32 * carlsonHorizontalMajorantCoefficient +
    12 * Real.pi + 125 / 18

theorem zero_le_carlsonSharpAmbientCoefficient {A sigma : ℝ}
    (hA : 0 ≤ A) (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    0 ≤ carlsonSharpAmbientCoefficient A sigma := by
  have hpositiveDen :
      0 < (2 : ℝ) ^ (2 - 2 * sigma) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by linarith))
  have hnegativeDen :
      0 < 1 - (2 : ℝ) ^ (1 / 2 - sigma) :=
    sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hsigmaGap : 0 < sigma - 1 / 2 := by linarith
  have hrightGap : 0 < 2 - 2 * sigma := by linarith
  dsimp [carlsonSharpAmbientCoefficient]
  apply add_nonneg
  · apply add_nonneg
    · dsimp [carlsonAmbientFirstCoefficient]
      positivity
    · dsimp [carlsonAmbientSecondCoefficient]
      positivity
  · dsimp [carlsonAmbientRemainderCoefficient]
    positivity

theorem zero_le_carlsonHorizontalMajorantCoefficient :
    0 ≤ carlsonHorizontalMajorantCoefficient := by
  dsimp [carlsonHorizontalMajorantCoefficient,
    carlsonHorizontalVariationCoefficient, carlsonZeroLogCoefficient]
  positivity

theorem zero_le_carlsonFinalCoefficient {A sigma : ℝ}
    (hA : 0 ≤ A) (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    0 ≤ carlsonFinalCoefficient A sigma := by
  dsimp [carlsonFinalCoefficient]
  apply add_nonneg
  · apply add_nonneg
    · apply add_nonneg
      · apply add_nonneg
        · exact mul_nonneg
            (mul_nonneg (by norm_num) Real.pi_pos.le)
            (ExplicitFormulaAux.globalZeroMultiplicity_nonneg 6)
        · exact zero_le_carlsonSharpAmbientCoefficient hA hsigma hsigmaOne
      · exact mul_nonneg (by norm_num)
          zero_le_carlsonHorizontalMajorantCoefficient
    · positivity
  · norm_num

/-- Carlson's classical fixed-`sigma` zero-density estimate, with zeros
counted according to analytic multiplicity. -/
theorem carlson_zeroDensity_isBigO
    {sigma : ℝ} (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1) :
    (fun T => (ZeroDensity.zeroDensityCount sigma T : ℝ))
      =O[atTop]
    (fun T => T ^ (4 * sigma * (1 - sigma)) * (Real.log T) ^ 4) := by
  obtain ⟨A, C₁, C₂, hA, hC₁, hC₂, hcertificate⟩ :=
    exists_carlson_parameterized_count_certificate
  let K := carlsonFinalCoefficient A sigma
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact zero_le_carlsonFinalCoefficient hA hσ hσ1
  refine Asymptotics.IsBigO.of_bound (125 * K) ?_
  filter_upwards [eventually_carlson_optimized_parameter_conditions hσ,
      eventually_ge_atTop C₁, eventually_ge_atTop C₂] with T hparams hC₁T hC₂T
  rcases hparams with ⟨hT, hlog, hlarge, hpower⟩
  have hlogPos : 0 < Real.log T := zero_lt_one.trans_le hlog
  have hwindow : 2 / Real.log T < sigma - 1 / 2 :=
    (div_lt_div_of_pos_right (by norm_num : (2 : ℝ) < 4) hlogPos).trans hlarge
  rcases hcertificate hσ hσ1 hT hlogPos hwindow with
    ⟨x0, y0, y1, n,
      hgapLower, hgapUpper, hx0Half, hx0Sigma, hx04,
      hy0Lower, _hy0Upper, _hTy1, hy1Upper, _hy01,
      hnv, hvn, hcount⟩
  have hx0One : x0 < 1 := hx0Sigma.trans hσ1
  have hTOne : 1 ≤ T := by linarith
  have hXT : (carlsonMollifierLength sigma T : ℝ) ≤ T :=
    carlsonMollifierLength_le_height hσ hσ1 hTOne hpower
  have hgeom := carlson_parameterized_geometric_cover_optimized_le (A := A)
    hσ hσ1 hT hlogPos hlarge hpower hx0Half hx0One hx0Sigma hgapUpper
      (by linarith) hnv hvn hy1Upper
  have hbottom := regularizedCarlsonHorizontalLogDerivMajorant_le_ambientCube
    hC₁ hC₁T hC₂ hC₂T (one_le_carlsonMollifierLength sigma T) hXT hT
      (by norm_num : (0 : ℝ) ≤ 5) (by linarith)
  have htop := regularizedCarlsonHorizontalLogDerivMajorant_le_ambientCube
    hC₁ hC₁T hC₂ hC₂T (one_le_carlsonMollifierLength sigma T) hXT hT
      (by linarith : 0 ≤ T + 1 / 4) (by linarith)
  have hLone := one_le_carlsonAmbientLogCube hT
  have hL0 : 0 ≤ carlsonAmbientLogCube T := zero_le_one.trans hLone
  have hPone := one_le_carlson_target_rpow hσ hσ1 hT
  have hP0 : 0 ≤ T ^ (4 * sigma * (1 - sigma)) :=
    zero_le_one.trans hPone
  have hLPone :
      1 ≤ carlsonAmbientLogCube T * T ^ (4 * sigma * (1 - sigma)) := by
    nlinarith [mul_nonneg hL0 hP0]
  have hgapTwo : sigma - x0 ≤ 2 := by
    have htwoDiv : 2 / Real.log T ≤ 2 := by
      rw [div_le_iff₀ hlogPos]
      nlinarith
    exact hgapUpper.le.trans htwoDiv
  have hglobal0 :
      0 ≤ ExplicitFormulaAux.globalZeroMultiplicity 6 :=
    ExplicitFormulaAux.globalZeroMultiplicity_nonneg 6
  have hlow :
      (2 * Real.pi) * (sigma - x0) *
          ExplicitFormulaAux.globalZeroMultiplicity 6 ≤
        (4 * Real.pi * ExplicitFormulaAux.globalZeroMultiplicity 6) *
          (carlsonAmbientLogCube T *
            T ^ (4 * sigma * (1 - sigma))) := by
    have hfirst :
        (2 * Real.pi) * (sigma - x0) *
            ExplicitFormulaAux.globalZeroMultiplicity 6 ≤
          4 * Real.pi * ExplicitFormulaAux.globalZeroMultiplicity 6 := by
      have hpi : (2 * Real.pi) * (sigma - x0) ≤ 4 * Real.pi := by
        nlinarith [Real.pi_pos]
      exact mul_le_mul_of_nonneg_right hpi hglobal0
    have hcoefficient0 :
        0 ≤ 4 * Real.pi * ExplicitFormulaAux.globalZeroMultiplicity 6 := by
      positivity
    exact hfirst.trans (by
      calc
        _ = (4 * Real.pi * ExplicitFormulaAux.globalZeroMultiplicity 6) * 1 :=
          by ring
        _ ≤ (4 * Real.pi * ExplicitFormulaAux.globalZeroMultiplicity 6) *
            (carlsonAmbientLogCube T *
              T ^ (4 * sigma * (1 - sigma))) :=
          mul_le_mul_of_nonneg_left hLPone hcoefficient0)
  have hsquare : (4 - x0) ^ 2 ≤ 16 := by
    have hfour0 : 0 ≤ 4 - x0 := sub_nonneg.mpr hx04.le
    have hfour : 4 - x0 ≤ 4 := by linarith [hx0Half]
    convert pow_le_pow_left₀ hfour0 hfour 2 using 1 <;> norm_num
  have hhorizontalSum :
      regularizedCarlsonHorizontalLogDerivMajorant
            C₁ C₂ (carlsonMollifierLength sigma T) 5 +
          regularizedCarlsonHorizontalLogDerivMajorant
            C₁ C₂ (carlsonMollifierLength sigma T) (T + 1 / 4) ≤
        2 * carlsonHorizontalMajorantCoefficient *
          carlsonAmbientLogCube T := by
    linarith
  have hhorizontal :
      (4 - x0) ^ 2 *
          (regularizedCarlsonHorizontalLogDerivMajorant
              C₁ C₂ (carlsonMollifierLength sigma T) 5 +
            regularizedCarlsonHorizontalLogDerivMajorant
              C₁ C₂ (carlsonMollifierLength sigma T) (T + 1 / 4)) ≤
        (32 * carlsonHorizontalMajorantCoefficient) *
          (carlsonAmbientLogCube T *
            T ^ (4 * sigma * (1 - sigma))) := by
    have hH0 := zero_le_carlsonHorizontalMajorantCoefficient
    by_cases hsum0 : 0 ≤
        regularizedCarlsonHorizontalLogDerivMajorant
              C₁ C₂ (carlsonMollifierLength sigma T) 5 +
            regularizedCarlsonHorizontalLogDerivMajorant
              C₁ C₂ (carlsonMollifierLength sigma T) (T + 1 / 4)
    · have hfirst := mul_le_mul hsquare hhorizontalSum hsum0
          (by norm_num : (0 : ℝ) ≤ 16)
      have hscale0 : 0 ≤ 32 * carlsonHorizontalMajorantCoefficient *
          carlsonAmbientLogCube T := by positivity
      calc
        _ ≤ 32 * carlsonHorizontalMajorantCoefficient *
              carlsonAmbientLogCube T := by
            convert hfirst using 1 <;> ring
        _ ≤ (32 * carlsonHorizontalMajorantCoefficient) *
              (carlsonAmbientLogCube T *
                T ^ (4 * sigma * (1 - sigma))) := by
            calc
              _ = (32 * carlsonHorizontalMajorantCoefficient *
                  carlsonAmbientLogCube T) * 1 := by ring
              _ ≤ (32 * carlsonHorizontalMajorantCoefficient *
                  carlsonAmbientLogCube T) *
                    T ^ (4 * sigma * (1 - sigma)) :=
                mul_le_mul_of_nonneg_left hPone hscale0
              _ = _ := by ring
    · have hleftNonpos :
          (4 - x0) ^ 2 *
              (regularizedCarlsonHorizontalLogDerivMajorant
                  C₁ C₂ (carlsonMollifierLength sigma T) 5 +
                regularizedCarlsonHorizontalLogDerivMajorant
                  C₁ C₂ (carlsonMollifierLength sigma T) (T + 1 / 4)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_not_ge hsum0)
      exact hleftNonpos.trans (by positivity)
  have hboundary :
      (4 - x0) * (3 * Real.pi) + 125 / 18 ≤
        (12 * Real.pi + 125 / 18) *
          (carlsonAmbientLogCube T *
            T ^ (4 * sigma * (1 - sigma))) := by
    have hbasic :
        (4 - x0) * (3 * Real.pi) + 125 / 18 ≤
          12 * Real.pi + 125 / 18 := by
      have hfour : 4 - x0 ≤ 4 := by linarith [hx0Half]
      have hthreePi0 : 0 ≤ 3 * Real.pi := by positivity
      have hmul : (4 - x0) * (3 * Real.pi) ≤ 4 * (3 * Real.pi) :=
        mul_le_mul_of_nonneg_right hfour hthreePi0
      calc
        _ ≤ 4 * (3 * Real.pi) + 125 / 18 :=
          add_le_add hmul le_rfl
        _ = _ := by ring
    have hcoefficient0 : 0 ≤ 12 * Real.pi + 125 / 18 := by positivity
    exact hbasic.trans (by
      calc
        _ = (12 * Real.pi + 125 / 18) * 1 := by ring
        _ ≤ (12 * Real.pi + 125 / 18) *
            (carlsonAmbientLogCube T *
              T ^ (4 * sigma * (1 - sigma))) :=
          mul_le_mul_of_nonneg_left hLPone hcoefficient0)
  have hweighted :
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        K * (carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma))) := by
    have hgeom' :
        carlsonSharpGeometricCoverExplicitBound A
            (carlsonMollifierLength sigma T) x0 y0 y1 n ≤
          carlsonSharpAmbientCoefficient A sigma *
            (carlsonAmbientLogCube T *
              T ^ (4 * sigma * (1 - sigma))) := by
      simpa only [mul_assoc] using hgeom
    calc
      _ ≤ (2 * Real.pi) * (sigma - x0) *
              ExplicitFormulaAux.globalZeroMultiplicity 6 +
            carlsonSharpGeometricCoverExplicitBound A
              (carlsonMollifierLength sigma T) x0 y0 y1 n +
            (4 - x0) ^ 2 *
              (regularizedCarlsonHorizontalLogDerivMajorant
                  C₁ C₂ (carlsonMollifierLength sigma T) 5 +
                regularizedCarlsonHorizontalLogDerivMajorant
                  C₁ C₂ (carlsonMollifierLength sigma T) (T + 1 / 4)) +
            ((4 - x0) * (3 * Real.pi) + 125 / 18) := by
          convert hcount using 1 <;> ring
      _ ≤ (4 * Real.pi * ExplicitFormulaAux.globalZeroMultiplicity 6) *
              (carlsonAmbientLogCube T *
                T ^ (4 * sigma * (1 - sigma))) +
            (carlsonSharpAmbientCoefficient A sigma) *
              (carlsonAmbientLogCube T *
                T ^ (4 * sigma * (1 - sigma))) +
            (32 * carlsonHorizontalMajorantCoefficient) *
              (carlsonAmbientLogCube T *
                T ^ (4 * sigma * (1 - sigma))) +
            (12 * Real.pi + 125 / 18) *
              (carlsonAmbientLogCube T *
                T ^ (4 * sigma * (1 - sigma))) :=
          add_le_add (add_le_add (add_le_add hlow hgeom') hhorizontal) hboundary
      _ = K * (carlsonAmbientLogCube T *
            T ^ (4 * sigma * (1 - sigma))) := by
          dsimp [K, carlsonFinalCoefficient]
          ring
  have hN0 : 0 ≤ (ZeroDensity.zeroDensityCount sigma T : ℝ) :=
    Nat.cast_nonneg _
  have hgap0 : 0 ≤ sigma - x0 := sub_nonneg.mpr hx0Sigma.le
  have hgapN0 : 0 ≤ (sigma - x0) *
      (ZeroDensity.zeroDensityCount sigma T : ℝ) := mul_nonneg hgap0 hN0
  have hpiOne : 1 ≤ 2 * Real.pi := by
    nlinarith only [Real.pi_gt_three]
  have hgapCount :
      (sigma - x0) * (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        K * (carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma))) := by
    apply (show (sigma - x0) *
        (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
          (2 * Real.pi) * (sigma - x0) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ) by
      calc
        _ = 1 * ((sigma - x0) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) := by ring
        _ ≤ (2 * Real.pi) * ((sigma - x0) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) :=
          mul_le_mul_of_nonneg_right hpiOne hgapN0
        _ = _ := by ring).trans
    exact hweighted
  have hgapLog : 1 < (sigma - x0) * Real.log T :=
    (div_lt_iff₀ hlogPos).mp hgapLower
  have hcountScale :
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        Real.log T * ((sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ)) := by
    calc
      _ = 1 * (ZeroDensity.zeroDensityCount sigma T : ℝ) := by ring
      _ ≤ ((sigma - x0) * Real.log T) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) :=
        mul_le_mul_of_nonneg_right hgapLog.le hN0
      _ = _ := by ring
  have hambientCount :
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        K * carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma)) * Real.log T := by
    calc
      _ ≤ Real.log T * ((sigma - x0) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) := hcountScale
      _ ≤ Real.log T *
            (K * (carlsonAmbientLogCube T *
              T ^ (4 * sigma * (1 - sigma)))) :=
        mul_le_mul_of_nonneg_left hgapCount hlogPos.le
      _ = _ := by ring
  have hlogCube := carlsonAmbientLogCube_le_logCube hT hlog
  have hscale0 :
      0 ≤ K * T ^ (4 * sigma * (1 - sigma)) * Real.log T := by
    positivity
  have hfinal :
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        (125 * K) *
          (T ^ (4 * sigma * (1 - sigma)) * (Real.log T) ^ 4) := by
    calc
      _ ≤ K * carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma)) * Real.log T := hambientCount
      _ = carlsonAmbientLogCube T *
          (K * T ^ (4 * sigma * (1 - sigma)) * Real.log T) := by ring
      _ ≤ (125 * (Real.log T) ^ 3) *
          (K * T ^ (4 * sigma * (1 - sigma)) * Real.log T) :=
        mul_le_mul_of_nonneg_right hlogCube hscale0
      _ = (125 * K) *
          (T ^ (4 * sigma * (1 - sigma)) * (Real.log T) ^ 4) := by ring
  have htarget0 : 0 ≤
      T ^ (4 * sigma * (1 - sigma)) * (Real.log T) ^ 4 := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hN0,
    abs_of_nonneg htarget0] using hfinal

end CarlsonZeroDensity
end PrimeNumberTheorem
