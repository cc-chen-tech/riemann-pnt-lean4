import Mathlib

/-!
# Carlson endpoint minimax

This module isolates the real-variable optimization in Carlson's classical
two-endpoint zero-density argument.  It proves that changing only the
mollifier length cannot improve the exponent `4 * σ * (1 - σ)`.
-/

namespace PrimeNumberTheorem

/-- The exponent contributed by Carlson's lower endpoint when `X = T^x`. -/
def carlsonLowerEndpointExponent (σ x : ℝ) : ℝ :=
  1 + x * (1 - 2 * σ)

/-- The exponent contributed by Carlson's upper endpoint when `X = T^x`. -/
def carlsonUpperEndpointExponent (σ x : ℝ) : ℝ :=
  (1 + x) * (2 - 2 * σ)

/-- The length exponent at which Carlson's two endpoint exponents balance. -/
def carlsonEndpointBalance (σ : ℝ) : ℝ :=
  2 * σ - 1

/-- Carlson's optimized classical density exponent. -/
def carlsonEndpointOptimum (σ : ℝ) : ℝ :=
  4 * σ * (1 - σ)

/-- The two endpoint exponents differ by the signed displacement from the
balance point. -/
theorem carlson_endpoint_difference (σ x : ℝ) :
    carlsonLowerEndpointExponent σ x - carlsonUpperEndpointExponent σ x =
      carlsonEndpointBalance σ - x := by
  simp only [carlsonLowerEndpointExponent, carlsonUpperEndpointExponent,
    carlsonEndpointBalance]
  ring

/-- Both endpoint exponents equal the classical optimum at the balance
length. -/
theorem carlson_endpoints_at_balance (σ : ℝ) :
    carlsonLowerEndpointExponent σ (carlsonEndpointBalance σ) =
        carlsonEndpointOptimum σ ∧
      carlsonUpperEndpointExponent σ (carlsonEndpointBalance σ) =
        carlsonEndpointOptimum σ := by
  simp only [carlsonLowerEndpointExponent, carlsonUpperEndpointExponent,
    carlsonEndpointBalance, carlsonEndpointOptimum]
  constructor <;> ring

/-- For `1/2 < σ < 1`, no real mollifier-length exponent improves the
maximum of Carlson's two endpoint exponents. -/
theorem carlson_endpoint_max_ge_optimum {σ x : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    carlsonEndpointOptimum σ ≤
      max (carlsonLowerEndpointExponent σ x)
        (carlsonUpperEndpointExponent σ x) := by
  by_cases hx : x ≤ carlsonEndpointBalance σ
  · have hslope : 1 - 2 * σ < 0 := by linarith
    have hmul := mul_le_mul_of_nonpos_right hx hslope.le
    calc
      carlsonEndpointOptimum σ =
          carlsonLowerEndpointExponent σ (carlsonEndpointBalance σ) :=
        (carlson_endpoints_at_balance σ).1.symm
      _ ≤ carlsonLowerEndpointExponent σ x := by
        simpa only [carlsonLowerEndpointExponent, add_comm] using
          add_le_add_left hmul 1
      _ ≤ max (carlsonLowerEndpointExponent σ x)
          (carlsonUpperEndpointExponent σ x) := le_max_left _ _
  · have hx' : carlsonEndpointBalance σ ≤ x := (not_le.mp hx).le
    have hslope : 0 < 2 - 2 * σ := by linarith
    have hadd : 1 + carlsonEndpointBalance σ ≤ 1 + x := by
      simpa only [add_comm] using add_le_add_left hx' 1
    have hmul := mul_le_mul_of_nonneg_right hadd hslope.le
    calc
      carlsonEndpointOptimum σ =
          carlsonUpperEndpointExponent σ (carlsonEndpointBalance σ) :=
        (carlson_endpoints_at_balance σ).2.symm
      _ ≤ carlsonUpperEndpointExponent σ x := by
        simpa only [carlsonUpperEndpointExponent] using hmul
      _ ≤ max (carlsonLowerEndpointExponent σ x)
          (carlsonUpperEndpointExponent σ x) := le_max_right _ _

/-- The balance length is the unique minimizer of the maximum endpoint
exponent. -/
theorem carlson_endpoint_max_eq_optimum_iff {σ x : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    max (carlsonLowerEndpointExponent σ x)
          (carlsonUpperEndpointExponent σ x) = carlsonEndpointOptimum σ ↔
      x = carlsonEndpointBalance σ := by
  constructor
  · intro hmax
    by_contra hx
    rcases lt_or_gt_of_ne hx with hxlt | hxgt
    · have hslope : 1 - 2 * σ < 0 := by linarith
      have hmul := mul_lt_mul_of_neg_right hxlt hslope
      have hstrict : carlsonEndpointOptimum σ <
          carlsonLowerEndpointExponent σ x := by
        rw [← (carlson_endpoints_at_balance σ).1]
        simpa only [carlsonLowerEndpointExponent, add_comm] using
          add_lt_add_left hmul 1
      have hle : carlsonLowerEndpointExponent σ x ≤
          carlsonEndpointOptimum σ := by
        calc
          carlsonLowerEndpointExponent σ x ≤
              max (carlsonLowerEndpointExponent σ x)
                (carlsonUpperEndpointExponent σ x) := le_max_left _ _
          _ = carlsonEndpointOptimum σ := hmax
      exact (not_lt_of_ge hle) hstrict
    · have hslope : 0 < 2 - 2 * σ := by linarith
      have hadd : 1 + carlsonEndpointBalance σ < 1 + x := by
        simpa only [add_comm] using add_lt_add_left hxgt 1
      have hmul := mul_lt_mul_of_pos_right hadd hslope
      have hstrict : carlsonEndpointOptimum σ <
          carlsonUpperEndpointExponent σ x := by
        rw [← (carlson_endpoints_at_balance σ).2]
        simpa only [carlsonUpperEndpointExponent] using hmul
      have hle : carlsonUpperEndpointExponent σ x ≤
          carlsonEndpointOptimum σ := by
        calc
          carlsonUpperEndpointExponent σ x ≤
              max (carlsonLowerEndpointExponent σ x)
                (carlsonUpperEndpointExponent σ x) := le_max_right _ _
          _ = carlsonEndpointOptimum σ := hmax
      exact (not_lt_of_ge hle) hstrict
  · rintro rfl
    rw [(carlson_endpoints_at_balance σ).1,
      (carlson_endpoints_at_balance σ).2, max_self]

/-- At `σ = 2/3`, Carlson's endpoint lines are `1 - x/3` and
`2/3 + 2x/3`. -/
theorem carlson_twoThirds_endpoint_formulas (x : ℝ) :
    carlsonLowerEndpointExponent (2 / 3) x = 1 - x / 3 ∧
      carlsonUpperEndpointExponent (2 / 3) x = 2 / 3 + 2 * x / 3 := by
  simp only [carlsonLowerEndpointExponent, carlsonUpperEndpointExponent]
  constructor <;> norm_num <;> ring

/-- At `σ = 2/3`, the unique optimal length is `x = 1/3` and the
minimized maximum exponent is `8/9`. -/
theorem carlson_twoThirds_length_minimax (x : ℝ) :
    8 / 9 ≤ max (carlsonLowerEndpointExponent (2 / 3) x)
      (carlsonUpperEndpointExponent (2 / 3) x) ∧
    (max (carlsonLowerEndpointExponent (2 / 3) x)
          (carlsonUpperEndpointExponent (2 / 3) x) = 8 / 9 ↔ x = 1 / 3) := by
  have hσ : (1 / 2 : ℝ) < 2 / 3 := by norm_num
  have hσ1 : (2 / 3 : ℝ) < 1 := by norm_num
  have hopt : carlsonEndpointOptimum (2 / 3 : ℝ) = 8 / 9 := by
    norm_num [carlsonEndpointOptimum]
  have hbalance : carlsonEndpointBalance (2 / 3 : ℝ) = 1 / 3 := by
    norm_num [carlsonEndpointBalance]
  constructor
  · simpa [hopt] using (carlson_endpoint_max_ge_optimum hσ hσ1 :
      carlsonEndpointOptimum (2 / 3 : ℝ) ≤
        max (carlsonLowerEndpointExponent (2 / 3) x)
          (carlsonUpperEndpointExponent (2 / 3) x))
  · simpa [hopt, hbalance] using
      (carlson_endpoint_max_eq_optimum_iff hσ hσ1 :
        max (carlsonLowerEndpointExponent (2 / 3) x)
            (carlsonUpperEndpointExponent (2 / 3) x) =
              carlsonEndpointOptimum (2 / 3) ↔
          x = carlsonEndpointBalance (2 / 3))

/-! ## Endpoint estimates with fixed power savings -/

/-- A fixed power saving `δL` in Carlson's lower endpoint estimate. -/
def carlsonSavedLowerEndpointExponent (σ δL x : ℝ) : ℝ :=
  carlsonLowerEndpointExponent σ x - δL

/-- A fixed power saving `δU` in Carlson's upper endpoint estimate. -/
def carlsonSavedUpperEndpointExponent (σ δU x : ℝ) : ℝ :=
  carlsonUpperEndpointExponent σ x - δU

/-- The new balance length after fixed savings at both endpoints. -/
def carlsonSavedBalance (σ δL δU : ℝ) : ℝ :=
  2 * σ - 1 - δL + δU

/-- The optimized endpoint exponent after fixed savings `δL` and `δU`. -/
def carlsonSavedOptimum (σ δL δU : ℝ) : ℝ :=
  4 * σ * (1 - σ) - 2 * (1 - σ) * δL - (2 * σ - 1) * δU

/-- The saved endpoint difference still measures displacement from their
new balance point. -/
theorem carlson_saved_endpoint_difference (σ δL δU x : ℝ) :
    carlsonSavedLowerEndpointExponent σ δL x -
        carlsonSavedUpperEndpointExponent σ δU x =
      carlsonSavedBalance σ δL δU - x := by
  simp only [carlsonSavedLowerEndpointExponent,
    carlsonSavedUpperEndpointExponent, carlsonSavedBalance,
    carlsonLowerEndpointExponent, carlsonUpperEndpointExponent]
  ring

/-- Both saved endpoint lines equal the claimed new optimum at their
intersection. -/
theorem carlson_saved_endpoints_at_balance (σ δL δU : ℝ) :
    carlsonSavedLowerEndpointExponent σ δL
          (carlsonSavedBalance σ δL δU) =
        carlsonSavedOptimum σ δL δU ∧
      carlsonSavedUpperEndpointExponent σ δU
          (carlsonSavedBalance σ δL δU) =
        carlsonSavedOptimum σ δL δU := by
  simp only [carlsonSavedLowerEndpointExponent,
    carlsonSavedUpperEndpointExponent, carlsonSavedBalance,
    carlsonSavedOptimum, carlsonLowerEndpointExponent,
    carlsonUpperEndpointExponent]
  constructor <;> ring

/-- Fixed endpoint savings shift the balance and lower the minimax value by
the exact weighted combination in `carlsonSavedOptimum`. -/
theorem carlson_saved_endpoint_max_ge_optimum {σ δL δU x : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    carlsonSavedOptimum σ δL δU ≤
      max (carlsonSavedLowerEndpointExponent σ δL x)
        (carlsonSavedUpperEndpointExponent σ δU x) := by
  by_cases hx : x ≤ carlsonSavedBalance σ δL δU
  · have hslope : 1 - 2 * σ < 0 := by linarith
    have hmul := mul_le_mul_of_nonpos_right hx hslope.le
    calc
      carlsonSavedOptimum σ δL δU =
          carlsonSavedLowerEndpointExponent σ δL
            (carlsonSavedBalance σ δL δU) :=
        (carlson_saved_endpoints_at_balance σ δL δU).1.symm
      _ ≤ carlsonSavedLowerEndpointExponent σ δL x := by
        simp only [carlsonSavedLowerEndpointExponent,
          carlsonLowerEndpointExponent]
        linarith
      _ ≤ max (carlsonSavedLowerEndpointExponent σ δL x)
          (carlsonSavedUpperEndpointExponent σ δU x) := le_max_left _ _
  · have hx' : carlsonSavedBalance σ δL δU ≤ x := (not_le.mp hx).le
    have hslope : 0 < 2 - 2 * σ := by linarith
    have hadd : 1 + carlsonSavedBalance σ δL δU ≤ 1 + x := by
      linarith
    have hmul := mul_le_mul_of_nonneg_right hadd hslope.le
    calc
      carlsonSavedOptimum σ δL δU =
          carlsonSavedUpperEndpointExponent σ δU
            (carlsonSavedBalance σ δL δU) :=
        (carlson_saved_endpoints_at_balance σ δL δU).2.symm
      _ ≤ carlsonSavedUpperEndpointExponent σ δU x := by
        simp only [carlsonSavedUpperEndpointExponent,
          carlsonUpperEndpointExponent]
        linarith
      _ ≤ max (carlsonSavedLowerEndpointExponent σ δL x)
          (carlsonSavedUpperEndpointExponent σ δU x) := le_max_right _ _

/-- The shifted balance is the unique optimizer after fixed endpoint
savings. -/
theorem carlson_saved_endpoint_max_eq_optimum_iff {σ δL δU x : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    max (carlsonSavedLowerEndpointExponent σ δL x)
          (carlsonSavedUpperEndpointExponent σ δU x) =
        carlsonSavedOptimum σ δL δU ↔
      x = carlsonSavedBalance σ δL δU := by
  constructor
  · intro hmax
    by_contra hx
    rcases lt_or_gt_of_ne hx with hxlt | hxgt
    · have hslope : 1 - 2 * σ < 0 := by linarith
      have hmul := mul_lt_mul_of_neg_right hxlt hslope
      have hstrict : carlsonSavedOptimum σ δL δU <
          carlsonSavedLowerEndpointExponent σ δL x := by
        rw [← (carlson_saved_endpoints_at_balance σ δL δU).1]
        simp only [carlsonSavedLowerEndpointExponent,
          carlsonLowerEndpointExponent]
        linarith
      have hle : carlsonSavedLowerEndpointExponent σ δL x ≤
          carlsonSavedOptimum σ δL δU := by
        calc
          carlsonSavedLowerEndpointExponent σ δL x ≤
              max (carlsonSavedLowerEndpointExponent σ δL x)
                (carlsonSavedUpperEndpointExponent σ δU x) := le_max_left _ _
          _ = carlsonSavedOptimum σ δL δU := hmax
      exact (not_lt_of_ge hle) hstrict
    · have hslope : 0 < 2 - 2 * σ := by linarith
      have hadd : 1 + carlsonSavedBalance σ δL δU < 1 + x := by
        linarith
      have hmul := mul_lt_mul_of_pos_right hadd hslope
      have hstrict : carlsonSavedOptimum σ δL δU <
          carlsonSavedUpperEndpointExponent σ δU x := by
        rw [← (carlson_saved_endpoints_at_balance σ δL δU).2]
        simp only [carlsonSavedUpperEndpointExponent,
          carlsonUpperEndpointExponent]
        linarith
      have hle : carlsonSavedUpperEndpointExponent σ δU x ≤
          carlsonSavedOptimum σ δL δU := by
        calc
          carlsonSavedUpperEndpointExponent σ δU x ≤
              max (carlsonSavedLowerEndpointExponent σ δL x)
                (carlsonSavedUpperEndpointExponent σ δU x) := le_max_right _ _
          _ = carlsonSavedOptimum σ δL δU := hmax
      exact (not_lt_of_ge hle) hstrict
  · rintro rfl
    rw [(carlson_saved_endpoints_at_balance σ δL δU).1,
      (carlson_saved_endpoints_at_balance σ δL δU).2, max_self]

/-- At `σ = 2/3`, fixed endpoint savings enter with weights `2/3` and
`1/3`. -/
theorem carlson_twoThirds_saved_optimum (δL δU : ℝ) :
    carlsonSavedOptimum (2 / 3) δL δU =
      8 / 9 - (2 / 3) * δL - (1 / 3) * δU := by
  norm_num [carlsonSavedOptimum]

end PrimeNumberTheorem
