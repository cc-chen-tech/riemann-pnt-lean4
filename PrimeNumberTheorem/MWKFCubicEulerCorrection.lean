import PrimeNumberTheorem.MWKFCubicEulerLocalFactor

open Complex

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The quadratic cancellation in the cubic Euler correction

The local correction factor equals one to first order because its numerator
has an exact quadratic cancellation.  This file isolates that algebraic fact;
it also proves a uniform prime-local strip bound, but does not yet sum over
primes or construct the infinite Euler product.
-/

/-- After subtracting one, the local correction factor has an explicitly
quadratic numerator.  This is the exact cancellation behind the later
`O(p^(-2+δ))` estimate. -/
theorem mwkfPrimeCorrectionFactor_sub_one
    {p : ℕ} {s t w : ℂ}
    (hsw : 1 - (p : ℂ) ^ (-(1 + s + w)) ≠ 0)
    (htw : 1 - (p : ℂ) ^ (-(1 + t + w)) ≠ 0) :
    mwkfPrimeCorrectionFactor p s t w - 1 =
      (((p : ℂ) ^ (-(1 + s + w))) *
          ((p : ℂ) ^ (-(1 + s + t))) +
        ((p : ℂ) ^ (-(1 + t + w))) *
          ((p : ℂ) ^ (-(1 + s + t))) -
        ((p : ℂ) ^ (-(1 + s + t))) ^ 2 -
        ((p : ℂ) ^ (-(1 + s + w))) *
          ((p : ℂ) ^ (-(1 + t + w)))) /
      ((1 - (p : ℂ) ^ (-(1 + s + w))) *
        (1 - (p : ℂ) ^ (-(1 + t + w)))) := by
  let A : ℂ := (p : ℂ) ^ (-(1 + s + w))
  let B : ℂ := (p : ℂ) ^ (-(1 + t + w))
  let C : ℂ := (p : ℂ) ^ (-(1 + s + t))
  have hA : 1 - A ≠ 0 := by simpa [A] using hsw
  have hB : 1 - B ≠ 0 := by simpa [B] using htw
  have hAB : (1 - A) * (1 - B) ≠ 0 := mul_ne_zero hA hB
  change ((1 - A - B + C) * (1 - C) / ((1 - A) * (1 - B))) - 1 =
    (A * C + B * C - C ^ 2 - A * B) / ((1 - A) * (1 - B))
  field_simp [hAB]
  ring

/-- The exact quadratic cancellation gives a norm bound with no hidden
constant and with the two local denominators left visible. -/
theorem norm_mwkfPrimeCorrectionFactor_sub_one_le
    {p : ℕ} {s t w : ℂ}
    (hsw : 1 - (p : ℂ) ^ (-(1 + s + w)) ≠ 0)
    (htw : 1 - (p : ℂ) ^ (-(1 + t + w)) ≠ 0) :
    ‖mwkfPrimeCorrectionFactor p s t w - 1‖ ≤
      (‖(p : ℂ) ^ (-(1 + s + w))‖ *
          ‖(p : ℂ) ^ (-(1 + s + t))‖ +
        ‖(p : ℂ) ^ (-(1 + t + w))‖ *
          ‖(p : ℂ) ^ (-(1 + s + t))‖ +
        ‖(p : ℂ) ^ (-(1 + s + t))‖ ^ 2 +
        ‖(p : ℂ) ^ (-(1 + s + w))‖ *
          ‖(p : ℂ) ^ (-(1 + t + w))‖) /
      (‖1 - (p : ℂ) ^ (-(1 + s + w))‖ *
        ‖1 - (p : ℂ) ^ (-(1 + t + w))‖) := by
  let A : ℂ := (p : ℂ) ^ (-(1 + s + w))
  let B : ℂ := (p : ℂ) ^ (-(1 + t + w))
  let C : ℂ := (p : ℂ) ^ (-(1 + s + t))
  rw [mwkfPrimeCorrectionFactor_sub_one hsw htw]
  change ‖(A * C + B * C - C ^ 2 - A * B) / ((1 - A) * (1 - B))‖ ≤
    (‖A‖ * ‖C‖ + ‖B‖ * ‖C‖ + ‖C‖ ^ 2 + ‖A‖ * ‖B‖) /
      (‖1 - A‖ * ‖1 - B‖)
  rw [norm_div, norm_mul]
  apply div_le_div_of_nonneg_right _
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    ‖A * C + B * C - C ^ 2 - A * B‖ ≤
        ‖A * C + B * C - C ^ 2‖ + ‖A * B‖ := norm_sub_le _ _
    _ ≤ (‖A * C + B * C‖ + ‖C ^ 2‖) + ‖A * B‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ ((‖A * C‖ + ‖B * C‖) + ‖C ^ 2‖) + ‖A * B‖ := by
      gcongr
      exact norm_add_le _ _
    _ = ‖A‖ * ‖C‖ + ‖B‖ * ‖C‖ + ‖C‖ ^ 2 + ‖A‖ * ‖B‖ := by
      rw [norm_mul, norm_mul, norm_pow, norm_mul]

/-- A uniform fixed-constant form of the quadratic local estimate.  Once the
three prime powers have norm at most `r < 1`, the correction differs from one
by at most `4 * r^2 / (1-r)^2`. -/
theorem norm_mwkfPrimeCorrectionFactor_sub_one_le_of_norm_le
    {p : ℕ} {s t w : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hrOne : r < 1)
    (hsw : ‖(p : ℂ) ^ (-(1 + s + w))‖ ≤ r)
    (htw : ‖(p : ℂ) ^ (-(1 + t + w))‖ ≤ r)
    (hst : ‖(p : ℂ) ^ (-(1 + s + t))‖ ≤ r) :
    ‖mwkfPrimeCorrectionFactor p s t w - 1‖ ≤
      4 * r ^ 2 / (1 - r) ^ 2 := by
  let A : ℂ := (p : ℂ) ^ (-(1 + s + w))
  let B : ℂ := (p : ℂ) ^ (-(1 + t + w))
  let C : ℂ := (p : ℂ) ^ (-(1 + s + t))
  have hA : ‖A‖ ≤ r := by simpa [A] using hsw
  have hB : ‖B‖ ≤ r := by simpa [B] using htw
  have hC : ‖C‖ ≤ r := by simpa [C] using hst
  have hAden : 1 - A ≠ 0 := by
    intro h
    have hAOne : A = 1 := (sub_eq_zero.mp h).symm
    have : (1 : ℝ) ≤ r := by simpa [hAOne] using hA
    exact (not_le_of_gt hrOne) this
  have hBden : 1 - B ≠ 0 := by
    intro h
    have hBOne : B = 1 := (sub_eq_zero.mp h).symm
    have : (1 : ℝ) ≤ r := by simpa [hBOne] using hB
    exact (not_le_of_gt hrOne) this
  have hAC : ‖A‖ * ‖C‖ ≤ r ^ 2 := by
    nlinarith [norm_nonneg A, norm_nonneg C]
  have hBC : ‖B‖ * ‖C‖ ≤ r ^ 2 := by
    nlinarith [norm_nonneg B, norm_nonneg C]
  have hCC : ‖C‖ ^ 2 ≤ r ^ 2 := by
    nlinarith [norm_nonneg C]
  have hAB : ‖A‖ * ‖B‖ ≤ r ^ 2 := by
    nlinarith [norm_nonneg A, norm_nonneg B]
  have hnum :
      ‖A‖ * ‖C‖ + ‖B‖ * ‖C‖ + ‖C‖ ^ 2 + ‖A‖ * ‖B‖ ≤
        4 * r ^ 2 := by
    linarith
  have hAlo : 1 - r ≤ ‖1 - A‖ := by
    calc
      1 - r ≤ 1 - ‖A‖ := sub_le_sub_left hA 1
      _ = ‖(1 : ℂ)‖ - ‖A‖ := by simp
      _ ≤ ‖(1 : ℂ) - A‖ := norm_sub_norm_le _ _
  have hBlo : 1 - r ≤ ‖1 - B‖ := by
    calc
      1 - r ≤ 1 - ‖B‖ := sub_le_sub_left hB 1
      _ = ‖(1 : ℂ)‖ - ‖B‖ := by simp
      _ ≤ ‖(1 : ℂ) - B‖ := norm_sub_norm_le _ _
  have hrNonneg : 0 ≤ 1 - r := sub_nonneg.mpr hrOne.le
  have hden : (1 - r) ^ 2 ≤ ‖1 - A‖ * ‖1 - B‖ := by
    rw [pow_two]
    exact mul_le_mul hAlo hBlo hrNonneg (norm_nonneg _)
  calc
    ‖mwkfPrimeCorrectionFactor p s t w - 1‖ ≤
        (‖A‖ * ‖C‖ + ‖B‖ * ‖C‖ + ‖C‖ ^ 2 + ‖A‖ * ‖B‖) /
          (‖1 - A‖ * ‖1 - B‖) := by
      simpa [A, B, C] using
        (norm_mwkfPrimeCorrectionFactor_sub_one_le hAden hBden)
    _ ≤ (4 * r ^ 2) / (‖1 - A‖ * ‖1 - B‖) :=
      div_le_div_of_nonneg_right hnum
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ 4 * r ^ 2 / (1 - r) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos (sub_pos.mpr hrOne)) hden

/-- On a real-part strip, a positive prime power is bounded by the
corresponding real power with the worst permitted exponent. -/
theorem norm_prime_cpow_neg_one_add_le
    {p : ℕ} (hp : p.Prime) {u v : ℂ} {eta : ℝ}
    (hu : -eta ≤ u.re) (hv : -eta ≤ v.re) :
    ‖(p : ℂ) ^ (-(1 + u + v))‖ ≤
      (p : ℝ) ^ (-1 + 2 * eta) := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hp.one_le
  · simp only [neg_re, add_re, one_re]
    linarith

/-- Explicit prime-local quadratic decay on the symmetric real-part strip
`Re(s), Re(t), Re(w) ≥ -eta`, valid for `eta < 1/2`. -/
theorem norm_mwkfPrimeCorrectionFactor_sub_one_le_on_strip
    {p : ℕ} (hp : p.Prime) {s t w : ℂ} {eta : ℝ}
    (hetaHalf : eta < 1 / 2)
    (hs : -eta ≤ s.re) (ht : -eta ≤ t.re) (hw : -eta ≤ w.re) :
    ‖mwkfPrimeCorrectionFactor p s t w - 1‖ ≤
      4 * ((p : ℝ) ^ (-1 + 2 * eta)) ^ 2 /
        (1 - (p : ℝ) ^ (-1 + 2 * eta)) ^ 2 := by
  have hpReal : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hexponent : -1 + 2 * eta < 0 := by linarith
  apply norm_mwkfPrimeCorrectionFactor_sub_one_le_of_norm_le
  · exact Real.rpow_nonneg (by positivity) _
  · exact Real.rpow_lt_one_of_one_lt_of_neg hpReal hexponent
  · exact norm_prime_cpow_neg_one_add_le hp hs hw
  · exact norm_prime_cpow_neg_one_add_le hp ht hw
  · exact norm_prime_cpow_neg_one_add_le hp hs ht

/-- At the center of the Selberg--Perron expansion every prime-local
correction factor is exactly one. -/
theorem mwkfPrimeCorrectionFactor_zero
    {p : ℕ} (hp : p.Prime) :
    mwkfPrimeCorrectionFactor p 0 0 0 = 1 := by
  have hpOne : (p : ℂ) ≠ 1 := by exact_mod_cast hp.ne_one
  have hden : 1 - (p : ℂ)⁻¹ ≠ 0 := by
    intro h
    have hinv : (p : ℂ)⁻¹ = 1 := (sub_eq_zero.mp h).symm
    apply hpOne
    calc
      (p : ℂ) = ((p : ℂ)⁻¹)⁻¹ := by simp
      _ = 1 := by rw [hinv, inv_one]
  unfold mwkfPrimeCorrectionFactor mwkfPrimeLocalFactorStandard
  simp only [add_zero, Complex.cpow_neg_one]
  field_simp [hden]
  ring

end PrimeNumberTheorem.MWKFCubic
