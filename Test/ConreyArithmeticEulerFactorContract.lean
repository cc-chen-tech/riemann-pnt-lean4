import HardyTheorem.ConreyArithmeticEulerFactor

namespace HardyTheorem

example {p : ℝ} {a : ℂ} (hp : 2 ≤ p) (ha : ‖a‖ ≤ 1 / 8) :
    (1 / 4 : ℝ) ≤ ‖1 - (p : ℂ)⁻¹ * Complex.exp (-a * (Real.log p : ℂ))‖ :=
  conreyArithmeticDenominator_norm_ge hp ha

example {p : ℝ} {a b : ℂ} (hp : 2 ≤ p)
    (ha : ‖a‖ ≤ 1 / 8) (hb : ‖b‖ ≤ 1 / 8) :
    conreyArithmeticEulerFactor p a b - 1 =
      -((p : ℂ)⁻¹ ^ 2) * (1 - Complex.exp (-a * (Real.log p : ℂ))) *
        (1 - Complex.exp (-b * (Real.log p : ℂ))) /
        ((1 - (p : ℂ)⁻¹ * Complex.exp (-a * (Real.log p : ℂ))) *
         (1 - (p : ℂ)⁻¹ * Complex.exp (-b * (Real.log p : ℂ)))) :=
  conreyArithmeticEulerFactor_sub_one hp ha hb

-- This literal expression retains both distinct shifts and the p^-1
-- normalization. A missing sign, missing p^-1, or single-shift error bound
-- cannot satisfy the quadratic contract, including either zero shift.
example {p : ℝ} {a b : ℂ} (hp : 2 ≤ p)
    (ha : ‖a‖ ≤ 1 / 8) (hb : ‖b‖ ≤ 1 / 8) :
    ‖(1 - (p : ℂ)⁻¹) *
      (1 + (p : ℂ)⁻¹ *
        ((1 - (p : ℂ)⁻¹ * Complex.exp (-(a + b) * (Real.log p : ℂ))) /
          ((1 - (p : ℂ)⁻¹ * Complex.exp (-a * (Real.log p : ℂ))) *
           (1 - (p : ℂ)⁻¹ * Complex.exp (-b * (Real.log p : ℂ)))))) - 1‖ ≤
      16 * ‖a‖ * ‖b‖ * Real.log p ^ 2 * Real.exp (-(7 / 4 : ℝ) * Real.log p) :=
  norm_conreyArithmeticEulerFactor_sub_one_le hp ha hb

example {p : ℝ} {b : ℂ} (hp : 2 ≤ p) (hb : ‖b‖ ≤ 1 / 8) :
    conreyArithmeticEulerFactor p 0 b = 1 := by
  have h := conreyArithmeticEulerFactor_sub_one hp (by norm_num : ‖(0 : ℂ)‖ ≤ 1 / 8) hb
  apply sub_eq_zero.mp
  simpa using h

example {p : ℝ} {a : ℂ} (hp : 2 ≤ p) (ha : ‖a‖ ≤ 1 / 8) :
    conreyArithmeticEulerFactor p a 0 = 1 := by
  have h := conreyArithmeticEulerFactor_sub_one hp ha (by norm_num : ‖(0 : ℂ)‖ ≤ 1 / 8)
  apply sub_eq_zero.mp
  simpa using h

#print axioms conreyArithmeticDenominator_norm_ge
#print axioms conreyArithmeticEulerFactor_sub_one
#print axioms norm_conreyArithmeticEulerFactor_sub_one_le

end HardyTheorem
