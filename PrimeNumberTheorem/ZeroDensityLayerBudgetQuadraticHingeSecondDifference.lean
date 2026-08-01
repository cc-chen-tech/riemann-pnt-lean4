import PrimeNumberTheorem.ZeroDensityLayerBudgetCubicExplicitFormula

namespace PrimeNumberTheorem

/-- The scalar quadratic hinge underlying the von Mangoldt second Riesz mean. -/
noncomputable def quadraticHinge (q : ℝ) : ℝ :=
  (max q 0) ^ 2 / 2

/-- Unnormalized second forward difference of the quadratic hinge. -/
noncomputable def quadraticHingeSecondDifferenceNumerator (q h : ℝ) : ℝ :=
  quadraticHinge (q + 2 * h) - 2 * quadraticHinge (q + h) + quadraticHinge q

theorem quadraticHingeSecondDifferenceNumerator_bounds
    {q h : ℝ} (hh : 0 < h) :
    0 ≤ quadraticHingeSecondDifferenceNumerator q h ∧
      quadraticHingeSecondDifferenceNumerator q h ≤ h ^ 2 := by
  by_cases hq : 0 ≤ q
  · have hqh : 0 ≤ q + h := by linarith
    have hq2h : 0 ≤ q + 2 * h := by linarith
    simp only [quadraticHingeSecondDifferenceNumerator, quadraticHinge,
      max_eq_left hq, max_eq_left hqh, max_eq_left hq2h]
    constructor <;> nlinarith
  · have hqneg : q < 0 := lt_of_not_ge hq
    by_cases hqh : 0 ≤ q + h
    · have hq2h : 0 ≤ q + 2 * h := by linarith
      simp only [quadraticHingeSecondDifferenceNumerator, quadraticHinge,
        max_eq_right hqneg.le, max_eq_left hqh, max_eq_left hq2h]
      constructor
      · nlinarith [sq_nonneg (q + h), sq_nonneg q]
      · nlinarith [sq_nonneg q]
    · have hqhneg : q + h < 0 := lt_of_not_ge hqh
      by_cases hq2h : 0 ≤ q + 2 * h
      · simp only [quadraticHingeSecondDifferenceNumerator, quadraticHinge,
          max_eq_right hqneg.le, max_eq_right hqhneg.le, max_eq_left hq2h]
        constructor
        · nlinarith [sq_nonneg (q + 2 * h)]
        · have hsum : 0 ≤ q + 3 * h := by linarith
          have hprod : (q + h) * (q + 3 * h) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hqhneg.le hsum
          nlinarith
      · have hq2hneg : q + 2 * h < 0 := lt_of_not_ge hq2h
        simp [quadraticHingeSecondDifferenceNumerator, quadraticHinge,
          max_eq_right hqneg.le, max_eq_right hqhneg.le, max_eq_right hq2hneg.le,
          sq_nonneg h]

theorem quadraticHingeSecondDifferenceNumerator_eq_sq_of_nonneg
    {q h : ℝ} (hq : 0 ≤ q) (hh : 0 ≤ h) :
    quadraticHingeSecondDifferenceNumerator q h = h ^ 2 := by
  have hqh : 0 ≤ q + h := by linarith
  have hq2h : 0 ≤ q + 2 * h := by linarith
  simp only [quadraticHingeSecondDifferenceNumerator, quadraticHinge,
    max_eq_left hq, max_eq_left hqh, max_eq_left hq2h]
  ring

theorem quadraticHingeSecondDifferenceNumerator_eq_zero_of_add_two_mul_nonpos
    {q h : ℝ} (hq2h : q + 2 * h ≤ 0) (hh : 0 ≤ h) :
    quadraticHingeSecondDifferenceNumerator q h = 0 := by
  have hqh : q + h ≤ 0 := by linarith
  have hq : q ≤ 0 := by linarith
  simp [quadraticHingeSecondDifferenceNumerator, quadraticHinge,
    max_eq_right hq, max_eq_right hqh, max_eq_right hq2h]

/-- Normalized second-difference kernel. -/
noncomputable def normalizedQuadraticHingeSecondDifference (q h : ℝ) : ℝ :=
  quadraticHingeSecondDifferenceNumerator q h / h ^ 2

theorem normalizedQuadraticHingeSecondDifference_mem_unitInterval
    {q h : ℝ} (hh : 0 < h) :
    0 ≤ normalizedQuadraticHingeSecondDifference q h ∧
      normalizedQuadraticHingeSecondDifference q h ≤ 1 := by
  have hb := quadraticHingeSecondDifferenceNumerator_bounds (q := q) hh
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  constructor
  · exact div_nonneg hb.1 hh2.le
  · exact (div_le_one₀ hh2).2 hb.2

theorem normalizedQuadraticHingeSecondDifference_eq_one_of_nonneg
    {q h : ℝ} (hq : 0 ≤ q) (hhpos : 0 ≤ h) (hh : h ≠ 0) :
    normalizedQuadraticHingeSecondDifference q h = 1 := by
  rw [normalizedQuadraticHingeSecondDifference,
    quadraticHingeSecondDifferenceNumerator_eq_sq_of_nonneg hq hhpos,
    div_self (pow_ne_zero 2 hh)]

theorem normalizedQuadraticHingeSecondDifference_eq_zero_of_add_two_mul_nonpos
    {q h : ℝ} (hq2h : q + 2 * h ≤ 0) (hh : 0 ≤ h) :
    normalizedQuadraticHingeSecondDifference q h = 0 := by
  rw [normalizedQuadraticHingeSecondDifference,
    quadraticHingeSecondDifferenceNumerator_eq_zero_of_add_two_mul_nonpos hq2h hh,
    zero_div]

end PrimeNumberTheorem
