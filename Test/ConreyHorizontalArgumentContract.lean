import HardyTheorem.ConreyV1HorizontalArgument

open Complex Set MeasureTheory HardyTheorem

/-! These contracts forbid a hidden separation assumption on zero ordinates,
and forbid replacing an already selected height by a new existential height. -/

example (a b t : ℝ) (rho : ℂ) :
    IntervalIntegrable (fun x : ℝ => (((x : ℂ) + I * t - rho)⁻¹).im) volume a b :=
  intervalIntegrable_im_inv_horizontal_sub

example (a b t : ℝ) (rho : ℂ) :
    (∫ x in a..b, |(((x : ℂ) + I * t - rho)⁻¹).im|) ≤ Real.pi :=
  integral_abs_im_inv_horizontal_sub_le_pi_all_heights

example (P : Finset ℂ) (m : ℂ → ℝ) {a b t : ℝ} (hab : a ≤ b)
    (hm : ∀ rho ∈ P, 0 ≤ m rho) :
    |∫ x in a..b, ∑ rho ∈ P, m rho *
      (((x : ℂ) + I * t - rho)⁻¹).im| ≤ Real.pi * ∑ rho ∈ P, m rho :=
  abs_integral_finset_principalParts_le P m hab hm

example {P : ℝ → ℝ} (hP0 : P 0 = 0) (hP1 : P 1 = 1) (sigma0 : ℝ) (s : ℂ) :
    conreyMollifier 2 sigma0 P s = 1 :=
  conreyMollifier_two hP0 hP1 sigma0 s

example : ∃ L0 : ℝ, 40000 ≤ L0 ∧ ∀ {L U t : ℝ}, L0 ≤ L →
    2 * Real.log L + 1 ≤ U → U + 1 ≤ Real.exp L → t ∈ Icc U (U + 1) →
    (∀ x ∈ Icc (1 / 2 : ℝ) (2 * Real.log L),
      conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L ((x : ℂ) + I * t) ≠ 0) →
    |∫ x in (1 / 2 : ℝ)..2 * Real.log L,
      (logDeriv (conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L)
        ((x : ℂ) + I * t)).im| ≤ 1100000000000 * L ^ 7 :=
  exists_conreyV1_horizontalArgument_le_coarse

#print axioms exists_conreyV1_horizontalArgument_le_coarse
#print axioms conreyMollifier_two
#print axioms intervalIntegrable_im_inv_horizontal_sub
#print axioms integral_abs_im_inv_horizontal_sub_le_pi_all_heights
#print axioms abs_integral_finset_principalParts_le
