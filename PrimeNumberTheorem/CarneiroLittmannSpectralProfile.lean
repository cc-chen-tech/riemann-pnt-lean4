import PrimeNumberTheorem.TriangleFourierKernel

open Complex MeasureTheory Set

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- The unit translation phase in the standard `-2 * pi * I` Fourier
convention. -/
noncomputable def carneiroLittmannSpectralPhase (u : ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi * u : ℝ) : ℂ) * Complex.I)

private noncomputable def carneiroLittmannSpectralLeft (u : ℝ) : ℂ :=
  carneiroLittmannSpectralPhase u * (1 + u) +
    (carneiroLittmannSpectralPhase u - 1) /
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I)

private noncomputable def carneiroLittmannSpectralRight (u : ℝ) : ℂ :=
  carneiroLittmannSpectralPhase u * (1 - u) -
    (carneiroLittmannSpectralPhase u - 1) /
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I)

/-- Compact spectral profile whose standard Fourier transform will recover
the Carneiro--Littmann derivative. -/
noncomputable def carneiroLittmannSpectralProfile (u : ℝ) : ℂ :=
  if u ≤ -1 then 0
  else if u ≤ 0 then carneiroLittmannSpectralLeft u
  else if u ≤ 1 then carneiroLittmannSpectralRight u
  else 0

private theorem carneiroLittmannSpectralPhase_neg_one :
    carneiroLittmannSpectralPhase (-1) = 1 := by
  unfold carneiroLittmannSpectralPhase
  rw [show (((-2 * Real.pi * (-1 : ℝ) : ℝ) : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * Complex.I by
    push_cast
    ring]
  exact Complex.exp_two_pi_mul_I

@[simp] theorem carneiroLittmannSpectralPhase_zero :
    carneiroLittmannSpectralPhase 0 = 1 := by
  simp [carneiroLittmannSpectralPhase]

private theorem carneiroLittmannSpectralPhase_one :
    carneiroLittmannSpectralPhase 1 = 1 := by
  unfold carneiroLittmannSpectralPhase
  rw [show (((-2 * Real.pi * (1 : ℝ) : ℝ) : ℂ) * Complex.I) =
      -(2 * (Real.pi : ℂ) * Complex.I) by
    push_cast
    ring]
  rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

private theorem carneiroLittmannSpectralLeft_neg_one :
    carneiroLittmannSpectralLeft (-1) = 0 := by
  simp [carneiroLittmannSpectralLeft,
    carneiroLittmannSpectralPhase_neg_one]

private theorem carneiroLittmannSpectralLeft_zero :
    carneiroLittmannSpectralLeft 0 = 1 := by
  simp [carneiroLittmannSpectralLeft]

private theorem carneiroLittmannSpectralRight_zero :
    carneiroLittmannSpectralRight 0 = 1 := by
  simp [carneiroLittmannSpectralRight]

private theorem carneiroLittmannSpectralRight_one :
    carneiroLittmannSpectralRight 1 = 0 := by
  simp [carneiroLittmannSpectralRight,
    carneiroLittmannSpectralPhase_one]

private theorem continuous_carneiroLittmannSpectralPhase :
    Continuous carneiroLittmannSpectralPhase := by
  unfold carneiroLittmannSpectralPhase
  fun_prop

private theorem continuous_carneiroLittmannSpectralLeft :
    Continuous carneiroLittmannSpectralLeft := by
  unfold carneiroLittmannSpectralLeft carneiroLittmannSpectralPhase
  fun_prop

private theorem continuous_carneiroLittmannSpectralRight :
    Continuous carneiroLittmannSpectralRight := by
  unfold carneiroLittmannSpectralRight carneiroLittmannSpectralPhase
  fun_prop

theorem continuous_carneiroLittmannSpectralProfile :
    Continuous carneiroLittmannSpectralProfile := by
  have hRightPiece : Continuous (fun u : ℝ =>
      if u ≤ 1 then carneiroLittmannSpectralRight u else 0) := by
    exact continuous_if_le continuous_id continuous_const
      continuous_carneiroLittmannSpectralRight.continuousOn
      continuous_const.continuousOn (by
        intro u hu
        subst u
        exact carneiroLittmannSpectralRight_one)
  have hMiddlePiece : Continuous (fun u : ℝ =>
      if u ≤ 0 then carneiroLittmannSpectralLeft u
      else if u ≤ 1 then carneiroLittmannSpectralRight u else 0) := by
    exact continuous_if_le continuous_id continuous_const
      continuous_carneiroLittmannSpectralLeft.continuousOn
      hRightPiece.continuousOn (by
        intro u hu
        subst u
        norm_num
        rw [carneiroLittmannSpectralLeft_zero,
          carneiroLittmannSpectralRight_zero])
  unfold carneiroLittmannSpectralProfile
  exact continuous_if_le continuous_id continuous_const
    continuous_const.continuousOn hMiddlePiece.continuousOn (by
      intro u hu
      subst u
      norm_num
      exact carneiroLittmannSpectralLeft_neg_one.symm)

theorem carneiroLittmannSpectralProfile_eq_zero_of_one_le_abs
    {u : ℝ} (hu : 1 ≤ |u|) :
    carneiroLittmannSpectralProfile u = 0 := by
  rcases (le_abs.mp hu) with hu | hu
  · by_cases huOne : u = 1
    · subst u
      simp [carneiroLittmannSpectralProfile,
        carneiroLittmannSpectralRight_one]
    · have huGtOne : 1 < u := lt_of_le_of_ne hu (Ne.symm huOne)
      have huNotNegOne : ¬u ≤ -1 := not_le.mpr (by linarith)
      have huNotZero : ¬u ≤ 0 := not_le.mpr (by linarith)
      have huNotOne : ¬u ≤ 1 := not_le.mpr huGtOne
      simp [carneiroLittmannSpectralProfile, huNotNegOne, huNotZero,
        huNotOne]
  · have huNeg : u ≤ -1 := by linarith
    simp [carneiroLittmannSpectralProfile, huNeg]

theorem hasCompactSupport_carneiroLittmannSpectralProfile :
    HasCompactSupport carneiroLittmannSpectralProfile := by
  apply HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc
  intro u hu
  simp only [Set.mem_Icc, not_and_or, not_le] at hu
  apply carneiroLittmannSpectralProfile_eq_zero_of_one_le_abs
  rcases hu with hu | hu
  · rw [abs_of_neg (hu.trans_le (by norm_num))]
    linarith
  · rw [abs_of_pos ((by norm_num : (0 : ℝ) < 1).trans hu)]
    linarith

theorem integrable_carneiroLittmannSpectralProfile :
    Integrable carneiroLittmannSpectralProfile :=
  continuous_carneiroLittmannSpectralProfile.integrable_of_hasCompactSupport
    hasCompactSupport_carneiroLittmannSpectralProfile

end DirichletPolynomial
end PrimeNumberTheorem
