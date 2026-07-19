import HardyTheorem.HardyPhaseFullSecondMoment

open Complex MeasureTheory

#check HardyTheorem.integral_normSq_sum_hardyPhaseShortIntegral_eq_diagonal_add_offDiagonal
#check HardyTheorem.integral_normSq_sum_hardyPhaseShortIntegral_le_diagonal_add_offDiagonal_norm

example (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0)
    {T delta : ℝ} (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hroom : delta ≤ T) :
    (∫ t in T..2 * T - delta,
      Complex.normSq
        (∑ n ∈ s, coeff n *
          HardyTheorem.OscillatoryIntegral.hardyPhaseShortIntegral n delta t)) =
      (∑ n ∈ s, Complex.normSq (coeff n) *
        ∫ t in T..2 * T - delta,
          Complex.normSq
            (HardyTheorem.OscillatoryIntegral.hardyPhaseShortIntegral n delta t)) +
      (∫ w in 0..delta, ∫ v in 0..delta,
        ∫ t in T..2 * T - delta,
          HardyTheorem.hardyPhaseCorrelationOffDiagonal s coeff v w t).re :=
  HardyTheorem.integral_normSq_sum_hardyPhaseShortIntegral_eq_diagonal_add_offDiagonal
    s coeff hpositive hT hdelta hroom

example (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0)
    {T delta : ℝ} (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hroom : delta ≤ T) :
    (∫ t in T..2 * T - delta,
      Complex.normSq
        (∑ n ∈ s, coeff n *
          HardyTheorem.OscillatoryIntegral.hardyPhaseShortIntegral n delta t)) ≤
      (∑ n ∈ s, Complex.normSq (coeff n) *
        ∫ t in T..2 * T - delta,
          Complex.normSq
            (HardyTheorem.OscillatoryIntegral.hardyPhaseShortIntegral n delta t)) +
      ‖∫ w in 0..delta, ∫ v in 0..delta,
        ∫ t in T..2 * T - delta,
          HardyTheorem.hardyPhaseCorrelationOffDiagonal s coeff v w t‖ :=
  HardyTheorem.integral_normSq_sum_hardyPhaseShortIntegral_le_diagonal_add_offDiagonal_norm
    s coeff hpositive hT hdelta hroom

#print axioms HardyTheorem.integral_normSq_sum_hardyPhaseShortIntegral_eq_diagonal_add_offDiagonal
#print axioms HardyTheorem.integral_normSq_sum_hardyPhaseShortIntegral_le_diagonal_add_offDiagonal_norm
