import HardyTheorem.OscillatoryIntegral

open Complex MeasureTheory Set

example {F : ℝ → ℝ} {a b m p : ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hm : 0 < m) (hp : 0 < p)
    (hF : ContDiff ℝ 2 F)
    (hmono : MonotoneOn (deriv F) (Icc a b) ∨
      AntitoneOn (deriv F) (Icc a b))
    (haway : ∀ x ∈ Icc a b, m ≤ |deriv F x|) :
    ‖∫ x in a..b, x ^ (-p) • Complex.exp (I * F x)‖ ≤
      4 * a ^ (-p) / m :=
  HardyTheorem.OscillatoryIntegral.norm_integral_rpow_smul_cexp_phase_le_of_monotone_deriv
    hab ha hm hp hF hmono haway

example {a b t p : ℝ} (hab : a ≤ b) (ha : 0 < a) (hp : 0 < p)
    (ht : |t| ≤ a) (k : ℤ) (hk : k ≠ 0) :
    ‖∫ x in a..b, x ^ (-p) •
        Complex.exp (I * (2 * Real.pi * (k : ℝ) * x - t * Real.log x))‖ ≤
      4 * a ^ (-p) / ((2 * Real.pi - 1) * |(k : ℝ)|) :=
  by
    simpa [HardyTheorem.OscillatoryIntegral.fourierMellinPhase] using
      HardyTheorem.OscillatoryIntegral.norm_integral_rpow_smul_cexp_fourierMellinPhase_le
        hab ha hp ht k hk

example {a b t p : ℝ} (hab : a ≤ b) (ha : 0 < a) (hp : 0 < p)
    (ht : 0 ≤ t) (k : ℤ)
    (hgap : 0 < t / b - 2 * Real.pi * (k : ℝ)) :
    ‖∫ x in a..b, x ^ (-p) •
        Complex.exp (I * (2 * Real.pi * (k : ℝ) * x - t * Real.log x))‖ ≤
      4 * a ^ (-p) / (t / b - 2 * Real.pi * (k : ℝ)) := by
  simpa [HardyTheorem.OscillatoryIntegral.fourierMellinPhase] using
    HardyTheorem.OscillatoryIntegral.norm_integral_rpow_smul_cexp_fourierMellinPhase_le_of_stationary_right
        hab ha hp ht k hgap

example {a b t p : ℝ} (hab : a ≤ b) (ha : 0 < a) (hp : 0 < p)
    (ht : 0 ≤ t) (k : ℤ)
    (hgap : 0 < 2 * Real.pi * (k : ℝ) - t / a) :
    ‖∫ x in a..b, x ^ (-p) •
        Complex.exp (I * (2 * Real.pi * (k : ℝ) * x - t * Real.log x))‖ ≤
      4 * a ^ (-p) / (2 * Real.pi * (k : ℝ) - t / a) := by
  simpa [HardyTheorem.OscillatoryIntegral.fourierMellinPhase] using
    HardyTheorem.OscillatoryIntegral.norm_integral_rpow_smul_cexp_fourierMellinPhase_le_of_stationary_left
        hab ha hp ht k hgap

#print axioms HardyTheorem.OscillatoryIntegral.norm_integral_rpow_smul_cexp_fourierMellinPhase_le_of_stationary_right
#print axioms HardyTheorem.OscillatoryIntegral.norm_integral_rpow_smul_cexp_fourierMellinPhase_le_of_stationary_left
