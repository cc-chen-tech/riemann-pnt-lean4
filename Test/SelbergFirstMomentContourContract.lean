import HardyTheorem.SelbergFirstMomentContour

open Complex MeasureTheory Set
open scoped Interval

namespace HardyTheorem

example (X : ℕ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    MathlibAux.boundaryRectIntegral (selbergFirstMomentAuxiliary X)
      (1 / 2) 2 a b = 0 :=
  boundaryRectIntegral_selbergFirstMomentAuxiliary_eq_zero X ha hab

example (X : ℕ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b,
        selbergFirstMomentAuxiliary X ((1 / 2 : ℂ) + I * t)) =
      (∫ t in a..b,
        selbergFirstMomentAuxiliary X ((2 : ℂ) + I * t)) +
      I * ((∫ sigma in (1 / 2 : ℝ)..2,
          selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * b)) -
        (∫ sigma in (1 / 2 : ℝ)..2,
          selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * a))) :=
  intervalIntegral_selbergFirstMomentAuxiliary_criticalLine_eq_right_add_horizontal
    X ha hab

example {X : ℕ} (hX : 2 ≤ X) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (b - a) - 16 / Real.log 2 -
          ‖∫ sigma in (1 / 2 : ℝ)..2,
              selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * b)‖ -
        ‖∫ sigma in (1 / 2 : ℝ)..2,
              selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * a)‖ ≤
      ‖∫ t in a..b,
          selbergFirstMomentAuxiliary X ((1 / 2 : ℂ) + I * t)‖ :=
  norm_intervalIntegral_selbergFirstMomentAuxiliary_criticalLine_lower
    hX ha hab

example :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, ∀ X : ℕ,
        T0 ≤ T → 2 ≤ X →
        T / 2 - 16 / Real.log 2 -
              2 * C * X * Real.sqrt (T / 2) ≤
          ‖∫ t in T / 2..T,
              selbergFirstMomentAuxiliary X ((1 / 2 : ℂ) + I * t)‖ :=
  exists_norm_intervalIntegral_selbergFirstMomentAuxiliary_dyadic_lower

#print axioms boundaryRectIntegral_selbergFirstMomentAuxiliary_eq_zero
#print axioms intervalIntegral_selbergFirstMomentAuxiliary_criticalLine_eq_right_add_horizontal
#print axioms norm_intervalIntegral_selbergFirstMomentAuxiliary_criticalLine_lower
#print axioms exists_norm_intervalIntegral_selbergFirstMomentAuxiliary_dyadic_lower

end HardyTheorem
