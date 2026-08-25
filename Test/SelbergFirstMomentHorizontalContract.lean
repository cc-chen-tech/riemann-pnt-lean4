import HardyTheorem.SelbergFirstMomentHorizontal

open Complex MeasureTheory

namespace HardyTheorem

example :
    ∃ C T0 : ℝ, 0 < C ∧ 1 ≤ T0 ∧
      ∀ T t sigma : ℝ,
        T0 ≤ T → T ≤ |t| → |t| ≤ 2 * T →
        sigma ∈ Set.Icc (1 / 2 : ℝ) 2 →
        ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤ C * Real.sqrt T :=
  exists_norm_riemannZeta_half_two_strip_le_sqrt

example {X : ℕ} (hX : 2 ≤ X) {sigma t : ℝ}
    (hsigma : 1 / 2 ≤ sigma) :
    ‖selbergSqrtZetaMollifier X ((sigma : ℂ) + I * t)‖ ≤
      2 * Real.sqrt X :=
  norm_selbergSqrtZetaMollifier_half_strip_le_two_sqrt hX hsigma

example :
    ∃ C T0 : ℝ, 0 < C ∧ 1 ≤ T0 ∧
      ∀ T t : ℝ, ∀ X : ℕ,
        T0 ≤ T → T ≤ |t| → |t| ≤ 2 * T → 2 ≤ X →
        ‖∫ sigma in (1 / 2 : ℝ)..2,
            selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * t)‖ ≤
          C * X * Real.sqrt T :=
  exists_norm_intervalIntegral_selbergFirstMomentAuxiliary_horizontal_le

#print axioms exists_norm_riemannZeta_half_two_strip_le_sqrt
#print axioms norm_selbergSqrtZetaMollifier_half_strip_le_two_sqrt
#print axioms
  exists_norm_intervalIntegral_selbergFirstMomentAuxiliary_horizontal_le

end HardyTheorem
