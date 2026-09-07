import PrimeNumberTheorem.MWKFCubicSmoothIntegral

open PrimeNumberTheorem.MWKFCubic

#check contDiff_intervalIntegral_joint
#check contDiff_integral_joint_compactSupport

open MeasureTheory
open scoped ContDiff

-- The same helper handles vector-valued derivatives and product parameters.
example (F : (ℝ × ℂ) × ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun p ↦ ∫ y : ℝ in a..b, F (p, y)) :=
  contDiff_intervalIntegral_joint F hF a b

-- Reversed and degenerate intervals require no orientation hypothesis.
example (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x ↦ ∫ y : ℝ in (2 : ℝ)..(-3), F (x, y)) :=
  contDiff_intervalIntegral_joint F hF 2 (-3)

example (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ContDiff ℝ ∞ (fun x ↦ ∫ y : ℝ, F (x, y)) :=
  contDiff_integral_joint_compactSupport F hF hc
