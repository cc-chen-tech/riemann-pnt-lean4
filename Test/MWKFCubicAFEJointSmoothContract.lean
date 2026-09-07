import PrimeNumberTheorem.MWKFCubicAFEJointSmooth

open PrimeNumberTheorem.MWKFCubic

#check contDiff_cubicAFEScalar_joint
#check contDiff_cubicAFELogProductWeightFinite_joint
#check contDiffOn_cubicAFERealProductWeightFinite_joint
#check contDiff_cubicAFEProgressionCutoffSummand_joint
#check contDiff_integral_cubicAFEProgressionCutoffSummand
#check cubicAFEIntegratedProgressionSchwartz

open MeasureTheory Set
open scoped ContDiff SchwartzMap

#check (@contDiff_cubicAFEProgressionCutoffSummand_joint :
  ∀ (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ}, 0 < d → 0 < e →
    ∀ {δ : ℤ} (χ : CubicProgressionCutoff d e δ), 1 / 2 < X →
    ContDiff ℝ ∞ (Function.uncurry (cubicAFEProgressionCutoffSummand W T X V χ)))

-- This is the literal time-integrated physical kernel, not an abstract
-- Schwartz replacement or a conditional regularity interface.
example (W : CubicTestWeight) {T X : ℝ} (hT : T ≠ 0) (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) {δ : ℤ}
    (χ : CubicProgressionCutoff d e δ) (x : ℝ) :
    cubicAFEIntegratedProgressionSchwartz W hT hX V hd he χ x =
      ∫ t : ℝ, cubicAFEProgressionCutoffSummand W T X V χ t x := rfl

example (W : CubicTestWeight) {T X : ℝ} (hT : T ≠ 0) (hX : 1 / 2 < X)
    (χ : CubicProgressionCutoff 1 1 (-3)) :
    ContDiff ℝ ∞ (fun x ↦ ∫ t : ℝ, cubicAFEProgressionCutoffSummand W T X (-2) χ t x) :=
  contDiff_integral_cubicAFEProgressionCutoffSummand W hT hX (-2) (by norm_num) (by norm_num) χ
