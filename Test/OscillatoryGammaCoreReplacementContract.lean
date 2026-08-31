import HardyTheorem.OscillatoryGammaCoreReplacement

open Complex MeasureTheory HardyTheorem.AFE
open HardyTheorem.OscillatoryGammaBoundaryFormula

-- The canonical whole value must be the actual positive-phase conditional limit.
example {sigma c t x : ℝ} {N : ℕ} (hs0 : 0 < sigma) (hs1 : sigma < 1)
    (hc : 0 < c) (hx : 0 < x) (hgap : c * x < t)
    (hN : 1 ≤ N) (hfar : 2 * t ≤ c * (N : ℝ)) :
    let s : ℂ := (sigma : ℂ) + I * t
    ‖oscillatoryGammaPosWhole (1 - s) c -
      ∫ u in x..(N : ℝ), (u : ℂ) ^ (-s) * Complex.exp (I * (c * u))‖ ≤
        2 * x ^ (1 - sigma) / (t - c * x) + 8 * (N : ℝ) ^ (-sigma) / c :=
  norm_oscillatoryGammaPosWhole_sub_mellinCore_le hs0 hs1 hc hx hgap hN hfar

-- The exact coefficient, its phase sign, and both endpoint denominators matter.
example {sigma c t x : ℝ} {N : ℕ} (hs0 : 0 < sigma) (hs1 : sigma < 1)
    (hc : 0 < c) (hx : 0 < x) (hgap : c * x < t)
    (hN : 1 ≤ N) (hfar : 2 * t ≤ c * (N : ℝ)) :
    let s : ℂ := (sigma : ℂ) + I * t
    ‖(∫ u in x..(N : ℝ), (u : ℂ) ^ (-s) * Complex.exp (I * (c * u))) -
      (c : ℂ) ^ (s - 1) *
        (Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ) * (1 - s)) * Complex.Gamma (1 - s))‖ ≤
      2 * x ^ (1 - sigma) / (t - c * x) + 8 * (N : ℝ) ^ (-sigma) / c :=
  norm_mellinCore_sub_gammaValue_le hs0 hs1 hc hx hgap hN hfar

#print axioms norm_oscillatoryGammaPosWhole_sub_mellinCore_le
#print axioms norm_mellinCore_sub_gammaValue_le
