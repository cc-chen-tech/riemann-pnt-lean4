import PrimeNumberTheorem.RiemannVonMangoldt.ZetaArgumentBound

open Complex MeasureTheory
open scoped Interval

open PrimeNumberTheorem

#check RiemannVonMangoldt.shiftedZetaDivisor
#check RiemannVonMangoldt.shiftedDivisorPrincipalPart
#check RiemannVonMangoldt.abs_integral_im_shiftedDivisorPrincipalPart_le_pi_mul_mass

example {T : ℝ} (hT : 4 ≤ T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    |∫ sigma in (1 / 2 : ℝ)..2,
      (RiemannVonMangoldt.shiftedDivisorPrincipalPart T sigma).im| ≤
      Real.pi * ∑ᶠ u,
        (RiemannVonMangoldt.shiftedZetaDivisor T u : ℝ) :=
  RiemannVonMangoldt.abs_integral_im_shiftedDivisorPrincipalPart_le_pi_mul_mass
    hT hgood
