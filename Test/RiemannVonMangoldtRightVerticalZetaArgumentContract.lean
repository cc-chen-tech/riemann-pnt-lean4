import PrimeNumberTheorem.RiemannVonMangoldt.RightVerticalZetaArgument

open Complex MeasureTheory
open scoped Interval

open PrimeNumberTheorem

#check RiemannVonMangoldt.zetaRightVerticalArgumentVariation
#check RiemannVonMangoldt.abs_zetaRightVerticalArgumentVariation_le_pi

example (U T : ℝ) :
    |RiemannVonMangoldt.zetaRightVerticalArgumentVariation U T| ≤ Real.pi :=
  RiemannVonMangoldt.abs_zetaRightVerticalArgumentVariation_le_pi U T
