import PrimeNumberTheorem.RiemannVonMangoldt.HalfBoundary

open Complex MeasureTheory
open scoped Interval

open PrimeNumberTheorem

#check RiemannVonMangoldt.completedZetaHalfBoundaryPhase
#check RiemannVonMangoldt.pi_mul_zeroCount_sub_eq_completedZetaHalfBoundaryPhase

example {U T : ℝ} (hU : 4 ≤ U) (hUT : U < T)
    (hUgood : ExplicitFormulaAux.goodHeight U)
    (hTgood : ExplicitFormulaAux.goodHeight T) :
    Real.pi * ((RiemannVonMangoldt.riemannZeroCount T -
      RiemannVonMangoldt.riemannZeroCount U : ℕ) : ℝ) =
      RiemannVonMangoldt.completedZetaHalfBoundaryPhase U T :=
  RiemannVonMangoldt.pi_mul_zeroCount_sub_eq_completedZetaHalfBoundaryPhase
    hU hUT hUgood hTgood
