import PrimeNumberTheorem.RiemannVonMangoldt.CountPhaseIdentity

open Complex MeasureTheory
open scoped Interval

open PrimeNumberTheorem

#check RiemannVonMangoldt.zetaHalfPathArgument
#check RiemannVonMangoldt.riemannZeroCount_sub_eq_gammaPhase_add_zetaHalfPathArgument
#check RiemannVonMangoldt.exists_abs_zetaHalfPathArgument_le_log

example {U T : ℝ} (hU : 4 ≤ U) (hUT : U < T)
    (hUgood : ExplicitFormulaAux.goodHeight U)
    (hTgood : ExplicitFormulaAux.goodHeight T) :
    Real.pi * ((RiemannVonMangoldt.riemannZeroCount T -
      RiemannVonMangoldt.riemannZeroCount U : ℕ) : ℝ) =
      HardyTheorem.verticalGammaUnwrappedPhase T -
        HardyTheorem.verticalGammaUnwrappedPhase U +
      RiemannVonMangoldt.zetaHalfPathArgument U T :=
  RiemannVonMangoldt.riemannZeroCount_sub_eq_gammaPhase_add_zetaHalfPathArgument
    hU hUT hUgood hTgood
