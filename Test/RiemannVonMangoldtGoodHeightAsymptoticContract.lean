import PrimeNumberTheorem.RiemannVonMangoldt.GoodHeightAsymptotic

open PrimeNumberTheorem

#check RiemannVonMangoldt.exists_abs_zeroCountIncrement_sub_mainTermIncrement_le_log
#check RiemannVonMangoldt.exists_abs_riemannZeroCount_sub_mainTerm_le_log_of_goodHeight

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 6 ≤ T →
    ExplicitFormulaAux.goodHeight T →
    |(RiemannVonMangoldt.riemannZeroCount T : ℝ) -
      RiemannVonMangoldt.riemannVonMangoldtMainTerm T| ≤
      C * (1 + Real.log (T + 5)) :=
  RiemannVonMangoldt.exists_abs_riemannZeroCount_sub_mainTerm_le_log_of_goodHeight
