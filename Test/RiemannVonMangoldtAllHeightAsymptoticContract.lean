import PrimeNumberTheorem.RiemannVonMangoldt.AllHeightAsymptotic

open PrimeNumberTheorem

#check RiemannVonMangoldt.hasDerivAt_riemannVonMangoldtMainTerm
#check RiemannVonMangoldt.exists_abs_riemannZeroCount_sub_mainTerm_le_log

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 8 ≤ T →
    |(RiemannVonMangoldt.riemannZeroCount T : ℝ) -
      RiemannVonMangoldt.riemannVonMangoldtMainTerm T| ≤
      C * (1 + Real.log (T + 6)) :=
  RiemannVonMangoldt.exists_abs_riemannZeroCount_sub_mainTerm_le_log
