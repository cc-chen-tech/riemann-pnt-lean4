import PrimeNumberTheorem.RiemannVonMangoldt.SelbergScale

open PrimeNumberTheorem

#check RiemannVonMangoldt.exists_eventually_riemannZeroCount_ge_selbergScale

example : ∃ c : ℝ, 0 < c ∧ ∀ᶠ T in Filter.atTop,
    c * (T / (2 * Real.pi) * Real.log T) ≤
      (RiemannVonMangoldt.riemannZeroCount T : ℝ) :=
  RiemannVonMangoldt.exists_eventually_riemannZeroCount_ge_selbergScale
