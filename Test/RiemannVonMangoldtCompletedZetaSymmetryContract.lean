import PrimeNumberTheorem.RiemannVonMangoldt.CompletedZetaSymmetry

open Complex
open scoped ComplexConjugate

open PrimeNumberTheorem

#check RiemannVonMangoldt.completedZeta_conj
#check RiemannVonMangoldt.logDeriv_completedZeta_conj
#check RiemannVonMangoldt.logDeriv_completedZeta_one_sub_conj

example (s : ℂ) :
    RiemannHypothesis.completedZeta (conj s) =
      conj (RiemannHypothesis.completedZeta s) :=
  RiemannVonMangoldt.completedZeta_conj s

example (s : ℂ) :
    logDeriv RiemannHypothesis.completedZeta (1 - conj s) =
      -conj (logDeriv RiemannHypothesis.completedZeta s) :=
  RiemannVonMangoldt.logDeriv_completedZeta_one_sub_conj s
