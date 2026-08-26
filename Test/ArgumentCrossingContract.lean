import MathlibAux.ArgumentCrossing

open Complex Set Topology

namespace MathlibAux

example (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) (t : unitInterval) :
    Complex.exp (continuousArgumentLift gamma hne t) = gamma t :=
  exp_continuousArgumentLift_eq gamma hne t

example (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) :
    continuousArgumentLift gamma hne 0 = Complex.log (gamma 0) :=
  continuousArgumentLift_zero gamma hne

example (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) (k : ℤ)
    (hlevel : argumentCrossingLevel k ∈
      Set.Icc (continuousArgumentLift gamma hne 0).im
        (continuousArgumentLift gamma hne 1).im) :
    ∃ t : unitInterval,
      (continuousArgumentLift gamma hne t).im = argumentCrossingLevel k ∧
        (gamma t).re = 0 :=
  exists_argumentCrossing_of_level_mem_Icc gamma hne k hlevel

example (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0)
    (K : Finset ℤ)
    (hK : ∀ k ∈ K, argumentCrossingLevel k ∈
      Set.Icc (continuousArgumentLift gamma hne 0).im
        (continuousArgumentLift gamma hne 1).im) :
    ∃ tau : ℤ → unitInterval,
      Set.InjOn tau (K : Set ℤ) ∧
        ∀ k ∈ K,
          (continuousArgumentLift gamma hne (tau k)).im =
              argumentCrossingLevel k ∧
            (gamma (tau k)).re = 0 :=
  exists_injective_argumentCrossing_times gamma hne K hK

#print axioms exp_continuousArgumentLift_eq
#print axioms exists_argumentCrossing_of_level_mem_Icc
#print axioms exists_injective_argumentCrossing_times

end MathlibAux
