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

example {alpha beta : ℝ} {k : ℤ} :
    k ∈ argumentCrossingIndices alpha beta ↔
      argumentCrossingLevel k ∈ Set.Icc alpha beta :=
  mem_argumentCrossingIndices_iff

example {alpha beta : ℝ} :
    (beta - alpha) / Real.pi - 1 ≤
      (argumentCrossingIndices alpha beta).card :=
  argumentCrossingIndices_card_lower_bound

example (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) :
    ∃ tau : ℤ → unitInterval,
      Set.InjOn tau
          (argumentCrossingIndices
            (continuousArgumentLift gamma hne 0).im
            (continuousArgumentLift gamma hne 1).im : Set ℤ) ∧
        (∀ k ∈ argumentCrossingIndices
            (continuousArgumentLift gamma hne 0).im
            (continuousArgumentLift gamma hne 1).im,
          (continuousArgumentLift gamma hne (tau k)).im =
              argumentCrossingLevel k ∧
            (gamma (tau k)).re = 0) ∧
        ((continuousArgumentLift gamma hne 1).im -
            (continuousArgumentLift gamma hne 0).im) / Real.pi - 1 ≤
          (argumentCrossingIndices
            (continuousArgumentLift gamma hne 0).im
            (continuousArgumentLift gamma hne 1).im).card :=
  exists_quantified_argumentCrossing_times gamma hne

#print axioms exp_continuousArgumentLift_eq
#print axioms exists_argumentCrossing_of_level_mem_Icc
#print axioms exists_injective_argumentCrossing_times
#print axioms argumentCrossingIndices_card_lower_bound
#print axioms exists_quantified_argumentCrossing_times

end MathlibAux
