import MathlibAux.ArgumentCrossing

open Complex Set Topology

namespace MathlibAux

-- Two continuous logarithms of the same nonvanishing curve on an interval
-- differ by one constant deck transformation, not a point-dependent choice.
example {ell₁ ell₂ : ℝ → ℂ} {a b x₀ : ℝ}
    (h₁ : ContinuousOn ell₁ (Set.Ioo a b))
    (h₂ : ContinuousOn ell₂ (Set.Ioo a b))
    (hexp : ∀ x ∈ Set.Ioo a b, Complex.exp (ell₁ x) = Complex.exp (ell₂ x))
    (hx₀ : x₀ ∈ Set.Ioo a b) :
    ∃ k : ℤ, ∀ x ∈ Set.Ioo a b,
      ell₁ x = ell₂ x + k * (2 * Real.pi * Complex.I) := by
  exact exists_int_continuousLogs_eq_add_two_pi_I h₁ h₂ hexp hx₀

#print axioms exists_int_continuousLogs_eq_add_two_pi_I

-- Mutation caught: a zero-free component whose endpoint argument decreases
-- must still realize every half-odd-integer level between its endpoints.
example (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) (k : ℤ)
    (hlevel : argumentCrossingLevel k ∈
      Set.uIcc (continuousArgumentLift gamma hne 0).im
        (continuousArgumentLift gamma hne 1).im) :
    ∃ t : unitInterval,
      (continuousArgumentLift gamma hne t).im = argumentCrossingLevel k ∧
        (gamma t).re = 0 := by
  exact exists_argumentCrossing_of_level_mem_uIcc gamma hne k hlevel

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

-- A surviving global level is realized on one indexed zero-free component.
example {start finish : ℝ} {components : List (ℝ × ℝ)}
    {bridges : List (ℝ × ℕ)}
    (partition : ArgumentPhasePartition start finish components bridges)
    (gamma : Fin components.length → C(unitInterval, ℂ))
    (hne : ∀ i t, gamma i t ≠ 0)
    (hendpoints : ∀ i,
      (continuousArgumentLift (gamma i) (hne i) 0).im =
          (components.get i).1 ∧
        (continuousArgumentLift (gamma i) (hne i) 1).im =
          (components.get i).2)
    {k : ℤ}
    (hglobal : argumentCrossingLevel k ∈ Set.uIcc start finish)
    (hnotBridge : ∀ bridge ∈ bridges,
      argumentCrossingLevel k ∉
        Set.Ico bridge.1 (bridge.1 + bridge.2 * Real.pi)) :
    ∃ i : Fin components.length, ∃ t : unitInterval,
      (continuousArgumentLift (gamma i) (hne i) t).im =
          argumentCrossingLevel k ∧
        (gamma i t).re = 0 := by
  exact partition.exists_component_argumentCrossing_of_forall_not_mem_bridge
    gamma hne hendpoints hglobal hnotBridge

-- Distinct surviving levels give distinct component-tagged crossing points.
example {start finish : ℝ} {components : List (ℝ × ℝ)}
    {bridges : List (ℝ × ℕ)}
    (partition : ArgumentPhasePartition start finish components bridges)
    (gamma : Fin components.length → C(unitInterval, ℂ))
    (hne : ∀ i t, gamma i t ≠ 0)
    (hendpoints : ∀ i,
      (continuousArgumentLift (gamma i) (hne i) 0).im =
          (components.get i).1 ∧
        (continuousArgumentLift (gamma i) (hne i) 1).im =
          (components.get i).2)
    (K : Finset ℤ)
    (hglobal : ∀ k ∈ K, argumentCrossingLevel k ∈ Set.uIcc start finish)
    (hnotBridge : ∀ k ∈ K, ∀ bridge ∈ bridges,
      argumentCrossingLevel k ∉
        Set.Ico bridge.1 (bridge.1 + bridge.2 * Real.pi)) :
    ∃ crossing : (k : ↥K) →
        Fin components.length × unitInterval,
      Function.Injective crossing ∧
        ∀ k : ↥K,
          (continuousArgumentLift (gamma (crossing k).1)
              (hne (crossing k).1) (crossing k).2).im =
                argumentCrossingLevel k.1 ∧
            (gamma (crossing k).1 (crossing k).2).re = 0 := by
  exact partition.exists_injective_component_argumentCrossings
    gamma hne hendpoints K hglobal hnotBridge

#print axioms exp_continuousArgumentLift_eq
#print axioms exists_argumentCrossing_of_level_mem_uIcc
#print axioms exists_argumentCrossing_of_level_mem_Icc
#print axioms exists_injective_argumentCrossing_times
#print axioms argumentCrossingIndices_card_lower_bound
#print axioms exists_quantified_argumentCrossing_times
#print axioms
  ArgumentPhasePartition.exists_component_argumentCrossing_of_forall_not_mem_bridge
#print axioms ArgumentPhasePartition.exists_injective_component_argumentCrossings

end MathlibAux
