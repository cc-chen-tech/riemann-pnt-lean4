import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Order.IntermediateValue

/-!
# Argument variation produces distinct real-part crossings

This file isolates the topological crossing mechanism behind the left-hand side of
Conrey's equation (41).  A nonvanishing complex curve on the unit interval has a
canonical continuous logarithmic lift, normalized by the principal logarithm at
the left endpoint.  Every lifted argument level `π / 2 + kπ` between the endpoint
arguments gives a zero of the real part, and different levels give different
crossing times.

The result deliberately counts crossings only on a zero-free interval.  Applying
it to a curve with zeros requires first partitioning at those zeros; that is the
separate subtraction step represented by `N_{0,η}` in Conrey's argument.
-/

open Complex Set Topology

namespace MathlibAux

private noncomputable def nonzeroCurve (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) :
    C(unitInterval, {z : ℂ // z ≠ 0}) :=
  ⟨fun t ↦ ⟨gamma t, hne t⟩, gamma.continuous.subtype_mk hne⟩

/-- The continuous logarithmic lift of a nonvanishing complex curve, normalized
by the principal logarithm at the left endpoint. -/
noncomputable def continuousArgumentLift (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) :
    C(unitInterval, ℂ) :=
  Complex.isCoveringMap_exp.liftPath (nonzeroCurve gamma hne) (Complex.log (gamma 0)) (by
    apply Subtype.ext
    exact (Complex.exp_log (hne 0)).symm)

theorem exp_continuousArgumentLift_eq (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0)
    (t : unitInterval) :
    Complex.exp (continuousArgumentLift gamma hne t) = gamma t := by
  have h := congr_fun (Complex.isCoveringMap_exp.liftPath_lifts
    (nonzeroCurve gamma hne) (Complex.log (gamma 0)) (by
      apply Subtype.ext
      exact (Complex.exp_log (hne 0)).symm)) t
  exact congrArg Subtype.val h

theorem continuousArgumentLift_zero (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) :
    continuousArgumentLift gamma hne 0 = Complex.log (gamma 0) :=
  Complex.isCoveringMap_exp.liftPath_zero
    (nonzeroCurve gamma hne) (Complex.log (gamma 0)) (by
      apply Subtype.ext
      exact (Complex.exp_log (hne 0)).symm)

/-- The lifted argument levels at which the real part of a complex number vanishes. -/
noncomputable def argumentCrossingLevel (k : ℤ) : ℝ :=
  Real.pi / 2 + k * Real.pi

theorem exists_argumentCrossing_of_level_mem_Icc
    (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) (k : ℤ)
    (hlevel : argumentCrossingLevel k ∈
      Icc (continuousArgumentLift gamma hne 0).im
        (continuousArgumentLift gamma hne 1).im) :
    ∃ t : unitInterval,
      (continuousArgumentLift gamma hne t).im = argumentCrossingLevel k ∧
        (gamma t).re = 0 := by
  let theta : unitInterval → ℝ := fun t ↦ (continuousArgumentLift gamma hne t).im
  have htheta : Continuous theta :=
    Complex.continuous_im.comp (continuousArgumentLift gamma hne).continuous
  rcases intermediate_value_univ (0 : unitInterval) 1 htheta hlevel with ⟨t, ht⟩
  have ht' : (continuousArgumentLift gamma hne t).im = argumentCrossingLevel k := by
    simpa [theta] using ht
  refine ⟨t, ht', ?_⟩
  rw [← exp_continuousArgumentLift_eq gamma hne t, Complex.exp_re, ht',
    argumentCrossingLevel, Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero,
    mul_zero]

theorem exists_injective_argumentCrossing_times
    (gamma : C(unitInterval, ℂ)) (hne : ∀ t, gamma t ≠ 0) (K : Finset ℤ)
    (hK : ∀ k ∈ K, argumentCrossingLevel k ∈
      Icc (continuousArgumentLift gamma hne 0).im
        (continuousArgumentLift gamma hne 1).im) :
    ∃ tau : ℤ → unitInterval, Set.InjOn tau (K : Set ℤ) ∧
      ∀ k ∈ K,
        (continuousArgumentLift gamma hne (tau k)).im = argumentCrossingLevel k ∧
          (gamma (tau k)).re = 0 := by
  classical
  have hcross : ∀ k : ℤ, k ∈ K → ∃ t : unitInterval,
      (continuousArgumentLift gamma hne t).im = argumentCrossingLevel k ∧
        (gamma t).re = 0 := fun k hk ↦
    exists_argumentCrossing_of_level_mem_Icc gamma hne k (hK k hk)
  let tau : ℤ → unitInterval := fun k ↦ if hk : k ∈ K then Classical.choose (hcross k hk) else 0
  have htau : ∀ k ∈ K,
      (continuousArgumentLift gamma hne (tau k)).im = argumentCrossingLevel k ∧
        (gamma (tau k)).re = 0 := by
    intro k hk
    rw [show tau k = Classical.choose (hcross k hk) by simp [tau, hk]]
    exact Classical.choose_spec (hcross k hk)
  refine ⟨tau, ?_, htau⟩
  intro k hk l hl hkl
  have hlevels : argumentCrossingLevel k = argumentCrossingLevel l := by
    calc
      argumentCrossingLevel k = (continuousArgumentLift gamma hne (tau k)).im :=
        (htau k (by simpa using hk)).1.symm
      _ = (continuousArgumentLift gamma hne (tau l)).im := by rw [hkl]
      _ = argumentCrossingLevel l := (htau l (by simpa using hl)).1
  have hcasts : (k : ℝ) = (l : ℝ) := by
    unfold argumentCrossingLevel at hlevels
    nlinarith [Real.pi_pos]
  exact_mod_cast hcasts

end MathlibAux
