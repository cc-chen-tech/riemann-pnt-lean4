import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTSharpSignedOmega
import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeTransfer

/-!
# Real-variable signed target-amplitude witnesses

The existing signed sharp-transfer predicates are indexed by natural sample
points.  This module supplies the corresponding real-variable target-scale
interfaces and embeds every natural-point witness into them.
-/

namespace PrimeNumberTheorem

/-- Arbitrarily far real points where `f` is at least the scale-dependent
amplitude. -/
def HasFarPositiveTargetAmplitudeWitness
    (f amplitude : ℝ → ℝ) : Prop :=
  ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧ amplitude x ≤ f x

/-- Arbitrarily far real points where `f` is at most the negative of the
scale-dependent amplitude. -/
def HasFarNegativeTargetAmplitudeWitness
    (f amplitude : ℝ → ℝ) : Prop :=
  ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧ f x ≤ -amplitude x

/-- Both signs recur arbitrarily far with one common scale-dependent
amplitude. -/
structure HasFarSignedTargetAmplitudeWitnesses
    (f amplitude : ℝ → ℝ) : Prop where
  positive : HasFarPositiveTargetAmplitudeWitness f amplitude
  negative : HasFarNegativeTargetAmplitudeWitness f amplitude

/-- A positive natural-point target-amplitude witness embeds into the
real-variable interface. -/
theorem HasFarNaturalPointPositiveTargetAmplitudeWitness.toReal
    {f amplitude : ℝ → ℝ}
    (hwitness :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ => f (m : ℝ))
        (fun m : ℕ => amplitude (m : ℝ))) :
    HasFarPositiveTargetAmplitudeWitness f amplitude := by
  intro X
  rcases exists_nat_ge X with ⟨M, hXM⟩
  rcases hwitness M with ⟨m, hmM, hm⟩
  have hcast : (M : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hmM
  exact ⟨(m : ℝ), hXM.trans hcast, hm⟩

/-- A negative natural-point target-amplitude witness embeds into the
real-variable interface. -/
theorem HasFarNaturalPointNegativeTargetAmplitudeWitness.toReal
    {f amplitude : ℝ → ℝ}
    (hwitness :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ => f (m : ℝ))
        (fun m : ℕ => amplitude (m : ℝ))) :
    HasFarNegativeTargetAmplitudeWitness f amplitude := by
  intro X
  rcases exists_nat_ge X with ⟨M, hXM⟩
  rcases hwitness M with ⟨m, hmM, hm⟩
  have hcast : (M : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hmM
  exact ⟨(m : ℝ), hXM.trans hcast, hm⟩

/-- A pair of signed natural-point witnesses embeds into one real-variable
signed target-amplitude certificate. -/
theorem hasFarSignedTargetAmplitudeWitnesses_of_naturalPoint
    {f amplitude : ℝ → ℝ}
    (hpositive :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ => f (m : ℝ))
        (fun m : ℕ => amplitude (m : ℝ)))
    (hnegative :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ => f (m : ℝ))
        (fun m : ℕ => amplitude (m : ℝ))) :
    HasFarSignedTargetAmplitudeWitnesses f amplitude :=
  ⟨hpositive.toReal, hnegative.toReal⟩

end PrimeNumberTheorem
