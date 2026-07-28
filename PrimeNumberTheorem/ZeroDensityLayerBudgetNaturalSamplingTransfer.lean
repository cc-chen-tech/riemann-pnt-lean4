import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalTransfer

/-!
# Sampling a far real witness at natural points

This file isolates the exact approximation needed to transfer a far
real-variable amplitude witness to natural arguments.  It is designed for
finite zeta-zero packages whose normalized variation over an interval of
length one tends to zero.
-/

namespace PrimeNumberTheorem

open Filter

/-- A far real witness can be sampled at natural floors if the amplitude lost
at the floor and the sampling error together fit below the original
amplitude. -/
theorem HasFarTargetAmplitudeWitness.toNatural_natFloor_of_eventually_sampling
    {f amplitude : ℝ → ℝ} (q : ℝ)
    (hwitness : HasFarTargetAmplitudeWitness f amplitude)
    (hsampling :
      ∀ᶠ x : ℝ in atTop,
        q * amplitude (⌊x⌋₊ : ℝ) +
            |f (⌊x⌋₊ : ℝ) - f x| ≤
          amplitude x) :
    HasFarNaturalPointTargetAmplitudeWitness
      (fun m : ℕ => f (m : ℝ))
      (fun m : ℕ => q * amplitude (m : ℝ)) := by
  intro M
  rcases eventually_atTop.1 hsampling with ⟨X₀, hX₀⟩
  rcases hwitness (max X₀ ((M : ℝ) + 1)) with ⟨x, hx, hwitness_x⟩
  have hx₀ : X₀ ≤ x := (le_max_left _ _).trans hx
  have hxM : (M : ℝ) ≤ x := by
    have : (M : ℝ) + 1 ≤ x := (le_max_right _ _).trans hx
    linarith
  have hM : M ≤ ⌊x⌋₊ := Nat.le_floor hxM
  have hsampling_x := hX₀ x hx₀
  have htriangle :
      |f x| ≤
        |f (⌊x⌋₊ : ℝ)| +
          |f (⌊x⌋₊ : ℝ) - f x| := by
    have h :=
      abs_add_le (f (⌊x⌋₊ : ℝ))
        (f x - f (⌊x⌋₊ : ℝ))
    calc
      |f x| =
          |f (⌊x⌋₊ : ℝ) +
            (f x - f (⌊x⌋₊ : ℝ))| := by
              congr 1
              ring
      _ ≤
          |f (⌊x⌋₊ : ℝ)| +
            |f x - f (⌊x⌋₊ : ℝ)| := h
      _ =
          |f (⌊x⌋₊ : ℝ)| +
            |f (⌊x⌋₊ : ℝ) - f x| := by
              rw [abs_sub_comm]
  refine ⟨⌊x⌋₊, hM, ?_⟩
  linarith

/-- Normalized floor stability implies the eventual sampling inequality, so
every factor `q < 1` of a far real witness survives at natural points. -/
theorem HasFarTargetAmplitudeWitness.toNatural_natFloor_of_normalized_stability
    {f amplitude : ℝ → ℝ} {q : ℝ}
    (hq : q < 1)
    (hwitness : HasFarTargetAmplitudeWitness f amplitude)
    (hamplitude_pos : ∀ᶠ x : ℝ in atTop, 0 < amplitude x)
    (hamplitude_floor :
      Tendsto
        (fun x : ℝ => amplitude (⌊x⌋₊ : ℝ) / amplitude x)
        atTop (nhds 1))
    (hsampling :
      Tendsto
        (fun x : ℝ =>
          |f (⌊x⌋₊ : ℝ) - f x| / amplitude x)
        atTop (nhds 0)) :
    HasFarNaturalPointTargetAmplitudeWitness
      (fun m : ℕ => f (m : ℝ))
      (fun m : ℕ => q * amplitude (m : ℝ)) := by
  have hnormalized :
      Tendsto
        (fun x : ℝ =>
          q * (amplitude (⌊x⌋₊ : ℝ) / amplitude x) +
            |f (⌊x⌋₊ : ℝ) - f x| / amplitude x)
        atTop (nhds q) := by
    simpa using
      (tendsto_const_nhds.mul hamplitude_floor).add hsampling
  have hnormalized_lt :
      ∀ᶠ x : ℝ in atTop,
        q * (amplitude (⌊x⌋₊ : ℝ) / amplitude x) +
            |f (⌊x⌋₊ : ℝ) - f x| / amplitude x <
          1 :=
    hnormalized.eventually_lt_const hq
  apply
    HasFarTargetAmplitudeWitness.toNatural_natFloor_of_eventually_sampling
      q hwitness
  filter_upwards [hamplitude_pos, hnormalized_lt] with x hx hratio
  have hdiv :
      (q * amplitude (⌊x⌋₊ : ℝ) +
          |f (⌊x⌋₊ : ℝ) - f x|) /
          amplitude x <
        1 := by
    calc
      (q * amplitude (⌊x⌋₊ : ℝ) +
          |f (⌊x⌋₊ : ℝ) - f x|) /
          amplitude x =
        q * (amplitude (⌊x⌋₊ : ℝ) / amplitude x) +
          |f (⌊x⌋₊ : ℝ) - f x| / amplitude x := by ring
      _ < 1 := hratio
  exact le_of_lt (by
    simpa using (div_lt_iff₀ hx).1 hdiv)

end PrimeNumberTheorem
