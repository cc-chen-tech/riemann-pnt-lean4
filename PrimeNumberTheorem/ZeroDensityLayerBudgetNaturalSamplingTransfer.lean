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

/-- The target power amplitude is asymptotically unchanged by taking the
natural floor of its argument. -/
theorem targetZeroPowerAmplitude_natFloor_ratio_tendsto
    (beta : ℝ) :
    Tendsto
      (fun x : ℝ =>
        targetZeroPowerAmplitude beta (⌊x⌋₊ : ℝ) /
          targetZeroPowerAmplitude beta x)
      atTop (nhds 1) := by
  have hratio :
      Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ) / x)
        atTop (nhds 1) :=
    tendsto_nat_floor_div_atTop
  have hrpow :
      Tendsto
        (fun x : ℝ => ((⌊x⌋₊ : ℝ) / x) ^ (beta - 1))
        atTop (nhds 1) := by
    simpa using hratio.rpow_const (Or.inl one_ne_zero)
  apply hrpow.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hfloor_nonneg : 0 ≤ (⌊x⌋₊ : ℝ) := by positivity
  simp only [targetZeroPowerAmplitude]
  exact Real.div_rpow hfloor_nonneg hx (beta - 1)

/-- A fixed nonzero coefficient cancels from the floor ratio of the target
power amplitude. -/
theorem const_mul_targetZeroPowerAmplitude_natFloor_ratio_tendsto
    (beta c : ℝ) (hc : c ≠ 0) :
    Tendsto
      (fun x : ℝ =>
        (c * targetZeroPowerAmplitude beta (⌊x⌋₊ : ℝ)) /
          (c * targetZeroPowerAmplitude beta x))
      atTop (nhds 1) := by
  apply
    (targetZeroPowerAmplitude_natFloor_ratio_tendsto beta).congr'
  filter_upwards with x
  field_simp [hc]

end PrimeNumberTheorem
