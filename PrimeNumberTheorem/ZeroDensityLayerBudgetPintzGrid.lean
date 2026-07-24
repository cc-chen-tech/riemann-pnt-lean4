import PrimeNumberTheorem.ZeroDensityLayerBudgetEventuallyZeroFreeUnified

/-!
# Pintz envelope dynamic candidate grids

The Pintz input is a diverging lower envelope for admissible explicit-formula
heights.  A finite collection of positive candidates is placed above that
envelope at every scale.  If those candidates are eventually zero-free, this
single input produces both the dynamic optimization grid and the eventual
zero-free certificate required by the unified transfer.
-/

namespace PrimeNumberTheorem

/--
Pintz-envelope data for a scale-dependent finite candidate grid.

The concrete `PintzEnvelope.lean` growth theorem is intended to discharge
`envelope_tendsto_atTop`; its eventual admissibility theorem is intended to
discharge `eventually_candidate_zeroFree`.
-/
structure PintzEnvelopeDynamicGridInput
    (zeroFree : ℝ → ℝ → Prop) where
  envelope : ℝ → ℝ
  candidates : ℝ → FiniteHeightGrid
  envelope_tendsto_atTop :
    Filter.Tendsto envelope Filter.atTop Filter.atTop
  envelope_le_candidates :
    ∀ x T, T ∈ (candidates x).heights → envelope x ≤ T
  eventually_candidate_zeroFree :
    ∀ᶠ x in Filter.atTop,
      ∀ T, T ∈ (candidates x).heights → zeroFree x T

/-- Build the dynamic finite-height grid carried by a Pintz envelope input. -/
def PintzEnvelopeDynamicGridInput.toDynamicFiniteHeightGrid
    {zeroFree : ℝ → ℝ → Prop}
    (input : PintzEnvelopeDynamicGridInput zeroFree) :
    DynamicFiniteHeightGrid where
  grid := input.candidates
  lowerEnvelope := input.envelope
  lowerEnvelope_tendsto_atTop := input.envelope_tendsto_atTop
  lowerEnvelope_le := input.envelope_le_candidates

/--
The same Pintz input supplies eventual zero-freeness for its converted dynamic
grid.
-/
def PintzEnvelopeDynamicGridInput.toEventuallyZeroFreeHeightCertificate
    {zeroFree : ℝ → ℝ → Prop}
    (input : PintzEnvelopeDynamicGridInput zeroFree) :
    EventuallyDynamicZeroFreeHeightCertificate zeroFree
      input.toDynamicFiniteHeightGrid where
  eventually_candidate_zeroFree :=
    input.eventually_candidate_zeroFree

/--
The pointwise cost minimizer selected from a Pintz grid always lies above the
Pintz envelope.
-/
theorem PintzEnvelopeDynamicGridInput.envelope_le_optimalHeight
    {zeroFree : ℝ → ℝ → Prop}
    (input : PintzEnvelopeDynamicGridInput zeroFree)
    (cost : ℝ → ℝ → ℝ) (x : ℝ) :
    input.envelope x ≤
      dynamicFiniteGridOptimalHeight
        cost input.toDynamicFiniteHeightGrid x :=
  input.envelope_le_candidates x _
    (dynamicFiniteGridOptimalHeight_mem
      cost input.toDynamicFiniteHeightGrid x)

/--
The optimizer selected from the Pintz grid tends to infinity.
-/
theorem PintzEnvelopeDynamicGridInput.optimalHeight_tendsto_atTop
    {zeroFree : ℝ → ℝ → Prop}
    (input : PintzEnvelopeDynamicGridInput zeroFree)
    (cost : ℝ → ℝ → ℝ) :
    Filter.Tendsto
      (dynamicFiniteGridOptimalHeight
        cost input.toDynamicFiniteHeightGrid)
      Filter.atTop Filter.atTop :=
  dynamicFiniteGridOptimalHeight_tendsto_atTop
    cost input.toDynamicFiniteHeightGrid

/--
The Pintz-grid optimizer is eventually zero-free.
-/
theorem PintzEnvelopeDynamicGridInput.eventually_optimalHeight_zeroFree
    {zeroFree : ℝ → ℝ → Prop}
    (input : PintzEnvelopeDynamicGridInput zeroFree)
    (cost : ℝ → ℝ → ℝ) :
    ∀ᶠ x in Filter.atTop,
      zeroFree x
        (dynamicFiniteGridOptimalHeight
          cost input.toDynamicFiniteHeightGrid x) :=
  eventually_dynamicFiniteGridOptimalHeight_zeroFree
    cost input.toDynamicFiniteHeightGrid
      input.toEventuallyZeroFreeHeightCertificate

end PrimeNumberTheorem
