import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTMovingSigmaTransfer

/-!
# Anchored Carlson control for moving real-part thresholds

A family of thresholds may move with the selected explicit-formula height
without requiring Carlson constants uniform in the threshold.  Fix an anchor
`sigma0 > 1 / 2`.  If every threshold to the right of the critical line is at
least `sigma0`, antitonicity gives

`zeroDensityCount (sigma T i) T <= zeroDensityCount sigma0 T`.

Thus one fixed Carlson estimate at `sigma0` controls every moving high layer.
Low layers remain controlled by the global multiplicity count.  This module
proves that the resulting uniform budget feeds the moving-threshold explicit
formula and yields decay of the actual relative PNT error.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- A height-dependent threshold family is anchored at `sigma0` when every
threshold strictly to the right of `1 / 2` is at least `sigma0`. -/
def MovingSigmaAnchoredAt
    {n : ℕ} (sigma0 : ℝ)
    (inputAtHeight : ∀ T : ℝ, PositiveZeroBucketInput T n) : Prop :=
  ∀ T i, 1 / 2 < (inputAtHeight T).sigma i →
    sigma0 ≤ (inputAtHeight T).sigma i

/-- Uniform majorant for `n` moving layers: all low layers are charged to the
global zero count and all high layers to the one fixed Carlson count at
`sigma0`. -/
noncomputable def anchoredMovingSigmaDensityMajorant
    (n : ℕ) (sigma0 x T : ℝ) : ℝ :=
  (n : ℝ) * ExplicitFormulaAux.globalZeroMultiplicity T *
      Real.exp (-Pintz.pintzZeroEnvelope x) +
    (n : ℝ) * (ZeroDensity.zeroDensityCount sigma0 T : ℝ) *
      Real.exp (-Pintz.pintzZeroEnvelope x)

/-- The hybrid budget of any anchored threshold family is bounded pointwise
by one global-count term plus one fixed-anchor Carlson term per layer. -/
theorem pintzCarlsonHybridDensityBudget_le_anchoredMajorant
    {n : ℕ} {sigma0 : ℝ} (sigma : Fin n → ℝ)
    (hanchor : ∀ i, 1 / 2 < sigma i → sigma0 ≤ sigma i)
    (x T : ℝ) :
    pintzCarlsonHybridDensityBudget sigma x T ≤
      anchoredMovingSigmaDensityMajorant n sigma0 x T := by
  classical
  have hlowCardNat :
      (pintzCarlsonLowDensityIndices sigma).card ≤ n := by
    calc
      (pintzCarlsonLowDensityIndices sigma).card ≤
          (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have hhighCardNat :
      (pintzCarlsonHighDensityIndices sigma).card ≤ n := by
    calc
      (pintzCarlsonHighDensityIndices sigma).card ≤
          (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have hlowCard :
      ((pintzCarlsonLowDensityIndices sigma).card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hlowCardNat
  have hhighCard :
      ((pintzCarlsonHighDensityIndices sigma).card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hhighCardNat
  have hglobal0 :
      0 ≤ ExplicitFormulaAux.globalZeroMultiplicity T :=
    ExplicitFormulaAux.globalZeroMultiplicity_nonneg T
  have hexp0 : 0 ≤ Real.exp (-Pintz.pintzZeroEnvelope x) :=
    Real.exp_nonneg _
  have hanchorCount0 :
      0 ≤ (ZeroDensity.zeroDensityCount sigma0 T : ℝ) :=
    Nat.cast_nonneg _
  have hlow :
      pintzGlobalLowDensityBudget sigma x T ≤
        (n : ℝ) * ExplicitFormulaAux.globalZeroMultiplicity T *
          Real.exp (-Pintz.pintzZeroEnvelope x) := by
    dsimp [pintzGlobalLowDensityBudget]
    have hfactor0 :
        0 ≤ ExplicitFormulaAux.globalZeroMultiplicity T *
          Real.exp (-Pintz.pintzZeroEnvelope x) :=
      mul_nonneg hglobal0 hexp0
    calc
      ((pintzCarlsonLowDensityIndices sigma).card : ℝ) *
            ExplicitFormulaAux.globalZeroMultiplicity T *
            Real.exp (-Pintz.pintzZeroEnvelope x) =
          ((pintzCarlsonLowDensityIndices sigma).card : ℝ) *
            (ExplicitFormulaAux.globalZeroMultiplicity T *
              Real.exp (-Pintz.pintzZeroEnvelope x)) := by ring
      _ ≤ (n : ℝ) *
            (ExplicitFormulaAux.globalZeroMultiplicity T *
              Real.exp (-Pintz.pintzZeroEnvelope x)) :=
        mul_le_mul_of_nonneg_right hlowCard hfactor0
      _ = _ := by ring
  have hhigh :
      pintzCarlsonClassicalAggregatedDensityLayerTerm
          (pintzCarlsonHighDensityIndices sigma) sigma () x T ≤
        (n : ℝ) * (ZeroDensity.zeroDensityCount sigma0 T : ℝ) *
          Real.exp (-Pintz.pintzZeroEnvelope x) := by
    simp only [pintzCarlsonClassicalAggregatedDensityLayerTerm,
      pintzCarlsonAggregatedDensityLayerTerm]
    calc
      (∑ i ∈ pintzCarlsonHighDensityIndices sigma,
          (ZeroDensity.zeroDensityCount (sigma i) T : ℝ) *
            Real.exp (-Pintz.pintzZeroEnvelope x)) ≤
          ∑ _i ∈ pintzCarlsonHighDensityIndices sigma,
            (ZeroDensity.zeroDensityCount sigma0 T : ℝ) *
              Real.exp (-Pintz.pintzZeroEnvelope x) := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast
            ZeroDensity.zeroDensityCount_antitone_re
              (hanchor i (mem_pintzCarlsonHighDensityIndices.mp hi))
        · exact hexp0
      _ = ((pintzCarlsonHighDensityIndices sigma).card : ℝ) *
            (ZeroDensity.zeroDensityCount sigma0 T : ℝ) *
              Real.exp (-Pintz.pintzZeroEnvelope x) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ (n : ℝ) * (ZeroDensity.zeroDensityCount sigma0 T : ℝ) *
            Real.exp (-Pintz.pintzZeroEnvelope x) := by
        have hfactor0 :
            0 ≤ (ZeroDensity.zeroDensityCount sigma0 T : ℝ) *
              Real.exp (-Pintz.pintzZeroEnvelope x) :=
          mul_nonneg hanchorCount0 hexp0
        calc
          ((pintzCarlsonHighDensityIndices sigma).card : ℝ) *
                (ZeroDensity.zeroDensityCount sigma0 T : ℝ) *
                Real.exp (-Pintz.pintzZeroEnvelope x) =
              ((pintzCarlsonHighDensityIndices sigma).card : ℝ) *
                ((ZeroDensity.zeroDensityCount sigma0 T : ℝ) *
                  Real.exp (-Pintz.pintzZeroEnvelope x)) := by ring
          _ ≤ (n : ℝ) *
                ((ZeroDensity.zeroDensityCount sigma0 T : ℝ) *
                  Real.exp (-Pintz.pintzZeroEnvelope x)) :=
            mul_le_mul_of_nonneg_right hhighCard hfactor0
          _ = _ := by ring
  exact add_le_add hlow hhigh

/-- One Pintz constant makes the global-plus-fixed-anchor majorant decay for
every sufficiently small positive fixed rate. -/
theorem exists_pintzConstant_anchoredMovingSigmaDensityMajorant_tendsto
    (n : ℕ) (sigma0 : ℝ)
    (hhalf : 1 / 2 < sigma0) (hlt : sigma0 < 1) :
    ∃ c > 0, ∀ rate : ℝ, 0 < rate → rate < 2 * Real.sqrt c →
      Tendsto
        (fun x : ℝ =>
          anchoredMovingSigmaDensityMajorant n sigma0 x
            (pintzCarlsonHeight rate x))
        atTop (nhds 0) := by
  let lowSigma : Fin n → ℝ := fun _ => 0
  let anchorSigma : Fin n → ℝ := fun _ => sigma0
  rcases exists_pintzConstant_fixedGlobalLowDensityBudget_tendsto
      lowSigma with ⟨cLow, hcLow, hLow⟩
  rcases exists_pintzConstant_fixedClassicalCarlsonDensity_tendsto
      (Finset.univ : Finset (Fin n)) anchorSigma
      (fun _ => hhalf) (fun _ => hlt) with
    ⟨cHigh, hcHigh, hHigh⟩
  refine ⟨min cLow cHigh, lt_min hcLow hcHigh, ?_⟩
  intro rate hrate hgap
  have hgapLow : rate < 2 * Real.sqrt cLow :=
    hgap.trans_le
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (min_le_left cLow cHigh)) (by norm_num))
  have hgapHigh : rate < 2 * Real.sqrt cHigh :=
    hgap.trans_le
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (min_le_right cLow cHigh)) (by norm_num))
  have hLowLimit := hLow rate hrate hgapLow
  have hHighLimit := hHigh rate hrate hgapHigh
  have hLowLimit' :
      Tendsto
        (fun x : ℝ =>
          (n : ℝ) *
            ExplicitFormulaAux.globalZeroMultiplicity
              (pintzCarlsonHeight rate x) *
            Real.exp (-Pintz.pintzZeroEnvelope x))
        atTop (nhds 0) := by
    simpa [lowSigma, pintzGlobalLowDensityBudget,
      pintzCarlsonLowDensityIndices] using hLowLimit
  have hHighLimit' :
      Tendsto
        (fun x : ℝ =>
          (n : ℝ) *
            ((ZeroDensity.zeroDensityCount sigma0
                (pintzCarlsonHeight rate x) : ℝ) *
              Real.exp (-Pintz.pintzZeroEnvelope x)))
        atTop (nhds 0) := by
    simpa [anchorSigma,
      pintzCarlsonClassicalAggregatedDensityLayerTerm,
      pintzCarlsonAggregatedDensityLayerTerm] using hHighLimit
  simpa only [anchoredMovingSigmaDensityMajorant, mul_assoc, zero_add] using
    hLowLimit'.add hHighLimit'

/-- Anchoring turns the fixed Carlson theorem into the uniform moving-threshold
density input required by the explicit formula. -/
theorem exists_pintzConstant_anchoredUniformMovingSigmaDensityDecay
    {n : ℕ} (sigma0 : ℝ)
    (hhalf : 1 / 2 < sigma0) (hlt : sigma0 < 1)
    (inputAtHeight : ∀ T : ℝ, PositiveZeroBucketInput T n)
    (hanchor : MovingSigmaAnchoredAt sigma0 inputAtHeight) :
    ∃ c > 0, ∀ rate : ℝ, 0 < rate → rate < 2 * Real.sqrt c →
      UniformMovingSigmaHybridDensityDecay rate inputAtHeight := by
  rcases
      exists_pintzConstant_anchoredMovingSigmaDensityMajorant_tendsto
        n sigma0 hhalf hlt with
    ⟨c, hc, hmajorant⟩
  refine ⟨c, hc, ?_⟩
  intro rate hrate hgap height _hheight
  have hmajorantNat :=
    (hmajorant rate hrate hgap).comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ hmajorantNat
  · exact Filter.Eventually.of_forall fun m : ℕ =>
      pintzCarlsonHybridDensityBudget_nonneg
        (inputAtHeight (height m)).sigma (m : ℝ)
          (pintzCarlsonHeight rate (m : ℝ))
  · exact Filter.Eventually.of_forall fun m : ℕ =>
      pintzCarlsonHybridDensityBudget_le_anchoredMajorant
        (inputAtHeight (height m)).sigma
        (hanchor (height m)) (m : ℝ)
          (pintzCarlsonHeight rate (m : ℝ))

/-- Actual PNT transfer for arbitrary height-dependent threshold families
whose high thresholds stay to the right of one fixed Carlson anchor. -/
theorem exists_fixedRate_anchoredMovingSigma_relativeChebyshevPsi0Error_tendsto
    {n : ℕ} (sigma0 : ℝ)
    (hhalf : 1 / 2 < sigma0) (hlt : sigma0 < 1)
    (inputAtHeight : ∀ T : ℝ, PositiveZeroBucketInput T n)
    (hanchor : MovingSigmaAnchoredAt sigma0 inputAtHeight) :
    ∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) := by
  rcases
      exists_pintzConstant_anchoredUniformMovingSigmaDensityDecay
        sigma0 hhalf hlt inputAtHeight hanchor with
    ⟨c, hc, hdensity⟩
  let rate : ℝ := min 1 (Real.sqrt c)
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hrate : 0 < rate := lt_min zero_lt_one hsqrt
  have hrateOne : rate ≤ 1 := min_le_left 1 (Real.sqrt c)
  have hrateSqrt : rate ≤ Real.sqrt c :=
    min_le_right 1 (Real.sqrt c)
  have hgap : rate < 2 * Real.sqrt c := by
    linarith
  rcases
      exists_movingSigma_relativeChebyshevPsi0Error_tendsto
        hrate hrateOne inputAtHeight
          (hdensity rate hrate hgap) with
    ⟨_C, _hC, herror⟩
  exact ⟨rate, hrate, hrateOne, herror⟩

end PrimeNumberTheorem
