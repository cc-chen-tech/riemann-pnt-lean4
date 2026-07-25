import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzKernelAutomatic
import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonTargetLayer

/-!
# Dynamic actual-zeta layers for target-amplitude transfer

At every explicit-formula scale `x`, a dynamic height `T(x)` gives a finite
set of actual zeta zeros.  This file forms the norm of one
multiplicity-weighted PNT zero bucket and proves its pointwise domination by
the actual Carlson count times the automatic Pintz kernel majorant.

The normalized asymptotic estimate is deliberately a separate hypothesis.
This prevents a Carlson `BigO` count from being confused with the still-missing
upper-endpoint control for the kernels inside a real-part strip.
-/

open scoped BigOperators

namespace PrimeNumberTheorem

open Filter

/-- Norm of one actual multiplicity-weighted PNT zero bucket at the dynamic
height `T(x)`. -/
noncomputable def dynamicPositivePNTLayerNorm
    {n : ℕ} (T : ℝ → ℝ)
    (input : (x : ℝ) → PositiveZeroBucketInput (T x) n)
    (i : Fin n) (x : ℝ) : ℝ :=
  ‖∑ rho ∈ (input x).layer i,
      pntRelativeZeroContribution x rho‖

/-- Actual Carlson multiplicity count at a fixed strip threshold and dynamic
height. -/
noncomputable def dynamicCarlsonLayerCount
    (sigma : ℝ) (T : ℝ → ℝ) (x : ℝ) : ℝ :=
  ZeroDensity.zeroDensityCount sigma (T x)

/-- Automatic Pintz majorant for one actual relative PNT zero kernel. -/
noncomputable def dynamicPintzRelativeKernelBudget
    (x : ℝ) : ℝ :=
  Real.exp (-Pintz.pintzZeroEnvelope x)

/-- One actual zeta bucket is pointwise bounded by its fixed-threshold Carlson
count times the automatic Pintz kernel majorant.  Analytic multiplicity is
accounted for exactly once through `zeroDensityCount`. -/
theorem dynamicPositivePNTLayerNorm_le_carlson_mul_pintz
    {n : ℕ} {T : ℝ → ℝ}
    (input : (x : ℝ) → PositiveZeroBucketInput (T x) n)
    (i : Fin n) (sigma : ℝ)
    (hsigma : ∀ x, (input x).sigma i = sigma)
    {x : ℝ} (hx : 1 ≤ x) :
    |dynamicPositivePNTLayerNorm T input i x| ≤
      dynamicCarlsonLayerCount sigma T x *
        dynamicPintzRelativeKernelBudget x := by
  have hkernel :
      ∀ rho ∈ (input x).layer i,
        ‖pntRelativeSimpleZeroKernel x rho‖ ≤
          Real.exp (-Pintz.pintzZeroEnvelope x) := by
    intro rho hrho
    have hpositive : rho ∈ positiveNontrivialZerosFinset (T x) :=
      (Finset.mem_filter.mp hrho).1
    have hzero := mem_positiveNontrivialZerosFinset.mp hpositive
    exact norm_pntRelativeSimpleZeroKernel_le_exp_neg_pintzEnvelope
      hx hzero.1 hzero.2.1
  calc
    |dynamicPositivePNTLayerNorm T input i x| =
        dynamicPositivePNTLayerNorm T input i x := by
      exact abs_of_nonneg (norm_nonneg _)
    _ ≤ ∑ rho ∈ (input x).layer i,
          ‖pntRelativeZeroContribution x rho‖ := by
      exact norm_sum_le _ _
    _ ≤ Real.exp (-Pintz.pintzZeroEnvelope x) *
          (ZeroDensity.zeroDensityCount ((input x).sigma i) (T x) : ℝ) :=
      (input x).sum_norm_pntRelativeZeroContribution_layer_le_count'
        i hkernel
    _ = dynamicCarlsonLayerCount sigma T x *
          dynamicPintzRelativeKernelBudget x := by
      rw [hsigma x]
      simp [dynamicCarlsonLayerCount,
        dynamicPintzRelativeKernelBudget, mul_comm]

/-- The actual Carlson count is nonnegative at every scale. -/
theorem dynamicCarlsonLayerCount_nonneg
    (sigma : ℝ) (T : ℝ → ℝ) (x : ℝ) :
    0 ≤ dynamicCarlsonLayerCount sigma T x := by
  unfold dynamicCarlsonLayerCount
  exact_mod_cast
    (Nat.zero_le (ZeroDensity.zeroDensityCount sigma (T x)))

/-- The automatic Pintz kernel budget is positive at every scale. -/
theorem dynamicPintzRelativeKernelBudget_pos
    (x : ℝ) :
    0 < dynamicPintzRelativeKernelBudget x := by
  exact Real.exp_pos _

/-- An actual dynamic zeta bucket becomes a
`PintzCarlsonTargetLayerBudget` once the genuinely missing normalized product
estimate is supplied. -/
theorem dynamicPositivePNTLayerNorm_pintzCarlsonTargetLayerBudget
    {n : ℕ} {T amplitude : ℝ → ℝ}
    (input : (x : ℝ) → PositiveZeroBucketInput (T x) n)
    (i : Fin n) (sigma : ℝ)
    (hsigma : ∀ x, (input x).sigma i = sigma)
    (hnormalized :
      Filter.Tendsto
        (fun x =>
          dynamicCarlsonLayerCount sigma T x *
              dynamicPintzRelativeKernelBudget x /
            amplitude x)
        Filter.atTop (nhds 0)) :
    PintzCarlsonTargetLayerBudget amplitude
      (dynamicPositivePNTLayerNorm T input i)
      (dynamicCarlsonLayerCount sigma T)
      dynamicPintzRelativeKernelBudget where
  count_eventually_nonneg :=
    Filter.Eventually.of_forall
      (dynamicCarlsonLayerCount_nonneg sigma T)
  kernel_eventually_nonneg :=
    Filter.Eventually.of_forall fun x =>
      (dynamicPintzRelativeKernelBudget_pos x).le
  layer_abs_le_count_mul_kernel := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact dynamicPositivePNTLayerNorm_le_carlson_mul_pintz
      input i sigma hsigma hx
  normalized_product_tendsto_zero := hnormalized

/-- Target-amplitude negligibility for an actual zeta bucket, with the exact
remaining normalized product exposed as a premise. -/
theorem dynamicPositivePNTLayerNorm_targetAmplitudeNegligible
    {n : ℕ} {T amplitude : ℝ → ℝ}
    (input : (x : ℝ) → PositiveZeroBucketInput (T x) n)
    (i : Fin n) (sigma : ℝ)
    (hsigma : ∀ x, (input x).sigma i = sigma)
    (hamplitude : ∀ᶠ x in Filter.atTop, 0 < amplitude x)
    (hnormalized :
      Filter.Tendsto
        (fun x =>
          dynamicCarlsonLayerCount sigma T x *
              dynamicPintzRelativeKernelBudget x /
            amplitude x)
        Filter.atTop (nhds 0)) :
    TargetAmplitudeNegligible amplitude
      (dynamicPositivePNTLayerNorm T input i) :=
  (dynamicPositivePNTLayerNorm_pintzCarlsonTargetLayerBudget
    input i sigma hsigma hnormalized).targetAmplitudeNegligible hamplitude

end PrimeNumberTheorem
