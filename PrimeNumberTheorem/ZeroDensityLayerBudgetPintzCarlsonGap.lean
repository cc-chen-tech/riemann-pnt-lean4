import PrimeNumberTheorem.PintzEnvelope

open Filter Topology

namespace PrimeNumberTheorem

/-!
# The quantitative Pintz-Carlson exponent gap

For a candidate height of square-root logarithmic exponential scale,

`H(x) = exp (k * sqrt (log x))`,

a density factor `H(x)^a` contributes the exponential rate `a * k`, while a
Pintz envelope lower bound of size `2 * sqrt(c * log x)` contributes the
decay rate `2 * sqrt c`. The strict inequality

`a * k < 2 * sqrt c`

is the quantitative room needed to absorb every fixed power of
`sqrt (log x)`.
-/

/-- The real square-root logarithmic scale. -/
noncomputable def pintzCarlsonSqrtLogScale (x : ℝ) : ℝ :=
  Real.sqrt (Real.log x)

/-- The real square-root logarithmic scale tends to infinity. -/
theorem tendsto_pintzCarlsonSqrtLogScale_atTop :
    Tendsto pintzCarlsonSqrtLogScale atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop

/-- The proved Pintz envelope lower bound expressed on the common
square-root logarithmic scale used by the Carlson gap calculation. -/
theorem exists_eventually_two_mul_sqrt_mul_scale_le_pintzZeroEnvelope :
    ∃ c > 0, ∀ᶠ x : ℝ in atTop,
      2 * Real.sqrt c * pintzCarlsonSqrtLogScale x ≤
        Pintz.pintzZeroEnvelope x := by
  rcases Pintz.exists_eventually_two_mul_sqrt_le_zeroEnvelope with
    ⟨c, hc, henvelope⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), henvelope] with x hx hbound
  have hsqrtmul :
      Real.sqrt (c * Real.log x) =
        Real.sqrt c * Real.sqrt (Real.log x) := by
    simpa using Real.sqrt_mul hc.le (Real.log x)
  simpa [pintzCarlsonSqrtLogScale, hsqrtmul, mul_assoc] using hbound

/-- A lower bound for an envelope turns into an upper bound for the
corresponding exponentially weighted kernel. The nonnegative factor `P`
can contain the density majorant and logarithmic losses. -/
theorem pintzEnvelope_exp_kernel_le_gapKernel
    {E P : ℝ → ℝ} {a k c x : ℝ}
    (hP : 0 ≤ P x)
    (henvelope :
      2 * Real.sqrt c * pintzCarlsonSqrtLogScale x ≤ E x) :
    P x *
        Real.exp
          (a * k * pintzCarlsonSqrtLogScale x - E x) ≤
      P x *
        Real.exp
          ((a * k - 2 * Real.sqrt c) *
            pintzCarlsonSqrtLogScale x) := by
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    nlinarith
  · exact hP

/-- Eventual envelope domination plus decay of the explicit gap model imply
decay of the envelope-weighted kernel itself. -/
theorem tendsto_pintzEnvelopeWeightedKernel_of_gap
    {E P : ℝ → ℝ} {a k c : ℝ}
    (hP : ∀ x, 0 ≤ P x)
    (henvelope :
      ∀ᶠ x : ℝ in atTop,
        2 * Real.sqrt c * pintzCarlsonSqrtLogScale x ≤ E x)
    (hgapModel :
      Tendsto
        (fun x : ℝ =>
          P x *
            Real.exp
              ((a * k - 2 * Real.sqrt c) *
                pintzCarlsonSqrtLogScale x))
        atTop (𝓝 0)) :
    Tendsto
      (fun x : ℝ =>
        P x *
          Real.exp
            (a * k * pintzCarlsonSqrtLogScale x - E x))
      atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ hgapModel
  · exact Filter.Eventually.of_forall fun x =>
      mul_nonneg (hP x) (Real.exp_pos _).le
  · filter_upwards [henvelope] with x hx
    exact pintzEnvelope_exp_kernel_le_gapKernel (hP x) hx

/-- Any fixed real power is absorbed by the strict Pintz-Carlson exponential
gap. The parameter `a` is the density exponent and `k` is the exponential
height rate. -/
theorem tendsto_pintzCarlsonGap_rpow_mul_exp
    (p a k c : ℝ) (hgap : a * k < 2 * Real.sqrt c) :
    Tendsto
      (fun x : ℝ =>
        pintzCarlsonSqrtLogScale x ^ p *
          Real.exp
            ((a * k - 2 * Real.sqrt c) *
              pintzCarlsonSqrtLogScale x))
      atTop (𝓝 0) := by
  let d := 2 * Real.sqrt c - a * k
  have hd : 0 < d := by
    dsimp [d]
    linarith
  have hreal :
      Tendsto
        (fun u : ℝ => u ^ p * Real.exp (-d * u))
        atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p d hd
  refine
    (hreal.comp tendsto_pintzCarlsonSqrtLogScale_atTop).congr' ?_
  filter_upwards with x
  have harg :
      -d * pintzCarlsonSqrtLogScale x =
        (a * k - 2 * Real.sqrt c) *
          pintzCarlsonSqrtLogScale x := by
    dsimp [d]
    ring
  change
    pintzCarlsonSqrtLogScale x ^ p *
        Real.exp (-d * pintzCarlsonSqrtLogScale x) =
      pintzCarlsonSqrtLogScale x ^ p *
        Real.exp
          ((a * k - 2 * Real.sqrt c) *
            pintzCarlsonSqrtLogScale x)
  rw [harg]

/-- Carlson's classical fixed-strip exponent inserted into the gap criterion.
This is the exact admissible-rate inequality for the power part of the
classical density majorant. -/
theorem tendsto_carlsonExponent_pintzGap
    (p sigma k c : ℝ)
    (hgap :
      (4 * sigma * (1 - sigma)) * k < 2 * Real.sqrt c) :
    Tendsto
      (fun x : ℝ =>
        pintzCarlsonSqrtLogScale x ^ p *
          Real.exp
            (((4 * sigma * (1 - sigma)) * k -
                2 * Real.sqrt c) *
              pintzCarlsonSqrtLogScale x))
      atTop (𝓝 0) :=
  tendsto_pintzCarlsonGap_rpow_mul_exp
    p (4 * sigma * (1 - sigma)) k c hgap

/-- A fixed nonnegative Carlson coefficient does not change the exponent-gap
limit. This is the form used after extracting a concrete Big-O constant. -/
theorem tendsto_const_mul_carlsonExponent_pintzGap
    (C p sigma k c : ℝ)
    (hgap :
      (4 * sigma * (1 - sigma)) * k < 2 * Real.sqrt c) :
    Tendsto
      (fun x : ℝ =>
        C *
          (pintzCarlsonSqrtLogScale x ^ p *
            Real.exp
              (((4 * sigma * (1 - sigma)) * k -
                  2 * Real.sqrt c) *
                pintzCarlsonSqrtLogScale x)))
      atTop (𝓝 0) := by
  simpa only [mul_zero] using
    (tendsto_carlsonExponent_pintzGap p sigma k c hgap).const_mul C

/-- The fourth logarithmic power in Carlson's classical majorant, represented
as a fixed fourth power of the square-root logarithmic scale, is absorbed by
the same strict exponent gap. -/
theorem tendsto_carlsonFourthPower_pintzGap
    (C sigma k c : ℝ)
    (hgap :
      (4 * sigma * (1 - sigma)) * k < 2 * Real.sqrt c) :
    Tendsto
      (fun x : ℝ =>
        C *
          (pintzCarlsonSqrtLogScale x ^ (4 : ℝ) *
            Real.exp
              (((4 * sigma * (1 - sigma)) * k -
                  2 * Real.sqrt c) *
                pintzCarlsonSqrtLogScale x)))
      atTop (𝓝 0) :=
  tendsto_const_mul_carlsonExponent_pintzGap
    C 4 sigma k c hgap

/-- There is an unconditional Pintz constant for which every fixed Carlson
strip satisfying the strict height-rate gap has a vanishing
Pintz-envelope-weighted majorant. This is the concrete analytic bridge between
the existing Pintz envelope theorem and Carlson's classical density exponent.
-/
theorem exists_pintzConstant_carlsonWeightedKernel_tendsto :
    ∃ c > 0, ∀ (C p sigma k : ℝ), 0 ≤ C →
      (4 * sigma * (1 - sigma)) * k < 2 * Real.sqrt c →
      Tendsto
        (fun x : ℝ =>
          C * pintzCarlsonSqrtLogScale x ^ p *
            Real.exp
              ((4 * sigma * (1 - sigma)) * k *
                  pintzCarlsonSqrtLogScale x -
                Pintz.pintzZeroEnvelope x))
        atTop (𝓝 0) := by
  rcases
      exists_eventually_two_mul_sqrt_mul_scale_le_pintzZeroEnvelope with
    ⟨c, hc, henvelope⟩
  refine ⟨c, hc, ?_⟩
  intro C p sigma k hC hgap
  have hmodel :
      Tendsto
        (fun x : ℝ =>
          (C * pintzCarlsonSqrtLogScale x ^ p) *
            Real.exp
              (((4 * sigma * (1 - sigma)) * k -
                  2 * Real.sqrt c) *
                pintzCarlsonSqrtLogScale x))
        atTop (𝓝 0) := by
    simpa only [mul_assoc] using
      tendsto_const_mul_carlsonExponent_pintzGap
        C p sigma k c hgap
  have hweighted :=
    tendsto_pintzEnvelopeWeightedKernel_of_gap
      (E := Pintz.pintzZeroEnvelope)
      (P := fun x => C * pintzCarlsonSqrtLogScale x ^ p)
      (a := 4 * sigma * (1 - sigma))
      (k := k)
      (c := c)
      (fun x => by
        apply mul_nonneg hC
        exact Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      henvelope
      hmodel
  simpa only [mul_assoc] using hweighted

/-- Carlson's classical exponent never exceeds one. This elementary bound
makes one common height rate admissible for every fixed real-part strip. -/
theorem carlsonClassicalExponent_le_one (sigma : ℝ) :
    4 * sigma * (1 - sigma) ≤ 1 := by
  nlinarith [sq_nonneg (2 * sigma - 1)]

/-- A common nonnegative height rate strictly below the Pintz rate satisfies
the Carlson gap for every real-part parameter. -/
theorem carlsonClassicalExponent_mul_rate_lt_pintz
    (sigma k c : ℝ)
    (hk : 0 ≤ k)
    (hkGap : k < 2 * Real.sqrt c) :
    (4 * sigma * (1 - sigma)) * k < 2 * Real.sqrt c :=
  (mul_le_mul_of_nonneg_right
      (carlsonClassicalExponent_le_one sigma) hk).trans_lt hkGap

/-- A single unconditional Pintz constant and a single admissible height rate
control every finite family of Carlson real-part strips. Each strip may have
its own nonnegative coefficient and fixed logarithmic power, but all strips
use the same dynamic height scale. -/
theorem exists_pintzConstant_finiteCarlsonLayerBudget_tendsto
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι)
    (C p sigma : ι → ℝ)
    (hC : ∀ i ∈ layers, 0 ≤ C i) :
    ∃ c > 0, ∀ k : ℝ, 0 ≤ k → k < 2 * Real.sqrt c →
      Tendsto
        (fun x : ℝ =>
          ∑ i ∈ layers,
            C i * pintzCarlsonSqrtLogScale x ^ p i *
              Real.exp
                ((4 * sigma i * (1 - sigma i)) * k *
                    pintzCarlsonSqrtLogScale x -
                  Pintz.pintzZeroEnvelope x))
        atTop (𝓝 0) := by
  rcases exists_pintzConstant_carlsonWeightedKernel_tendsto with
    ⟨c, hc, hstrip⟩
  refine ⟨c, hc, ?_⟩
  intro k hk hkGap
  apply tendsto_finset_sum
  intro i hi
  exact hstrip
    (C i)
    (p i)
    (sigma i)
    k
    (hC i hi)
    (carlsonClassicalExponent_mul_rate_lt_pintz
      (sigma i) k c hk hkGap)

end PrimeNumberTheorem
