import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonGap

open Filter Topology

namespace PrimeNumberTheorem

/-!
# Explicit square-root logarithmic truncation heights

This module turns the abstract height-rate parameter in the Pintz-Carlson gap
into the concrete schedule

`H_k(x) = exp (k * sqrt (log x))`.
-/

/-- The square-root logarithmic exponential truncation height. -/
noncomputable def pintzCarlsonHeight (k x : ℝ) : ℝ :=
  Real.exp (k * pintzCarlsonSqrtLogScale x)

/-- Every Pintz-Carlson candidate height is positive. -/
theorem pintzCarlsonHeight_pos (k x : ℝ) :
    0 < pintzCarlsonHeight k x :=
  Real.exp_pos _

/-- Every positive-rate Pintz-Carlson height tends to infinity. -/
theorem tendsto_pintzCarlsonHeight_atTop
    {k : ℝ} (hk : 0 < k) :
    Tendsto (pintzCarlsonHeight k) atTop atTop := by
  exact Real.tendsto_exp_atTop.comp
    (tendsto_pintzCarlsonSqrtLogScale_atTop.const_mul_atTop hk)

/-- The logarithm of the dynamic height is exactly its rate times the
square-root logarithmic scale. -/
theorem log_pintzCarlsonHeight (k x : ℝ) :
    Real.log (pintzCarlsonHeight k x) =
      k * pintzCarlsonSqrtLogScale x := by
  exact Real.log_exp _

/-- Real powers of the dynamic height become linear exponential rates. -/
theorem pintzCarlsonHeight_rpow (a k x : ℝ) :
    pintzCarlsonHeight k x ^ a =
      Real.exp (a * k * pintzCarlsonSqrtLogScale x) := by
  rw [Real.rpow_def_of_pos (pintzCarlsonHeight_pos k x)]
  rw [log_pintzCarlsonHeight]
  congr 1
  ring

/-- At the explicit height, the full classical Carlson power-log majorant
times the Pintz kernel is exactly the previously analyzed exponent-gap model.
-/
theorem pintzCarlsonMajorantKernel_eq_gapModel
    (C sigma k x : ℝ) :
    C *
          pintzCarlsonHeight k x ^ (4 * sigma * (1 - sigma)) *
          Real.log (pintzCarlsonHeight k x) ^ 4 *
          Real.exp (-Pintz.pintzZeroEnvelope x) =
      (C * k ^ 4) *
          pintzCarlsonSqrtLogScale x ^ 4 *
          Real.exp
            ((4 * sigma * (1 - sigma)) * k *
                pintzCarlsonSqrtLogScale x -
              Pintz.pintzZeroEnvelope x) := by
  rw [pintzCarlsonHeight_rpow, log_pintzCarlsonHeight]
  calc
    C *
          Real.exp
              ((4 * sigma * (1 - sigma)) * k *
                pintzCarlsonSqrtLogScale x) *
          (k * pintzCarlsonSqrtLogScale x) ^ 4 *
          Real.exp (-Pintz.pintzZeroEnvelope x) =
        (C * k ^ 4) *
          pintzCarlsonSqrtLogScale x ^ 4 *
          (Real.exp
              ((4 * sigma * (1 - sigma)) * k *
                pintzCarlsonSqrtLogScale x) *
            Real.exp (-Pintz.pintzZeroEnvelope x)) := by
      ring
    _ =
        (C * k ^ 4) *
          pintzCarlsonSqrtLogScale x ^ 4 *
          Real.exp
            ((4 * sigma * (1 - sigma)) * k *
                pintzCarlsonSqrtLogScale x +
              -Pintz.pintzZeroEnvelope x) := by
      rw [Real.exp_add]
    _ =
        (C * k ^ 4) *
          pintzCarlsonSqrtLogScale x ^ 4 *
          Real.exp
            ((4 * sigma * (1 - sigma)) * k *
                pintzCarlsonSqrtLogScale x -
              Pintz.pintzZeroEnvelope x) := by
      ring

/-- There is an unconditional Pintz constant such that every positive common
height rate below `2 * sqrt c` makes the full fixed-strip Carlson majorant,
including its fourth logarithmic power, vanish after multiplication by the
actual Pintz envelope kernel. -/
theorem exists_pintzConstant_carlsonMajorantAtHeight_tendsto :
    ∃ c > 0, ∀ (C sigma k : ℝ), 0 ≤ C → 0 < k →
      k < 2 * Real.sqrt c →
      Tendsto
        (fun x : ℝ =>
          C *
            pintzCarlsonHeight k x ^ (4 * sigma * (1 - sigma)) *
            Real.log (pintzCarlsonHeight k x) ^ 4 *
            Real.exp (-Pintz.pintzZeroEnvelope x))
        atTop (𝓝 0) := by
  rcases exists_pintzConstant_carlsonWeightedKernel_tendsto with
    ⟨c, hc, hweighted⟩
  refine ⟨c, hc, ?_⟩
  intro C sigma k hC hk hkGap
  have hmodel :=
    hweighted
      (C * k ^ 4)
      4
      sigma
      k
      (mul_nonneg hC (by positivity))
      (carlsonClassicalExponent_mul_rate_lt_pintz
        sigma k c hk.le hkGap)
  have hmodelNat :
      Tendsto
        (fun x : ℝ =>
          (C * k ^ 4) *
            pintzCarlsonSqrtLogScale x ^ 4 *
            Real.exp
              ((4 * sigma * (1 - sigma)) * k *
                  pintzCarlsonSqrtLogScale x -
                Pintz.pintzZeroEnvelope x))
        atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using hmodel
  refine hmodelNat.congr' ?_
  filter_upwards with x
  exact (pintzCarlsonMajorantKernel_eq_gapModel C sigma k x).symm

/-- The full Pintz-weighted Carlson majorant tends to zero after summing over
any finite family of fixed real-part strips, all evaluated at one common
dynamic truncation height. -/
theorem exists_pintzConstant_finiteCarlsonMajorantAtHeight_tendsto
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι)
    (C sigma : ι → ℝ)
    (hC : ∀ i ∈ layers, 0 ≤ C i) :
    ∃ c > 0, ∀ k : ℝ, 0 < k → k < 2 * Real.sqrt c →
      Tendsto
        (fun x : ℝ =>
          ∑ i ∈ layers,
            C i *
              pintzCarlsonHeight k x ^
                (4 * sigma i * (1 - sigma i)) *
              Real.log (pintzCarlsonHeight k x) ^ 4 *
              Real.exp (-Pintz.pintzZeroEnvelope x))
        atTop (𝓝 0) := by
  rcases exists_pintzConstant_carlsonMajorantAtHeight_tendsto with
    ⟨c, hc, hstrip⟩
  refine ⟨c, hc, ?_⟩
  intro k hk hkGap
  apply tendsto_finset_sum
  intro i hi
  exact hstrip (C i) (sigma i) k (hC i hi) hk hkGap

end PrimeNumberTheorem
