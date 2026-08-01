import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonGap

open Filter Topology

namespace PrimeNumberTheorem

/-! Public contract for the quantitative Pintz-Carlson exponent gap. -/

example
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
  tendsto_carlsonExponent_pintzGap p sigma k c hgap

example :
    ∃ c > 0, ∀ᶠ x : ℝ in atTop,
      2 * Real.sqrt c * pintzCarlsonSqrtLogScale x ≤
        Pintz.pintzZeroEnvelope x :=
  exists_eventually_two_mul_sqrt_mul_scale_le_pintzZeroEnvelope

example
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
            pintzCarlsonSqrtLogScale x) :=
  pintzEnvelope_exp_kernel_le_gapKernel hP henvelope

example :
    ∃ c > 0, ∀ (C p sigma k : ℝ), 0 ≤ C →
      (4 * sigma * (1 - sigma)) * k < 2 * Real.sqrt c →
      Tendsto
        (fun x : ℝ =>
          C * pintzCarlsonSqrtLogScale x ^ p *
            Real.exp
              ((4 * sigma * (1 - sigma)) * k *
                  pintzCarlsonSqrtLogScale x -
                Pintz.pintzZeroEnvelope x))
        atTop (𝓝 0) :=
  exists_pintzConstant_carlsonWeightedKernel_tendsto

example (sigma : ℝ) :
    4 * sigma * (1 - sigma) ≤ 1 :=
  carlsonClassicalExponent_le_one sigma

example
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
        atTop (𝓝 0) :=
  exists_pintzConstant_finiteCarlsonLayerBudget_tendsto
    layers C p sigma hC

end PrimeNumberTheorem
