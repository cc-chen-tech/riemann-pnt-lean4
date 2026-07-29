import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonMovingBalancedMargin
import PrimeNumberTheorem.ZeroDensityLayerBudgetMovingGapBarrier

/-!
# Decay from a moving balanced Carlson margin

The arithmetic estimate

`balancedExponent (1 - delta) (1 - delta) alpha <= -delta / 2`

becomes analytic decay as soon as `delta(m) * log m -> infinity`.
-/

namespace PrimeNumberTheorem

open Filter Topology

noncomputable section

/-- Exponential form of the moving balanced power majorant. -/
noncomputable def carlsonMovingBalancedNormalizedRatio
  (alpha : ℝ) (delta : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.exp
    (carlsonTwoHeightBalancedExponent
        (1 - 2 * delta m) (1 - delta m) alpha *
      Real.log (m : ℝ))

/-- Divergence of `delta(m) * log m` kills the moving balanced Carlson
majorant. -/
theorem tendsto_carlsonMovingBalancedNormalizedRatio_zero
    {alpha : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 ≤ alpha)
    (hdelta :
      ∀ᶠ m : ℕ in atTop,
        0 < delta m ∧ delta m ≤ 1 / 2 ∧
          128 * alpha * delta m ≤ 1)
    (hlogGap :
      Tendsto
        (fun m : ℕ => delta m * Real.log (m : ℝ))
        atTop atTop) :
    Tendsto
      (carlsonMovingBalancedNormalizedRatio alpha delta)
      atTop (𝓝 0) := by
  have hhalfLogGap :
      Tendsto
        (fun m : ℕ => delta m / 2 * Real.log (m : ℝ))
        atTop atTop := by
    have hscaled :=
      hlogGap.const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
    refine hscaled.congr' ?_
    filter_upwards with m
    ring
  have hnegative :
      Tendsto
        (fun m : ℕ => -(delta m / 2 * Real.log (m : ℝ)))
        atTop atBot :=
    tendsto_neg_atTop_atBot.comp hhalfLogGap
  have hmajorant :
      Tendsto
        (fun m : ℕ =>
          Real.exp (-(delta m / 2 * Real.log (m : ℝ))))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hnegative
  refine squeeze_zero' ?_ ?_ hmajorant
  · exact Filter.Eventually.of_forall fun m =>
      (Real.exp_pos _).le
  · filter_upwards
      [hdelta, eventually_ge_atTop (1 : ℕ)] with m hmDelta hm
    have hlog : 0 ≤ Real.log (m : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast hm
    have hexponent :=
      carlsonTwoHeightBalancedExponent_movingStrip_le_neg_half
        hmDelta.1 hmDelta.2.1 halpha hmDelta.2.2
    unfold carlsonMovingBalancedNormalizedRatio
    rw [Real.exp_le_exp]
    have hscaled :=
      mul_le_mul_of_nonneg_right hexponent hlog
    calc
      carlsonTwoHeightBalancedExponent
            (1 - 2 * delta m) (1 - delta m) alpha *
          Real.log (m : ℝ)
          ≤ (-delta m / 2) * Real.log (m : ℝ) :=
        hscaled
      _ = -(delta m / 2 * Real.log (m : ℝ)) := by ring

end

end PrimeNumberTheorem
