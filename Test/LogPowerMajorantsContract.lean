import MathlibAux.LogPowerMajorants

open Set MeasureTheory Complex
open scoped Interval

-- Keeps the low-height logarithm and both reflected high tails.
example {f : ℝ → ℂ} {A D b M K : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hb : 0 < b) (hM : 1 ≤ M) (hK : M ≤ K)
    (hf : ContinuousOn f (Icc (-K) K))
    (hlow : ∀ t ∈ Icc (-M) M, ‖f t‖ ≤ A / (b + |t|))
    (hhigh : ∀ t ∈ Icc (-K) K, M ≤ |t| → ‖f t‖ ≤ D * |t| ^ (-3 / 2 : ℝ)) :
    ‖∫ t in (-K)..K, f t‖ ≤ 2 * A * Real.log (1 + M / b) + 4 * D := by
  exact MathlibAux.norm_integral_le_log_power_majorants hA hD hb hM hK hf hlow hhigh

#print axioms MathlibAux.norm_integral_le_log_power_majorants
