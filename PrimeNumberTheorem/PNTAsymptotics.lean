import Mathlib

open Filter Topology

namespace PrimeNumberTheorem

/-- The square-root logarithmic scale used for the dynamic PNT height. -/
noncomputable def pntSqrtLog (m : ℕ) : ℝ :=
  Real.sqrt (Real.log (m : ℝ))

/-- The square-root logarithmic scale tends to infinity along natural numbers. -/
theorem tendsto_pntSqrtLog_atTop :
    Tendsto pntSqrtLog atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- Every fixed polynomial in the square-root logarithmic scale is dominated
by a positive exponential decay in that scale. -/
theorem tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero
    (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Tendsto (fun m : ℕ =>
      pntSqrtLog m ^ k * Real.exp (-a * pntSqrtLog m))
      atTop (𝓝 0) := by
  have hreal : Tendsto (fun u : ℝ => u ^ k * Real.exp (-a * u))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) a ha)
  exact hreal.comp tendsto_pntSqrtLog_atTop

/-- A direct quadratic corollary in the square-root logarithmic scale. -/
theorem tendsto_one_add_pntSqrtLog_sq_mul_exp_neg_mul_atTop_nhds_zero
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun m : ℕ =>
      (1 + pntSqrtLog m) ^ 2 * Real.exp (-a * pntSqrtLog m))
      atTop (𝓝 0) := by
  have h0 :=
    tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero a ha 0
  have h1 :=
    tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero a ha 1
  have h2 :=
    tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero a ha 2
  have hsum := h0.add ((h1.const_mul 2).add h2)
  simpa only [zero_add, mul_zero] using hsum.congr' (by
    filter_upwards with m
    ring)

/-- A direct logarithmic-square corollary at the dynamic PNT height. -/
theorem tendsto_one_add_log_sq_mul_exp_neg_pntSqrtLog_atTop_nhds_zero
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun m : ℕ =>
      (1 + Real.log (m : ℝ)) ^ 2 * Real.exp (-a * pntSqrtLog m))
      atTop (𝓝 0) := by
  have h0 :=
    tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero a ha 0
  have h2 :=
    tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero a ha 2
  have h4 :=
    tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero a ha 4
  have hsum := h0.add ((h2.const_mul 2).add h4)
  simpa only [zero_add, mul_zero] using hsum.congr' (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hlog_nonneg : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hm)
    have hscale_sq : pntSqrtLog m ^ 2 = Real.log (m : ℝ) := by
      simpa only [pntSqrtLog] using Real.sq_sqrt hlog_nonneg
    rw [← hscale_sq]
    ring)

end PrimeNumberTheorem
