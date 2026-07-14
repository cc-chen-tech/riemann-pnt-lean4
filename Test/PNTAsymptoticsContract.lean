import PrimeNumberTheorem.PNTAsymptotics

open Filter Topology

namespace PrimeNumberTheorem

example : Tendsto pntSqrtLog atTop atTop :=
  tendsto_pntSqrtLog_atTop

example (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Tendsto (fun m : ℕ =>
      pntSqrtLog m ^ k * Real.exp (-a * pntSqrtLog m))
      atTop (𝓝 0) :=
  tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero a ha k

example (a : ℝ) (ha : 0 < a) :
    Tendsto (fun m : ℕ =>
      (1 + Real.log (m : ℝ)) ^ 2 * Real.exp (-a * pntSqrtLog m))
      atTop (𝓝 0) :=
  tendsto_one_add_log_sq_mul_exp_neg_pntSqrtLog_atTop_nhds_zero a ha

example (a : ℝ) (ha : 0 < a) :
    Tendsto (fun m : ℕ =>
      (1 + pntSqrtLog m) ^ 2 * Real.exp (-a * pntSqrtLog m))
      atTop (𝓝 0) :=
  tendsto_one_add_pntSqrtLog_sq_mul_exp_neg_mul_atTop_nhds_zero a ha

end PrimeNumberTheorem
