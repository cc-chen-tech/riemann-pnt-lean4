import PrimeNumberTheorem.VKEdgePiOverTwoAbelDual

open Filter Set Topology

open scoped Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check realAbelMean
#check missingOddHarmonicKernel
#check sharpenedMissingHarmonicLowerBound

example {f : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T) (hf : Function.Periodic f T)
    (hcont : Continuous f) :
    Tendsto (realAbelMean f) (𝓝[>] 0)
      (𝓝 ((1 / T) * ∫ y in (0 : ℝ)..T, f y)) :=
  tendsto_realAbelMean_of_continuous_periodic hT hf hcont

example (k : ℕ) (theta : ℝ) :
    |Real.cos (((2 * k + 1 : ℕ) : ℝ) * theta)| ≤
      ((2 * k + 1 : ℕ) : ℝ) * |Real.cos theta| :=
  abs_cos_odd_mul_le k theta

example (k : ℕ) :
    (∫ theta in (0 : ℝ)..2 * Real.pi,
        |missingOddHarmonicKernel k theta|) =
      4 - 2 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) :=
  integral_abs_missingOddHarmonicKernel k

example (k : ℕ) :
    Real.pi / 2 < sharpenedMissingHarmonicLowerBound k :=
  pi_div_two_lt_sharpenedMissingHarmonicLowerBound k

example {h q : ℝ → ℝ} {K Q D : ℝ}
    (hbound : ∀ y ∈ Set.Ioi (0 : ℝ), |h y| ≤ K)
    (hqint : ∀ a : ℝ, 0 < a →
      MeasureTheory.IntegrableOn
        (fun y => Real.exp (-a * y) * |q y|)
        (Set.Ioi 0))
    (hlim : Tendsto (realAbelMean (fun y => h y * q y))
      (𝓝[>] 0) (𝓝 Q))
    (hqlim : Tendsto (realAbelMean (fun y => |q y|))
      (𝓝[>] 0) (𝓝 D)) :
    |Q| ≤ K * D :=
  abs_limit_realAbelMean_mul_le_of_global_bound
    hbound hqint hlim hqlim

example {h q : ℝ → ℝ} {K Q D Y : ℝ}
    (hK : 0 ≤ K) (hY : 0 ≤ Y)
    (hbound : ∀ y ∈ Set.Ioi Y, |h y| ≤ K)
    (hprefix :
      MeasureTheory.IntegrableOn
        (fun y => h y * q y) (Set.Ioc 0 Y))
    (hint : ∀ a : ℝ, 0 < a →
      MeasureTheory.IntegrableOn
        (fun y => Real.exp (-a * y) * (h y * q y))
        (Set.Ioi 0))
    (hqint : ∀ a : ℝ, 0 < a →
      MeasureTheory.IntegrableOn
        (fun y => Real.exp (-a * y) * |q y|)
        (Set.Ioi 0))
    (hlim : Tendsto (realAbelMean (fun y => h y * q y))
      (𝓝[>] 0) (𝓝 Q))
    (hqlim : Tendsto (realAbelMean (fun y => |q y|))
      (𝓝[>] 0) (𝓝 D)) :
    |Q| ≤ K * D :=
  abs_limit_realAbelMean_mul_le_of_tail_bound
    hK hY hbound hprefix hint hqint hlim hqlim

end VKEdgePiOverTwo
end PrimeNumberTheorem
