import PrimeNumberTheorem.MWKFCubicActualMoment
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Complex MeasureTheory Set
open scoped ContDiff

namespace PrimeNumberTheorem.MWKFCubic

#check CubicTestWeight
#check CubicTestWeight.hasCompactSupport_dilate
#check cubicMollifierLength
#check cubicMomentIntegrand
#check cubicMollifiedSecondMoment

-- A mere projection check would accept the stronger, incorrect C^omega
-- hypothesis.  Construction from an arbitrary C^infty weight must work.
example (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Icc (1 : ℝ) 2) : CubicTestWeight :=
  ⟨f, hf, hs⟩

-- This nonzero bump rules out a vacuous class of analytic compact weights.
theorem cubicTestWeight_exists_value_one : ∃ W : CubicTestWeight, W (3 / 2) = 1 := by
  let f : ContDiffBump (3 / 2 : ℝ) :=
    ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hs : Function.support f ⊆ Icc (1 : ℝ) 2 := by
    rw [f.support_eq]
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    dsimp [f] at hx
    constructor <;> linarith [hx.1, hx.2]
  refine ⟨⟨f, f.contDiff, hs⟩, ?_⟩
  exact f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)

#print axioms cubicTestWeight_exists_value_one

#check (@cubicMollifierLength_cast_le :
  ∀ {T : ℝ}, 0 ≤ T → (cubicMollifierLength T : ℝ) ≤ T ^ 3)

#check (@cubicMomentIntegrand_eq_hardy :
  ∀ (W : CubicTestWeight) (T t : ℝ),
    cubicMomentIntegrand W T t =
      HardyTheorem.hardyZ t ^ 2 *
        Complex.normSq (HardyTheorem.selbergMoebiusMollifier
          (cubicMollifierLength T) ((1 / 2 : ℂ) + I * t)) * W (t / T))

#check (@integrable_cubicMomentIntegrand :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 →
    Integrable (cubicMomentIntegrand W T))

#check (@CubicTestWeight.hasCompactSupport_dilate :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 →
    HasCompactSupport (fun t : ℝ ↦ W (t / T)))

end PrimeNumberTheorem.MWKFCubic
