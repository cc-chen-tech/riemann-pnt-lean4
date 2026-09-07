import HardyTheorem.ConreyExplicitCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring

/-!
# Summable error budget for the explicit Conrey mollifier length

This module proves convergence and decay of an explicit numerical envelope,
not a bound for the actual shifted zeta moment. Establishing the Gaussian
kernel and DI arithmetic estimates needed to use this envelope is separate.

The kernel and arithmetic epsilon losses are both `1/200000`, strictly less
than `eta = 1/100000`. This is essential for the infinite dyadic sum. The
Gaussian parameter is `delta = 1/100000`; both contour choices are included
in the common loss, including the positive `delta * eta` term.

See `docs/research/2026-08-30-conrey-long-moment-uniformity-audit.md`.
-/

open Filter
open scoped Topology

namespace HardyTheorem

private theorem conreyLongMoment_dyadic_hasSum :
    HasSum (fun j : ℕ =>
      ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 200000 - 1 / 100000))
      (1 - (2 : ℝ) ^ (-(1 : ℝ) / 200000))⁻¹ := by
  have h := hasSum_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(1 : ℝ) / 200000))
    (Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : (1 : ℝ) < 2) (by norm_num : -(1 : ℝ) / 200000 < 0))
  have he : (1 : ℝ) / 200000 - 1 / 100000 = -(1 : ℝ) / 200000 := by norm_num
  simpa only [he, Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)] using h

/-- The actual infinite dyadic envelope is summable, not merely a totalized
`tsum` assigned zero by convention for a divergent series. -/
theorem conreyLongMoment_dyadic_summable : Summable (fun j : ℕ =>
    ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 200000 - 1 / 100000)) :=
  conreyLongMoment_dyadic_hasSum.summable

theorem conreyLongMoment_dyadic_tsum :
    (∑' j : ℕ, ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 200000 - 1 / 100000)) =
      (1 - (2 : ℝ) ^ (-(1 : ℝ) / 200000))⁻¹ :=
  conreyLongMoment_dyadic_hasSum.tsum_eq

/-- The complete common power loss before absorbing logarithmic counts. -/
noncomputable def conreyLongMomentCommonLoss : ℝ :=
  (7 / 2 : ℝ) * (1 / 100000) +
    (1 + 1 / 100000 + 2 * conreyExplicitTheta) * (1 / 100000) +
    1 / 200000 + 1 / 200000

/-- The dyadically summed continuous-contour envelope, with `L = log T`.
No assertion about an actual contour remainder is built into this definition. -/
noncomputable def conreyLongMomentErrorEnvelope (L : ℝ) : ℝ :=
  (1 + L) ^ 3 * Real.exp (conreyLongMomentCommonLoss * L) *
    (Real.exp ((-1 / 2 + 7 * conreyExplicitTheta / 8) * L) +
      Real.exp ((-1 + 7 * conreyExplicitTheta / 4) * L)) *
    ∑' j : ℕ, ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 200000 - 1 / 100000)

private theorem tendsto_one_add_cube_mul_exp_neg {b : ℝ} (hb : 0 < b) :
    Tendsto (fun L : ℝ => (1 + L) ^ 3 * Real.exp (-b * L)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => x ^ 3 * Real.exp (-b * x))
      atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 : ℕ) b hb
  have hshift := hbase.comp (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
  have h := hshift.const_mul (Real.exp b)
  simp only [mul_zero] at h
  apply h.congr'
  exact Eventually.of_forall fun L => by
    change Real.exp b * ((1 + L) ^ 3 * Real.exp (-b * (1 + L))) = _
    calc
      _ = (1 + L) ^ 3 * (Real.exp b * Real.exp (-b * (1 + L))) := by ring
      _ = (1 + L) ^ 3 * Real.exp (-b * L) := by
        rw [← Real.exp_add]
        congr 2
        ring

/-- After multiplication by `T^(1/4000)`, the complete explicit envelope
still tends to zero. This is a power-saving for the envelope, not a theorem
about the as-yet-unproved long mollified mean value. -/
theorem conreyLongMoment_errorEnvelope_scaled_tendsto_zero :
    Tendsto (fun L : ℝ => conreyLongMomentErrorEnvelope L * Real.exp (L / 4000))
      atTop (𝓝 0) := by
  have h₁ := tendsto_one_add_cube_mul_exp_neg
    (by norm_num : (0 : ℝ) < 585799 / 10000000000)
  have h₂ := tendsto_one_add_cube_mul_exp_neg
    (by norm_num : (0 : ℝ) < 4335799 / 10000000000)
  have h := (h₁.add h₂).mul_const
    (∑' j : ℕ, ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 200000 - 1 / 100000))
  simp only [zero_add, zero_mul] at h
  apply h.congr'
  refine Eventually.of_forall fun L => ?_
  dsimp [conreyLongMomentErrorEnvelope]
  have he₁ : Real.exp (conreyLongMomentCommonLoss * L) *
      Real.exp ((-1 / 2 + 7 * conreyExplicitTheta / 8) * L) *
      Real.exp (L / 4000) = Real.exp (-(585799 / 10000000000) * L) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    norm_num [conreyLongMomentCommonLoss, conreyExplicitTheta]
    ring
  have he₂ : Real.exp (conreyLongMomentCommonLoss * L) *
      Real.exp ((-1 + 7 * conreyExplicitTheta / 4) * L) *
      Real.exp (L / 4000) = Real.exp (-(4335799 / 10000000000) * L) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    norm_num [conreyLongMomentCommonLoss, conreyExplicitTheta]
    ring
  rw [← he₁, ← he₂]
  ring

end HardyTheorem
