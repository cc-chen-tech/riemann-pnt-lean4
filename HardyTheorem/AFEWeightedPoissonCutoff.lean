import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# A smooth compact cutoff for the weighted Poisson step in the critical AFE

Titchmarsh's finite weighted Poisson transformation can be reached without
applying whole-line Poisson summation to the discontinuous hard cutoff.  This
file constructs a smooth plateau which is exactly one on `[x, N]` and is zero
outside `[x - 2, N + 2]`.  If `2 < x <= N`, multiplying it by the Mellin
weight `u ^ (-s)` gives a compactly supported smooth function, hence a
Schwartz function.  Mathlib's Poisson theorem then applies unconditionally.

The remaining AFE work is quantitative: estimate the two transition strips
and split the Fourier side into stationary and nonstationary modes.  No such
estimate is postulated here.
-/

noncomputable section

open Complex Filter Metric Set
open scoped FourierTransform SchwartzMap Topology

namespace HardyTheorem
namespace AFE

/-- A symmetric smooth bump centered at the midpoint of `x` and `N`.  Its
inner radius is `|N-x|/2+1` and its outer radius is `|N-x|/2+2`. -/
noncomputable def intervalPlateauBump (x N : ℝ) :
    ContDiffBump ((x + N) / 2) where
  rIn := |N - x| / 2 + 1
  rOut := |N - x| / 2 + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The plateau is identically one on the requested interval. -/
theorem intervalPlateauBump_eq_one {x N u : ℝ} (hxN : x ≤ N)
    (hu : u ∈ Icc x N) :
    intervalPlateauBump x N u = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [mem_closedBall, Real.dist_eq]
  change |u - (x + N) / 2| ≤ |N - x| / 2 + 1
  rw [abs_of_nonneg (sub_nonneg.mpr hxN), abs_le]
  constructor <;> linarith [hu.1, hu.2]

/-- The left transition strip has width at most two. -/
theorem intervalPlateauBump_eq_zero_of_le {x N u : ℝ} (hxN : x ≤ N)
    (hu : u ≤ x - 2) :
    intervalPlateauBump x N u = 0 := by
  apply ContDiffBump.zero_of_le_dist
  rw [Real.dist_eq]
  change |N - x| / 2 + 2 ≤ |u - (x + N) / 2|
  rw [abs_of_nonneg (sub_nonneg.mpr hxN), abs_of_nonpos]
  · linarith
  · linarith

/-- The right transition strip has width at most two. -/
theorem intervalPlateauBump_eq_zero_of_ge {x N u : ℝ} (hxN : x ≤ N)
    (hu : N + 2 ≤ u) :
    intervalPlateauBump x N u = 0 := by
  apply ContDiffBump.zero_of_le_dist
  rw [Real.dist_eq]
  change |N - x| / 2 + 2 ≤ |u - (x + N) / 2|
  rw [abs_of_nonneg (sub_nonneg.mpr hxN), abs_of_nonneg]
  · linarith
  · linarith

/-- The compactly supported Mellin weight used in the Poisson transformation.
`Real.log` is used in the definition so smoothness can be proved directly.
On the positive plateau this is exactly `(u : ℂ) ^ (-s)`. -/
noncomputable def weightedPoissonCutoff (s : ℂ) (x N : ℝ) (u : ℝ) : ℂ :=
  (intervalPlateauBump x N u : ℂ) *
    Complex.exp (-s * (Real.log u : ℂ))

theorem weightedPoissonCutoff_hasCompactSupport (s : ℂ) (x N : ℝ) :
    HasCompactSupport (weightedPoissonCutoff s x N) := by
  have hb : HasCompactSupport
      (fun u : ℝ => (intervalPlateauBump x N u : ℂ)) :=
    (intervalPlateauBump x N).hasCompactSupport.comp_left Complex.ofReal_zero
  exact hb.mul_right

/-- The only apparent singularity is at zero.  When `2 < x <= N`, the bump
vanishes on a neighborhood of zero, so the product is globally smooth. -/
theorem weightedPoissonCutoff_contDiff (s : ℂ) {x N : ℝ}
    (hx : 2 < x) (hxN : x ≤ N) :
    ContDiff ℝ (⊤ : ℕ∞) (weightedPoissonCutoff s x N) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u = 0
  · subst u
    apply (contDiffAt_const (x := (0 : ℝ)) (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < x - 2 by linarith)] with v hv
    simp [weightedPoissonCutoff,
      intervalPlateauBump_eq_zero_of_le hxN hv.le]
  · have hb : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun v : ℝ => (intervalPlateauBump x N v : ℂ)) u :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp u
        (intervalPlateauBump x N).contDiffAt
    have hlog : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : ℝ => (Real.log v : ℂ)) u :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp u
        (Real.contDiffAt_log.mpr hu)
    exact hb.mul ((contDiffAt_const.mul hlog).cexp)

/-- On the whole requested interval the smoothed summand is the original
Mellin summand. -/
theorem weightedPoissonCutoff_eq_cpow (s : ℂ) {x N u : ℝ}
    (hx : 0 < x) (hxN : x ≤ N) (hu : u ∈ Icc x N) :
    weightedPoissonCutoff s x N u = (u : ℂ) ^ (-s) := by
  have hu0 : 0 < u := hx.trans_le hu.1
  rw [weightedPoissonCutoff, intervalPlateauBump_eq_one hxN hu,
    ofReal_one, one_mul, Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hu0.ne')]
  rw [Complex.ofReal_log hu0.le]
  congr 1
  ring

/-- Whole-line Poisson summation for the smoothed Mellin cutoff.  This is an
actual theorem obtained from the Schwartz Poisson formula, not an analytic
interface or an axiom. -/
theorem weightedPoissonCutoff_tsum_eq_fourier_tsum (s : ℂ) {x N : ℝ}
    (hx : 2 < x) (hxN : x ≤ N) :
    (∑' n : ℤ, weightedPoissonCutoff s x N n) =
      ∑' n : ℤ, 𝓕 (weightedPoissonCutoff s x N) n := by
  let F : 𝓢(ℝ, ℂ) :=
    (weightedPoissonCutoff_hasCompactSupport s x N).toSchwartzMap
      (weightedPoissonCutoff_contDiff s hx hxN)
  have h := SchwartzMap.tsum_eq_tsum_fourier F 0
  simp_rw [SchwartzMap.fourier_coe] at h
  change (∑' n : ℤ, F n) = ∑' n : ℤ, 𝓕 (F : ℝ → ℂ) n
  simpa using h

end AFE
end HardyTheorem
