import PrimeNumberTheorem.CarlsonPoleFreeMollifiedError

/-!
# Polynomial growth preparation for the pole-free Carlson error

The first step is a uniform bound on the compact low-height part of the
strip.  The complementary high-height estimate will use the unconditional
polynomial zeta bound.
-/

open Complex Set

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The pole-free two-scale mollified error is uniformly bounded on the
compact rectangle `1/2 ≤ Re(s) ≤ 4`, `|Im(s)| ≤ 1`. -/
theorem exists_norm_poleFreeTwoScaleMollifiedZetaError_le_on_compact_strip
    (Y0 Y1 : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {x t : ℝ},
      x ∈ Icc (1 / 2 : ℝ) 4 → t ∈ Icc (-1 : ℝ) 1 →
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
          ((x : ℂ) + I * (t : ℂ))‖ ≤ M := by
  let K : Set (ℝ × ℝ) :=
    Icc (1 / 2 : ℝ) 4 ×ˢ Icc (-1 : ℝ) 1
  let point : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + I * (p.2 : ℂ)
  let f : ℝ × ℝ → ℂ := fun p =>
    poleFreeTwoScaleMollifiedZetaError Y0 Y1 (point p)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hf : ContinuousOn f K := by
    intro p hp
    have hpoint : ContinuousAt point p := by
      dsimp [point]
      fun_prop
    have hre : 0 < (point p).re := by
      dsimp [point]
      simp only [ofReal_re, mul_re, I_re, ofReal_im, I_im,
        zero_mul, one_mul, sub_self, add_zero]
      linarith [hp.1.1]
    have hanalytic :
        AnalyticAt ℂ (poleFreeTwoScaleMollifiedZetaError Y0 Y1) (point p) :=
      analyticOnNhd_poleFreeTwoScaleMollifiedZetaError_re_gt
        (theta := 0) le_rfl Y0 Y1 (point p) hre
    exact (hanalytic.continuousAt.comp hpoint).continuousWithinAt
  rcases hK.exists_bound_of_continuousOn hf with ⟨M, hM⟩
  refine ⟨max 0 M, le_max_left 0 M, ?_⟩
  intro x t hx ht
  have hp : (x, t) ∈ K := ⟨hx, ht⟩
  have hbound : ‖f (x, t)‖ ≤ M := hM (x, t) hp
  have hbound' :
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
          ((x : ℂ) + I * (t : ℂ))‖ ≤ M := by
    simpa [f, point] using hbound
  exact hbound'.trans (le_max_right 0 M)

end CarlsonZeroDensity
end PrimeNumberTheorem
