import PrimeNumberTheorem.CarlsonPoleFreeMollifiedError
import PrimeNumberTheorem.CarlsonGaussianHilbertMemLp
import ZeroFreeRegion.PhragmenLindelofZeta

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

/-- On the full strip `1/2 ≤ Re(s) ≤ 4`, the square norm of the pole-free
two-scale error has a uniform degree-ten polynomial bound in the height.

The degree comes from the unconditional degree-four zeta bound, one factor
of `s - 1`, and then squaring.  The compact low-height part is supplied by
`exists_norm_poleFreeTwoScaleMollifiedZetaError_le_on_compact_strip`. -/
theorem
    exists_norm_sq_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_half_four
    {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℂ},
      s.re ∈ Icc (1 / 2 : ℝ) 4 →
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 s‖ ^ 2 ≤
        C * (|s.im| + 3) ^ 10 := by
  rcases exists_norm_poleFreeTwoScaleMollifiedZetaError_le_on_compact_strip
      Y0 Y1 with ⟨M, hM, hcompact⟩
  rcases ZeroFreeRegion.exists_norm_riemannZeta_le_polynomial_on_zero_four with
    ⟨Czeta, hCzeta, hzeta⟩
  let B : ℝ := Czeta * (Y1 : ℝ) + 1
  let C : ℝ := M ^ 2 + B ^ 2
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro s hsre
  let A : ℝ := |s.im| + 3
  have hA : 1 ≤ A := by
    dsimp [A]
    linarith [abs_nonneg s.im]
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hA5 : A ≤ A ^ 5 := by
    simpa using pow_le_pow_right₀ hA (by norm_num : (1 : ℕ) ≤ 5)
  have hA10 : 1 ≤ A ^ 10 := one_le_pow₀ hA
  by_cases him : |s.im| ≤ 1
  · have himIcc : s.im ∈ Icc (-1 : ℝ) 1 := abs_le.mp him
    have hsmall := hcompact hsre himIcc
    have hsrepr : ((s.re : ℂ) + I * (s.im : ℂ)) = s := by
      apply Complex.ext <;> simp
    rw [hsrepr] at hsmall
    have hsq :
        ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 s‖ ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hsmall 2
    calc
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 s‖ ^ 2
          ≤ M ^ 2 := hsq
      _ ≤ C := by
        dsimp [C]
        nlinarith [sq_nonneg B]
      _ ≤ C * A ^ 10 := le_mul_of_one_le_right hC hA10
      _ = C * (|s.im| + 3) ^ 10 := by rfl
  · have hheight : 1 ≤ |s.im| := le_of_lt (lt_of_not_ge him)
    have hs0 : s ≠ 0 := by
      intro hs
      subst s
      norm_num at hheight
    have hs1 : s ≠ 1 := by
      intro hs
      subst s
      norm_num at hheight
    have hsubRe : |s.re - 1| ≤ 3 := by
      rw [abs_le]
      constructor <;> linarith [hsre.1, hsre.2]
    have hsub : ‖s - 1‖ ≤ A := by
      calc
        ‖s - 1‖ ≤ |(s - 1).re| + |(s - 1).im| :=
          Complex.norm_le_abs_re_add_abs_im (s - 1)
        _ = |s.re - 1| + |s.im| := by simp
        _ ≤ 3 + |s.im| := add_le_add hsubRe le_rfl
        _ = A := by dsimp [A]; ring
    have hzetaBound : ‖riemannZeta s‖ ≤ Czeta * A ^ 4 := by
      simpa [A] using hzeta s ⟨by linarith [hsre.1], hsre.2⟩ hheight
    have hq :
        ‖ZeroFreeRegion.riemannZetaPoleUnitAtOne s‖ ≤ Czeta * A ^ 5 := by
      rw [ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
        hs0 hs1, norm_mul]
      calc
        ‖s - 1‖ * ‖riemannZeta s‖ ≤ A * (Czeta * A ^ 4) :=
          mul_le_mul hsub hzetaBound (norm_nonneg _) hA0
        _ = Czeta * A ^ 5 := by ring
    have hmollifier :
        ‖HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s‖ ≤ (Y1 : ℝ) :=
      HardyTheorem.norm_twoScaleSelbergMollifier_le_natCast
        hY0 hY01 (by linarith [hsre.1])
    have hproduct :
        ‖ZeroFreeRegion.riemannZetaPoleUnitAtOne s *
            HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s‖ ≤
          (Czeta * A ^ 5) * (Y1 : ℝ) := by
      rw [norm_mul]
      exact mul_le_mul hq hmollifier (norm_nonneg _) (by positivity)
    have hnumerator :
        ‖ZeroFreeRegion.riemannZetaPoleUnitAtOne s *
              HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s - (s - 1)‖ ≤
          B * A ^ 5 := by
      calc
        ‖ZeroFreeRegion.riemannZetaPoleUnitAtOne s *
              HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s - (s - 1)‖
            ≤ ‖ZeroFreeRegion.riemannZetaPoleUnitAtOne s *
                HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s‖ + ‖s - 1‖ :=
              norm_sub_le _ _
        _ ≤ (Czeta * A ^ 5) * (Y1 : ℝ) + A :=
              add_le_add hproduct hsub
        _ ≤ (Czeta * A ^ 5) * (Y1 : ℝ) + A ^ 5 :=
              add_le_add le_rfl hA5
        _ = B * A ^ 5 := by dsimp [B]; ring
    have hdenominator : 1 ≤ ‖s + 1‖ := by
      calc
        1 ≤ |s.im| := hheight
        _ = |(s + 1).im| := by simp
        _ ≤ ‖s + 1‖ := Complex.abs_im_le_norm (s + 1)
    have hlarge :
        ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 s‖ ≤ B * A ^ 5 := by
      rw [poleFreeTwoScaleMollifiedZetaError, norm_div]
      exact (div_le_self (norm_nonneg _) hdenominator).trans hnumerator
    have hsq :
        ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 s‖ ^ 2 ≤
          B ^ 2 * A ^ 10 := by
      calc
        ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 s‖ ^ 2
            ≤ (B * A ^ 5) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hlarge 2
        _ = B ^ 2 * A ^ 10 := by ring
    calc
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 s‖ ^ 2
          ≤ B ^ 2 * A ^ 10 := hsq
      _ ≤ C * A ^ 10 := by
        gcongr
        dsimp [C]
        nlinarith [sq_nonneg M]
      _ = C * (|s.im| + 3) ^ 10 := by rfl

/-- For every complex strip parameter with `1/2 ≤ Re(z) ≤ 4`, the concrete
pole-free Carlson Gaussian section belongs to `L²(ℝ)`. -/
theorem memLp_carlsonGaussian_poleFreeTwoScaleMollifiedZetaError_on_half_four
    {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hzre : z.re ∈ Icc (1 / 2 : ℝ) 4) :
    MeasureTheory.MemLp
      (carlsonGaussianHilbertSection Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z) 2
      MeasureTheory.volume := by
  rcases
      exists_norm_sq_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_half_four
        hY0 hY01 with ⟨C, hC, hgrowth⟩
  have hcont : Continuous fun t : ℝ =>
      poleFreeTwoScaleMollifiedZetaError Y0 Y1 (z + I * (t : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro t
    let point : ℝ → ℂ := fun u => z + I * (u : ℂ)
    have hpoint : ContinuousAt point t := by
      dsimp [point]
      fun_prop
    have hre : 0 < (point t).re := by
      dsimp [point]
      simp only [mul_re, I_re, ofReal_re, I_im, ofReal_im,
        zero_mul, one_mul, sub_self, add_zero]
      linarith [hzre.1]
    have hanalytic :
        AnalyticAt ℂ (poleFreeTwoScaleMollifiedZetaError Y0 Y1) (point t) :=
      analyticOnNhd_poleFreeTwoScaleMollifiedZetaError_re_gt
        (theta := 0) le_rfl Y0 Y1 (point t) hre
    simpa [point, Function.comp_def] using hanalytic.continuousAt.comp hpoint
  let D : ℝ := |w| + 3
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [abs_nonneg w]
  have hbound : ∀ t : ℝ,
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
          (z + I * (t : ℂ))‖ ^ 2 ≤
        (C * D ^ 10) * (1 + |z.im + t - w|) ^ 10 := by
    intro t
    let u : ℝ := z.im + t - w
    have habs : |z.im + t| ≤ |u| + |w| := by
      calc
        |z.im + t| = |u + w| := by
          congr 1
          dsimp [u]
          ring
        _ ≤ |u| + |w| := abs_add_le _ _
    have hlinear : |z.im + t| + 3 ≤ D * (1 + |u|) := by
      have huD : |u| ≤ D * |u| :=
        le_mul_of_one_le_left (abs_nonneg u) hD
      dsimp [D]
      nlinarith
    have hpow :
        (|z.im + t| + 3) ^ 10 ≤ (D * (1 + |u|)) ^ 10 :=
      pow_le_pow_left₀ (by positivity) hlinear 10
    have hraw := hgrowth (s := z + I * (t : ℂ)) (by simpa using hzre)
    calc
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
          (z + I * (t : ℂ))‖ ^ 2
          ≤ C * (|z.im + t| + 3) ^ 10 := by simpa using hraw
      _ ≤ C * (D * (1 + |u|)) ^ 10 :=
        mul_le_mul_of_nonneg_left hpow hC
      _ = (C * D ^ 10) * (1 + |z.im + t - w|) ^ 10 := by
        dsimp [u]
        ring
  exact
    memLp_carlsonGaussianHilbertSection_of_complex_polynomial_sq_bound
      hDelta 10 (poleFreeTwoScaleMollifiedZetaError Y0 Y1) hcont hbound

end CarlsonZeroDensity
end PrimeNumberTheorem
