import ZeroFreeRegion

open Complex

namespace ZeroFreeRegion.VinogradovKorobov

/-- The width appearing in the Vinogradov--Korobov zero-free region. -/
noncomputable def vinogradovKorobovWidth (c t : ℝ) : ℝ :=
  c / (Real.log t) ^ (2 / 3 : ℝ) *
    (Real.log (Real.log t)) ^ (-1 / 3 : ℝ)

/-- The repository's VK target restated using the named width function. -/
theorem vinogradov_korobov_zero_free_region_iff_width :
    ZeroFreeRegion.vinogradov_korobov_zero_free_region ↔
      ∃ c > 0, ∀ s : ℂ, |s.im| ≥ 3 →
        s.re ≥ 1 - vinogradovKorobovWidth c |s.im| →
        riemannZeta s ≠ 0 := by
  rfl

/-- Width-agnostic 3-4-1 closure at high height.  All analytic content is
isolated in upper bounds for the logarithmic derivative at the real point,
the candidate-zero height, and twice that height. -/
theorem three_four_one_zero_free_high_height_of_width
    {T0 : ℝ} {width σOf realBound twoBound : ℝ → ℝ}
    {zeroBound : ℝ → ℝ → ℝ}
    (hσ_gt : ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t)
    (hσ_le : ∀ t : ℝ, T0 ≤ |t| → σOf t ≤ 2)
    (hσ_sub_pos : ∀ β t : ℝ, T0 ≤ |t| → β < 1 →
      β ≥ 1 - width |t| → 0 < σOf t - β)
    (hreal :
      ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta (σOf t : ℂ) /
          riemannZeta (σOf t : ℂ)).re ≤ realBound t)
    (hzero :
      ∀ β t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 → β < 1 →
        β ≥ 1 - width |t| → 0 < σOf t - β →
        riemannZeta ((β : ℂ) + I * t) = 0 →
        (-deriv riemannZeta ((σOf t : ℂ) + I * t) /
          riemannZeta ((σOf t : ℂ) + I * t)).re ≤ zeroBound β t)
    (htwo :
      ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta ((σOf t : ℂ) + 2 * I * t) /
          riemannZeta ((σOf t : ℂ) + 2 * I * t)).re ≤ twoBound t)
    (hmargin :
      ∀ β t : ℝ, T0 ≤ |t| → β < 1 → β ≥ 1 - width |t| →
        3 * realBound t + 4 * zeroBound β t + twoBound t < 0) :
    ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - width |s.im| → riemannZeta s ≠ 0 := by
  intro s hsheight hsre hs_zero
  have hs_lt_one : s.re < 1 := by
    by_contra hs_not_lt
    exact (riemannZeta_ne_zero_of_one_le_re
      (le_of_not_gt hs_not_lt)) hs_zero
  have hσ_gt' : 1 < σOf s.im := hσ_gt s.im hsheight
  have hσ_le' : σOf s.im ≤ 2 := hσ_le s.im hsheight
  have hσ_sub' : 0 < σOf s.im - s.re :=
    hσ_sub_pos s.re s.im hsheight hs_lt_one hsre
  have hs_zero_re_im :
      riemannZeta ((s.re : ℂ) + I * s.im) = 0 := by
    simpa [ZeroFreeRegion.re_im_decomp s] using hs_zero
  have hnonneg := ZeroFreeRegion.log_deriv_zeta_nonneg_combination
    (σOf s.im) hσ_gt' s.im
  have hreal' := hreal s.im hsheight hσ_gt' hσ_le'
  have hzero' := hzero s.re s.im hsheight hσ_gt' hσ_le'
    hs_lt_one hsre hσ_sub' hs_zero_re_im
  have htwo' := htwo s.im hsheight hσ_gt' hσ_le'
  have hupper :
      3 * (-deriv riemannZeta (σOf s.im : ℂ) /
            riemannZeta (σOf s.im : ℂ)).re
        + 4 * (-deriv riemannZeta ((σOf s.im : ℂ) + I * s.im) /
            riemannZeta ((σOf s.im : ℂ) + I * s.im)).re
        + (-deriv riemannZeta ((σOf s.im : ℂ) + 2 * I * s.im) /
            riemannZeta ((σOf s.im : ℂ) + 2 * I * s.im)).re
        ≤ 3 * realBound s.im + 4 * zeroBound s.re s.im +
          twoBound s.im := by
    nlinarith
  have hneg := hmargin s.re s.im hsheight hs_lt_one hsre
  linarith

/-- Conditional VK closure at its native cutoff.  Once the three displayed
logarithmic-derivative estimates and their numerical margin are supplied on
the VK width, the target proposition follows without any further zeta
argument. -/
theorem vinogradov_korobov_zero_free_region_of_log_deriv_bounds_at_three
    {c : ℝ} {σOf realBound twoBound : ℝ → ℝ}
    {zeroBound : ℝ → ℝ → ℝ} (hc : 0 < c)
    (hσ_gt : ∀ t : ℝ, 3 ≤ |t| → 1 < σOf t)
    (hσ_le : ∀ t : ℝ, 3 ≤ |t| → σOf t ≤ 2)
    (hσ_sub_pos : ∀ β t : ℝ, 3 ≤ |t| → β < 1 →
      β ≥ 1 - vinogradovKorobovWidth c |t| → 0 < σOf t - β)
    (hreal :
      ∀ t : ℝ, 3 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta (σOf t : ℂ) /
          riemannZeta (σOf t : ℂ)).re ≤ realBound t)
    (hzero :
      ∀ β t : ℝ, 3 ≤ |t| → 1 < σOf t → σOf t ≤ 2 → β < 1 →
        β ≥ 1 - vinogradovKorobovWidth c |t| → 0 < σOf t - β →
        riemannZeta ((β : ℂ) + I * t) = 0 →
        (-deriv riemannZeta ((σOf t : ℂ) + I * t) /
          riemannZeta ((σOf t : ℂ) + I * t)).re ≤ zeroBound β t)
    (htwo :
      ∀ t : ℝ, 3 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta ((σOf t : ℂ) + 2 * I * t) /
          riemannZeta ((σOf t : ℂ) + 2 * I * t)).re ≤ twoBound t)
    (hmargin :
      ∀ β t : ℝ, 3 ≤ |t| → β < 1 →
        β ≥ 1 - vinogradovKorobovWidth c |t| →
        3 * realBound t + 4 * zeroBound β t + twoBound t < 0) :
    ZeroFreeRegion.vinogradov_korobov_zero_free_region := by
  rw [vinogradov_korobov_zero_free_region_iff_width]
  exact ⟨c, hc,
    three_four_one_zero_free_high_height_of_width
      hσ_gt hσ_le hσ_sub_pos hreal hzero htwo hmargin⟩

end ZeroFreeRegion.VinogradovKorobov
