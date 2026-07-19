import ZeroFreeRegion.VinogradovKorobov.ZeroFreeClosure

open Complex

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (c t : ℝ) : ℝ := vinogradovKorobovWidth c t

example :
    ZeroFreeRegion.vinogradov_korobov_zero_free_region ↔
      ∃ c > 0, ∀ s : ℂ, |s.im| ≥ 3 →
        s.re ≥ 1 - vinogradovKorobovWidth c |s.im| →
        riemannZeta s ≠ 0 :=
  vinogradov_korobov_zero_free_region_iff_width

example
    {T0 : ℝ} {width σOf realBound twoBound : ℝ → ℝ}
    {zeroBound : ℝ → ℝ → ℝ}
    (hσ_gt : ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t)
    (hσ_le : ∀ t : ℝ, T0 ≤ |t| → σOf t ≤ 2)
    (hσ_sub_pos : ∀ β t : ℝ, T0 ≤ |t| → β < 1 →
      β ≥ 1 - width |t| → 0 < σOf t - β)
    (hreal : ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
      (-deriv riemannZeta (σOf t : ℂ) /
        riemannZeta (σOf t : ℂ)).re ≤ realBound t)
    (hzero : ∀ β t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
      β < 1 → β ≥ 1 - width |t| → 0 < σOf t - β →
      riemannZeta ((β : ℂ) + I * t) = 0 →
      (-deriv riemannZeta ((σOf t : ℂ) + I * t) /
        riemannZeta ((σOf t : ℂ) + I * t)).re ≤ zeroBound β t)
    (htwo : ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
      (-deriv riemannZeta ((σOf t : ℂ) + 2 * I * t) /
        riemannZeta ((σOf t : ℂ) + 2 * I * t)).re ≤ twoBound t)
    (hmargin : ∀ β t : ℝ, T0 ≤ |t| → β < 1 →
      β ≥ 1 - width |t| →
      3 * realBound t + 4 * zeroBound β t + twoBound t < 0) :
    ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - width |s.im| → riemannZeta s ≠ 0 :=
  three_four_one_zero_free_high_height_of_width
    hσ_gt hσ_le hσ_sub_pos hreal hzero htwo hmargin

end ZeroFreeRegion.VinogradovKorobov
