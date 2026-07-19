import ZeroFreeRegion

open Complex

namespace ZeroFreeRegion.VinogradovKorobov

/-- The standard Vinogradov--Korobov logarithmic scale. -/
noncomputable def vinogradovKorobovScale (t : ℝ) : ℝ :=
  (Real.log t) ^ (2 / 3 : ℝ) *
    (Real.log (Real.log t)) ^ (1 / 3 : ℝ)

/-- The standard horizontal radius used to convert Richert growth into the
Vinogradov--Korobov logarithmic-derivative scale. -/
noncomputable def vinogradovKorobovEta (t : ℝ) : ℝ :=
  (Real.log (Real.log t) / Real.log t) ^ (2 / 3 : ℝ)

/-- The width appearing in the Vinogradov--Korobov zero-free region. -/
noncomputable def vinogradovKorobovWidth (c t : ℝ) : ℝ :=
  c / (Real.log t) ^ (2 / 3 : ℝ) *
    (Real.log (Real.log t)) ^ (-1 / 3 : ℝ)

theorem vinogradovKorobovScale_pos {t : ℝ} (ht : 3 ≤ t) :
    0 < vinogradovKorobovScale t := by
  have hlogpos : 0 < Real.log t :=
    Real.log_pos (by linarith)
  have hloglogpos : 0 < Real.log (Real.log t) := by
    have hlogone : 1 < Real.log t := by
      have ht0 : 0 ≤ t := by linarith
      simpa [abs_of_nonneg ht0] using
        (ZeroFreeRegion.log_abs_gt_one_of_three_le
          (ht.trans (le_abs_self t)))
    exact Real.log_pos hlogone
  unfold vinogradovKorobovScale
  positivity

theorem vinogradovKorobovEta_pos {t : ℝ} (ht : 3 ≤ t) :
    0 < vinogradovKorobovEta t := by
  have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hloglogpos : 0 < Real.log (Real.log t) := by
    have ht0 : 0 ≤ t := by linarith
    have hlogone : 1 < Real.log t := by
      simpa [abs_of_nonneg ht0] using
        (ZeroFreeRegion.log_abs_gt_one_of_three_le
          (ht.trans (le_abs_self t)))
    exact Real.log_pos hlogone
  unfold vinogradovKorobovEta
  positivity

/-- The parameter identity behind the VK exponent: a logarithmic-growth loss
`log log t`, divided by the Richert radius `eta(t)`, is exactly `S(t)`. -/
theorem log_log_div_vinogradovKorobovEta_eq_scale
    {t : ℝ} (ht : 3 ≤ t) :
    Real.log (Real.log t) / vinogradovKorobovEta t =
      vinogradovKorobovScale t := by
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hLL : 0 < Real.log (Real.log t) := by
    have ht0 : 0 ≤ t := by linarith
    have hLone : 1 < Real.log t := by
      simpa [abs_of_nonneg ht0] using
        (ZeroFreeRegion.log_abs_gt_one_of_three_le
          (ht.trans (le_abs_self t)))
    exact Real.log_pos hLone
  have hsub := Real.rpow_sub hLL (1 : ℝ) (2 / 3 : ℝ)
  have hquot : Real.log (Real.log t) /
      (Real.log (Real.log t)) ^ (2 / 3 : ℝ) =
        (Real.log (Real.log t)) ^ (1 / 3 : ℝ) := by
    calc
      Real.log (Real.log t) /
          (Real.log (Real.log t)) ^ (2 / 3 : ℝ) =
          (Real.log (Real.log t)) ^ (1 : ℝ) /
            (Real.log (Real.log t)) ^ (2 / 3 : ℝ) := by
              rw [Real.rpow_one]
      _ = (Real.log (Real.log t)) ^ ((1 : ℝ) - 2 / 3) := hsub.symm
      _ = (Real.log (Real.log t)) ^ (1 / 3 : ℝ) := by norm_num
  unfold vinogradovKorobovEta vinogradovKorobovScale
  rw [Real.div_rpow hLL.le hL.le]
  have hLp : (Real.log t) ^ (2 / 3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hL _)
  have hLLp : (Real.log (Real.log t)) ^ (2 / 3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hLL _)
  calc
    Real.log (Real.log t) /
        ((Real.log (Real.log t)) ^ (2 / 3 : ℝ) /
          (Real.log t) ^ (2 / 3 : ℝ)) =
        (Real.log t) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log t) /
            (Real.log (Real.log t)) ^ (2 / 3 : ℝ)) := by
              field_simp [hLp, hLLp]
    _ = (Real.log t) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log t)) ^ (1 / 3 : ℝ) := by rw [hquot]

/-- On its native range, the repository width is exactly `c / S(t)`. -/
theorem vinogradovKorobovWidth_eq_div_scale
    {c t : ℝ} (ht : 3 ≤ t) :
    vinogradovKorobovWidth c t = c / vinogradovKorobovScale t := by
  have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hloglogpos : 0 < Real.log (Real.log t) := by
    have hlogone : 1 < Real.log t := by
      have ht0 : 0 ≤ t := by linarith
      simpa [abs_of_nonneg ht0] using
        (ZeroFreeRegion.log_abs_gt_one_of_three_le
          (ht.trans (le_abs_self t)))
    exact Real.log_pos hlogone
  have hneg : (-1 / 3 : ℝ) = -(1 / 3 : ℝ) := by ring
  unfold vinogradovKorobovWidth vinogradovKorobovScale
  rw [hneg, Real.rpow_neg hloglogpos.le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hlogpos (2 / 3 : ℝ)),
    ne_of_gt (Real.rpow_pos_of_pos hloglogpos (1 / 3 : ℝ))]

theorem vinogradovKorobovScale_mono
    {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    vinogradovKorobovScale x ≤ vinogradovKorobovScale y := by
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogxy : Real.log x ≤ Real.log y :=
    Real.log_le_log (by linarith) hxy
  have hloglogxpos : 0 < Real.log (Real.log x) := by
    have hlogxone : 1 < Real.log x := by
      have hx0 : 0 ≤ x := by linarith
      simpa [abs_of_nonneg hx0] using
        (ZeroFreeRegion.log_abs_gt_one_of_three_le
          (hx.trans (le_abs_self x)))
    exact Real.log_pos hlogxone
  have hloglogxy : Real.log (Real.log x) ≤ Real.log (Real.log y) :=
    Real.log_le_log hlogxpos hlogxy
  have hfirst : (Real.log x) ^ (2 / 3 : ℝ) ≤
      (Real.log y) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hlogxpos.le hlogxy (by norm_num)
  have hsecond : (Real.log (Real.log x)) ^ (1 / 3 : ℝ) ≤
      (Real.log (Real.log y)) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow hloglogxpos.le hloglogxy (by norm_num)
  unfold vinogradovKorobovScale
  exact mul_le_mul hfirst hsecond
    (Real.rpow_nonneg hloglogxpos.le _)
    (Real.rpow_nonneg (hlogxpos.le.trans hlogxy) _)

/-- The repository's VK target restated using the named width function. -/
theorem vinogradov_korobov_zero_free_region_iff_width :
    ZeroFreeRegion.vinogradov_korobov_zero_free_region ↔
      ∃ c > 0, ∀ s : ℂ, |s.im| ≥ 3 →
        s.re ≥ 1 - vinogradovKorobovWidth c |s.im| →
        riemannZeta s ≠ 0 := by
  rfl

/-- For nonnegative width constant, the VK width is largest at the native
cutoff among all heights at least three. -/
theorem vinogradovKorobovWidth_le_at_three
    {c x : ℝ} (hc : 0 ≤ c) (hx : 3 ≤ x) :
    vinogradovKorobovWidth c x ≤ vinogradovKorobovWidth c 3 := by
  have hlog3pos : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlogxpos : 0 < Real.log x :=
    hlog3pos.trans_le (Real.log_le_log (by norm_num) hx)
  have hlog : Real.log (3 : ℝ) ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  have hden : (Real.log (3 : ℝ)) ^ (2 / 3 : ℝ) ≤
      (Real.log x) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hlog3pos.le hlog (by norm_num)
  have hden3pos : 0 < (Real.log (3 : ℝ)) ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos hlog3pos _
  have hdiv : c / (Real.log x) ^ (2 / 3 : ℝ) ≤
      c / (Real.log (3 : ℝ)) ^ (2 / 3 : ℝ) :=
    div_le_div_of_nonneg_left hc hden3pos hden
  have hloglog3pos : 0 < Real.log (Real.log (3 : ℝ)) := by
    have hlog3one : 1 < Real.log (3 : ℝ) := by
      simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 3)] using
        ZeroFreeRegion.log_abs_gt_one_of_three_le
          (show (3 : ℝ) ≤ |(3 : ℝ)| by norm_num)
    exact Real.log_pos hlog3one
  have hloglog : Real.log (Real.log (3 : ℝ)) ≤
      Real.log (Real.log x) :=
    Real.log_le_log hlog3pos hlog
  have hfactor :
      (Real.log (Real.log x)) ^ (-1 / 3 : ℝ) ≤
        (Real.log (Real.log (3 : ℝ))) ^ (-1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hloglog3pos hloglog (by norm_num)
  unfold vinogradovKorobovWidth
  exact mul_le_mul hdiv hfactor
    (Real.rpow_nonneg (hloglog3pos.le.trans hloglog) _)
    (div_nonneg hc hden3pos.le)

/-- Patch a sufficiently-high VK strip with the already verified compact
zero-free strip.  This reduces the analytic task to proving VK estimates
above any convenient cutoff `T0 ≥ 3`. -/
theorem compact_patch_vinogradov_korobov_zero_free_region
    (T0 : ℝ) (hT0 : 3 ≤ T0)
    (hhigh : ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - vinogradovKorobovWidth c |s.im| →
      riemannZeta s ≠ 0) :
    ZeroFreeRegion.vinogradov_korobov_zero_free_region := by
  rcases hhigh with ⟨chigh, hchigh, hregion⟩
  rcases ZeroFreeRegion.classical_zero_free_region_compact T0
      ((by norm_num : (2 : ℝ) ≤ 3).trans hT0) with
    ⟨d, hd, hcompact⟩
  let K : ℝ := vinogradovKorobovWidth 1 3
  have hK : 0 < K := by
    dsimp only [K, vinogradovKorobovWidth]
    have hlog3pos : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    have hloglog3pos : 0 < Real.log (Real.log (3 : ℝ)) := by
      have hlog3one : 1 < Real.log (3 : ℝ) := by
        simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 3)] using
          ZeroFreeRegion.log_abs_gt_one_of_three_le
            (show (3 : ℝ) ≤ |(3 : ℝ)| by norm_num)
      exact Real.log_pos hlog3one
    positivity
  let c := min chigh (d / K)
  have hc : 0 < c := lt_min hchigh (div_pos hd hK)
  rw [vinogradov_korobov_zero_free_region_iff_width]
  refine ⟨c, hc, ?_⟩
  intro s hs3 hsre
  by_cases hsT : T0 ≤ |s.im|
  · refine hregion s hsT ?_
    have hc_le : c ≤ chigh := min_le_left _ _
    have hwidth := ZeroFreeRegion.vinogradov_korobov_width_mono_const
      hc_le (hT0.trans hsT)
    have hwidth' : vinogradovKorobovWidth c |s.im| ≤
        vinogradovKorobovWidth chigh |s.im| := by
      simpa only [vinogradovKorobovWidth] using hwidth
    linarith
  · refine hcompact s (le_of_lt (lt_of_not_ge hsT)) ?_
    have hwidth3 : vinogradovKorobovWidth c |s.im| ≤
        vinogradovKorobovWidth c 3 :=
      vinogradovKorobovWidth_le_at_three hc.le hs3
    have hcK : c * K ≤ d := by
      have hc_div : c ≤ d / K := min_le_right _ _
      exact (le_div_iff₀ hK).mp hc_div
    have hwidth_eq : vinogradovKorobovWidth c 3 = c * K := by
      dsimp only [K, vinogradovKorobovWidth]
      ring
    rw [hwidth_eq] at hwidth3
    linarith

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
