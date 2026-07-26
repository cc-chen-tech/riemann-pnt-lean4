import ZeroFreeRegion.VinogradovKorobov.ZetaGrowthToLogDerivative

open Complex

namespace ZeroFreeRegion.VinogradovKorobov

/-- The regularized logarithmic-derivative loss for a parameterized Jensen
configuration centered at `2 + I*t`. -/
noncomputable def parameterizedJensenEnvelope
    (d a b R M K rho : ℝ) : ℝ :=
  6 * max (K + Real.log 3) 1 / rho +
    ((Real.log M + Real.log 3) / Real.log (R / b)) / (a - d)

/-- Parameterized Jensen growth gives a regularized logarithmic-derivative
bound on the retained disk.  Unlike the fixed-disk wrapper, all radii may
depend on height in a later application. -/
theorem norm_regularized_logDeriv_riemannZeta_le_of_parameterized_jensen_growth
    {d a q b R t M K rho : ℝ}
    (hd : 0 ≤ d) (hda : d < a) (haq : a < q) (hqb : q < b)
    (hbR : b < R) (hheight : R < |t|) (hM : 1 ≤ M)
    (hrho : 0 < rho) (hgeom : d + rho ≤ 3 * a / 4)
    (houter : ∀ z : ℂ,
      z ∈ Metric.sphere ((2 : ℂ) + I * t) R → ‖riemannZeta z‖ ≤ M)
    (hinner : ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) q,
      Real.log ‖riemannZeta z‖ ≤ K) :
    ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) d,
      riemannZeta z ≠ 0 →
      ‖logDeriv riemannZeta z -
          ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
            (Metric.closedBall ((2 : ℂ) + I * t) b) u : ℂ) *
              (z - u)⁻¹‖ ≤
        parameterizedJensenEnvelope d a b R M K rho := by
  intro z hz hzeta
  have hbound :=
    ZeroFreeRegion.norm_regularized_logDeriv_riemannZeta_le_of_good_radius_and_jensen_three_quarters
      hd hda haq hqb hbR hheight hM hrho hgeom houter hinner z hz hzeta
  simpa [parameterizedJensenEnvelope] using hbound

/-- A parameterized regularized bound implies repulsion from a specified
same-height zero in the factorization disk. -/
theorem re_neg_deriv_div_riemannZeta_le_neg_inv_add_of_regularized_bound
    {b d E σ β t : ℝ}
    (hσ1 : 1 ≤ σ) (hβ1 : β < 1) (hbheight : b < |t|)
    (hs : ((σ : ℂ) + I * t) ∈
      Metric.closedBall ((2 : ℂ) + I * t) d)
    (hrho : ((β : ℂ) + I * t) ∈
      Metric.closedBall ((2 : ℂ) + I * t) b)
    (hzero : riemannZeta ((β : ℂ) + I * t) = 0)
    (hregular : ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) d,
      riemannZeta z ≠ 0 →
      ‖logDeriv riemannZeta z -
          ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
            (Metric.closedBall ((2 : ℂ) + I * t) b) u : ℂ) *
              (z - u)⁻¹‖ ≤ E) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re ≤
      -1 / (σ - β) + E := by
  let c : ℂ := (2 : ℂ) + I * t
  let s : ℂ := (σ : ℂ) + I * t
  let rho : ℂ := (β : ℂ) + I * t
  let S : ℂ := ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
    (Metric.closedBall c b) u : ℂ) * (s - u)⁻¹
  let Rpart : ℂ := logDeriv riemannZeta s - S
  have havoid : ∀ u : ℂ, u ∈ Metric.closedBall c b → u ≠ 1 := by
    intro u hu
    exact ZeroFreeRegion.closedBall_sigma_it_ne_one_of_height_add_le
      (z := u) (σ := 2) (t := t) (R := b) (H := |t| - b)
      (by simpa [c] using hu) (by linarith) (by linarith)
  have hs_ne : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [s, hσ1])
  have hRnorm : ‖Rpart‖ ≤ E := by
    simpa [Rpart, S, s, c] using hregular s (by simpa [s, c] using hs) hs_ne
  have hprincipal : 1 / (σ - β) ≤ S.re := by
    have hsub : 0 < s.re - rho.re := by simp [s, rho]; linarith
    have h := ZeroFreeRegion.one_div_le_re_finsum_riemannZeta_divisor_mul_inv
      havoid (by simp [s, hσ1]) (by simpa [rho, c] using hrho)
      (by simpa [rho] using hzero) (by simp [s, rho]) hsub
    simpa [S, s, rho, c] using h
  have hdecomp : logDeriv riemannZeta s = Rpart + S := by
    dsimp [Rpart]
    ring
  have hreal : (-logDeriv riemannZeta s).re + 1 / (σ - β) ≤ ‖Rpart‖ := by
    have hnegR : -Rpart.re ≤ ‖Rpart‖ :=
      (neg_le_abs Rpart.re).trans (Complex.abs_re_le_norm Rpart)
    rw [hdecomp]
    simp only [neg_re, add_re]
    linarith
  calc
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re
        = (-logDeriv riemannZeta s).re := by
          simp [s, ZeroFreeRegion.neg_logDeriv_riemannZeta_eq_neg_deriv_div]
    _ ≤ ‖Rpart‖ - 1 / (σ - β) := by linarith
    _ ≤ E - 1 / (σ - β) := sub_le_sub_right hRnorm _
    _ = -1 / (σ - β) + E := by ring

/-- A parameterized regularized bound controls the vertical term without a
zero-free-disk assumption. -/
theorem re_neg_deriv_div_riemannZeta_le_of_regularized_bound
    {b d E σ t : ℝ}
    (hσ1 : 1 ≤ σ) (hbheight : b < |t|)
    (hs : ((σ : ℂ) + I * t) ∈
      Metric.closedBall ((2 : ℂ) + I * t) d)
    (hregular : ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) d,
      riemannZeta z ≠ 0 →
      ‖logDeriv riemannZeta z -
          ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
            (Metric.closedBall ((2 : ℂ) + I * t) b) u : ℂ) *
              (z - u)⁻¹‖ ≤ E) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re ≤ E := by
  let c : ℂ := (2 : ℂ) + I * t
  let s : ℂ := (σ : ℂ) + I * t
  let S : ℂ := ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
    (Metric.closedBall c b) u : ℂ) * (s - u)⁻¹
  let Rpart : ℂ := logDeriv riemannZeta s - S
  have havoid : ∀ u : ℂ, u ∈ Metric.closedBall c b → u ≠ 1 := by
    intro u hu
    exact ZeroFreeRegion.closedBall_sigma_it_ne_one_of_height_add_le
      (z := u) (σ := 2) (t := t) (R := b) (H := |t| - b)
      (by simpa [c] using hu) (by linarith) (by linarith)
  have hs_ne : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [s, hσ1])
  have hRnorm : ‖Rpart‖ ≤ E := by
    simpa [Rpart, S, s, c] using hregular s (by simpa [s, c] using hs) hs_ne
  have hprincipal : 0 ≤ S.re := by
    simpa [S] using ZeroFreeRegion.re_finsum_riemannZeta_divisor_mul_inv_nonneg
      havoid (by simp [s, hσ1])
  have hdecomp : logDeriv riemannZeta s = Rpart + S := by
    dsimp [Rpart]
    ring
  have hreal : (-logDeriv riemannZeta s).re ≤ ‖Rpart‖ := by
    have hnegR : -Rpart.re ≤ ‖Rpart‖ :=
      (neg_le_abs Rpart.re).trans (Complex.abs_re_le_norm Rpart)
    rw [hdecomp]
    simp only [neg_re, add_re]
    linarith
  calc
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re
        = (-logDeriv riemannZeta s).re := by
          simp [s, ZeroFreeRegion.neg_logDeriv_riemannZeta_eq_neg_deriv_div]
    _ ≤ ‖Rpart‖ := hreal
    _ ≤ E := hRnorm

/-- Direct candidate-zero consequence of parameterized Jensen growth. -/
theorem re_neg_deriv_div_riemannZeta_le_neg_inv_add_of_parameterized_jensen_growth
    {d a q b R t M K rho σ β : ℝ}
    (hd : 0 ≤ d) (hda : d < a) (haq : a < q) (hqb : q < b)
    (hbR : b < R) (hheight : R < |t|) (hM : 1 ≤ M)
    (hrho : 0 < rho) (hgeom : d + rho ≤ 3 * a / 4)
    (hσ1 : 1 ≤ σ) (hβ1 : β < 1)
    (hs : ((σ : ℂ) + I * t) ∈
      Metric.closedBall ((2 : ℂ) + I * t) d)
    (hbeta : ((β : ℂ) + I * t) ∈
      Metric.closedBall ((2 : ℂ) + I * t) b)
    (hzero : riemannZeta ((β : ℂ) + I * t) = 0)
    (houter : ∀ z : ℂ,
      z ∈ Metric.sphere ((2 : ℂ) + I * t) R → ‖riemannZeta z‖ ≤ M)
    (hinner : ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) q,
      Real.log ‖riemannZeta z‖ ≤ K) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re ≤
      -1 / (σ - β) + parameterizedJensenEnvelope d a b R M K rho := by
  apply re_neg_deriv_div_riemannZeta_le_neg_inv_add_of_regularized_bound
    (b := b) (d := d)
    (E := parameterizedJensenEnvelope d a b R M K rho)
    (t := t) hσ1 hβ1 (hbR.trans hheight) hs hbeta hzero
  exact norm_regularized_logDeriv_riemannZeta_le_of_parameterized_jensen_growth
    hd hda haq hqb hbR hheight hM hrho hgeom houter hinner

/-- Direct vertical-term consequence of parameterized Jensen growth. -/
theorem re_neg_deriv_div_riemannZeta_le_of_parameterized_jensen_growth
    {d a q b R t M K rho σ : ℝ}
    (hd : 0 ≤ d) (hda : d < a) (haq : a < q) (hqb : q < b)
    (hbR : b < R) (hheight : R < |t|) (hM : 1 ≤ M)
    (hrho : 0 < rho) (hgeom : d + rho ≤ 3 * a / 4)
    (hσ1 : 1 ≤ σ)
    (hs : ((σ : ℂ) + I * t) ∈
      Metric.closedBall ((2 : ℂ) + I * t) d)
    (houter : ∀ z : ℂ,
      z ∈ Metric.sphere ((2 : ℂ) + I * t) R → ‖riemannZeta z‖ ≤ M)
    (hinner : ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) q,
      Real.log ‖riemannZeta z‖ ≤ K) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re ≤
      parameterizedJensenEnvelope d a b R M K rho := by
  apply re_neg_deriv_div_riemannZeta_le_of_regularized_bound
    (b := b) (d := d)
    (E := parameterizedJensenEnvelope d a b R M K rho)
    (t := t) hσ1 (hbR.trans hheight) hs
  exact norm_regularized_logDeriv_riemannZeta_le_of_parameterized_jensen_growth
    hd hda haq hqb hbR hheight hM hrho hgeom houter hinner

end ZeroFreeRegion.VinogradovKorobov
