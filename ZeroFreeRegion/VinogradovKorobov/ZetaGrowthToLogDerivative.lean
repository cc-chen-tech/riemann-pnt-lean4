import ZeroFreeRegion.PhragmenLindelofZeta

open Complex

namespace ZeroFreeRegion.VinogradovKorobov

/-- The deterministic regular-part loss produced by the fixed Jensen disks.

The inner disk has radius `8/5`, the factorization disk radius `17/10`, and
the outer Jensen circle radius `7/4`.  These are the same disks used by the
verified classical zero-free-region argument. -/
noncomputable def fixedJensenRegularizedEnvelope (M K : ℝ) : ℝ :=
  6 * max (K + Real.log 3) 1 / (1 / 16 : ℝ) +
    ((Real.log M + Real.log 3) /
        Real.log ((7 / 4 : ℝ) / (17 / 10 : ℝ))) /
      ((3 / 2 : ℝ) - 1)

/-- The fixed Jensen envelope when the norm bound is `exp K`. -/
noncomputable def fixedJensenLogEnvelope (K : ℝ) : ℝ :=
  6 * max (K + Real.log 3) 1 / (1 / 16 : ℝ) +
    ((K + Real.log 3) /
        Real.log ((7 / 4 : ℝ) / (17 / 10 : ℝ))) /
      ((3 / 2 : ℝ) - 1)

theorem fixedJensenRegularizedEnvelope_exp (K : ℝ) :
    fixedJensenRegularizedEnvelope (Real.exp K) K =
      fixedJensenLogEnvelope K := by
  simp [fixedJensenRegularizedEnvelope, fixedJensenLogEnvelope]

/-- An absolute constant dominating the fixed Jensen loss linearly in the
input logarithmic growth scale. -/
noncomputable def fixedJensenLogEnvelopeConstant : ℝ :=
  96 * max (Real.log 3) 1 +
    2 * (1 + Real.log 3) /
      Real.log ((7 / 4 : ℝ) / (17 / 10 : ℝ))

theorem fixedJensenLogEnvelopeConstant_pos :
    0 < fixedJensenLogEnvelopeConstant := by
  have hD : 0 < Real.log ((7 / 4 : ℝ) / (17 / 10 : ℝ)) := by
    apply Real.log_pos
    norm_num
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  unfold fixedJensenLogEnvelopeConstant
  positivity

/-- The fixed-disk Jensen/Borel loss is `O(1 + K)` with an explicit absolute
constant. -/
theorem fixedJensenLogEnvelope_le_constant_mul_one_add
    {K : ℝ} (hK : 0 ≤ K) :
    fixedJensenLogEnvelope K ≤
      fixedJensenLogEnvelopeConstant * (1 + K) := by
  let D : ℝ := Real.log ((7 / 4 : ℝ) / (17 / 10 : ℝ))
  let L : ℝ := Real.log 3
  let C0 : ℝ := max L 1
  have hD : 0 < D := by
    dsimp [D]
    apply Real.log_pos
    norm_num
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by norm_num)
  have hC0_one : 1 ≤ C0 := le_max_right _ _
  have hC0_L : L ≤ C0 := le_max_left _ _
  have hmain : max (K + L) 1 ≤ C0 * (1 + K) := by
    apply max_le
    · have hK_le : K ≤ C0 * K := by
        nlinarith
      nlinarith
    · nlinarith
  have hnum : K + L ≤ (1 + L) * (1 + K) := by
    nlinarith [mul_nonneg hL hK]
  have hfrac : (K + L) / D ≤ ((1 + L) / D) * (1 + K) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hnum hD.le
  have hfirst : 96 * max (K + L) 1 ≤
      (96 * C0) * (1 + K) := by
    nlinarith
  have hsecond : 2 * ((K + L) / D) ≤
      (2 * (1 + L) / D) * (1 + K) := by
    calc
      2 * ((K + L) / D) ≤
          2 * (((1 + L) / D) * (1 + K)) :=
        mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ = (2 * (1 + L) / D) * (1 + K) := by ring
  have hrewrite : fixedJensenLogEnvelope K =
      96 * max (K + L) 1 + 2 * ((K + L) / D) := by
    simp only [fixedJensenLogEnvelope, L, D]
    ring
  rw [hrewrite]
  change 96 * max (K + L) 1 + 2 * ((K + L) / D) ≤
    (96 * C0 + 2 * (1 + L) / D) * (1 + K)
  nlinarith

/-- A local zeta-growth estimate on two fixed disks gives a uniform bound for
the logarithmic derivative after all local zero principal parts are removed.

This theorem is scale agnostic: `M` and `K` may later be chosen from a
Vinogradov--Korobov growth estimate. -/
theorem norm_regularized_logDeriv_riemannZeta_le_of_fixed_jensen_growth
    {t M K : ℝ} (hheight : (7 / 4 : ℝ) < |t|) (hM : 1 ≤ M)
    (houter : ∀ z : ℂ,
      z ∈ Metric.sphere ((2 : ℂ) + I * t) (7 / 4 : ℝ) →
        ‖riemannZeta z‖ ≤ M)
    (hinner : ∀ z ∈ Metric.closedBall
      ((2 : ℂ) + I * t) (8 / 5 : ℝ),
        Real.log ‖riemannZeta z‖ ≤ K) :
    ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) 1,
      riemannZeta z ≠ 0 →
      ‖logDeriv riemannZeta z -
          ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
            (Metric.closedBall ((2 : ℂ) + I * t) (17 / 10 : ℝ)) u : ℂ) *
              (z - u)⁻¹‖ ≤
        fixedJensenRegularizedEnvelope M K := by
  intro z hz hzeta
  have hbound :=
    ZeroFreeRegion.norm_regularized_logDeriv_riemannZeta_le_of_good_radius_and_jensen_three_quarters
      (d := (1 : ℝ)) (a := (3 / 2 : ℝ)) (q := (8 / 5 : ℝ))
      (b := (17 / 10 : ℝ)) (R := (7 / 4 : ℝ)) (t := t)
      (M := M) (K := K) (rho := (1 / 16 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hheight hM (by norm_num) (by norm_num)
      houter hinner z hz hzeta
  simpa [fixedJensenRegularizedEnvelope] using hbound

/-- Logarithmic-growth specialization of the fixed Jensen estimate.

If both local growth inputs are bounded by the same nonnegative logarithmic
scale `K`, the regularized logarithmic derivative is bounded by the explicit
envelope with `M = exp K`. -/
theorem norm_regularized_logDeriv_riemannZeta_le_of_fixed_jensen_log_growth
    {t K : ℝ} (hheight : (7 / 4 : ℝ) < |t|) (hK : 0 ≤ K)
    (houter : ∀ z : ℂ,
      z ∈ Metric.sphere ((2 : ℂ) + I * t) (7 / 4 : ℝ) →
        ‖riemannZeta z‖ ≤ Real.exp K)
    (hinner : ∀ z ∈ Metric.closedBall
      ((2 : ℂ) + I * t) (8 / 5 : ℝ),
        Real.log ‖riemannZeta z‖ ≤ K) :
    ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) 1,
      riemannZeta z ≠ 0 →
      ‖logDeriv riemannZeta z -
          ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
            (Metric.closedBall ((2 : ℂ) + I * t) (17 / 10 : ℝ)) u : ℂ) *
              (z - u)⁻¹‖ ≤
        fixedJensenLogEnvelope K := by
  rw [← fixedJensenRegularizedEnvelope_exp]
  apply norm_regularized_logDeriv_riemannZeta_le_of_fixed_jensen_growth
    hheight (Real.one_le_exp hK) houter hinner

/-- A fixed-disk regularized bound implies zero repulsion from every
same-height zeta zero contained in the factorization disk. -/
theorem re_neg_deriv_div_riemannZeta_le_neg_inv_add_of_fixed_regularized_bound
    {E σ β t : ℝ}
    (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (ht : 4 ≤ |t|)
    (hβ0 : (3 / 10 : ℝ) ≤ β) (hβ1 : β < 1)
    (hzero : riemannZeta ((β : ℂ) + I * t) = 0)
    (hregular : ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) 1,
      riemannZeta z ≠ 0 →
      ‖logDeriv riemannZeta z -
          ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
            (Metric.closedBall ((2 : ℂ) + I * t) (17 / 10 : ℝ)) u : ℂ) *
              (z - u)⁻¹‖ ≤ E) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re ≤
      -1 / (σ - β) + E := by
  let c : ℂ := (2 : ℂ) + I * t
  let s : ℂ := (σ : ℂ) + I * t
  let rho : ℂ := (β : ℂ) + I * t
  let S : ℂ := ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
    (Metric.closedBall c (17 / 10 : ℝ)) u : ℂ) * (s - u)⁻¹
  let Rpart : ℂ := logDeriv riemannZeta s - S
  have hs : s ∈ Metric.closedBall c 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : s - c = ((σ - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s, c]
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have hrho : rho ∈ Metric.closedBall c (17 / 10 : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : rho - c = ((β - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [rho, c]
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have havoid : ∀ u : ℂ,
      u ∈ Metric.closedBall c (17 / 10 : ℝ) → u ≠ 1 := by
    intro u hu
    exact ZeroFreeRegion.closedBall_sigma_it_ne_one_of_height_add_le
      (z := u) (σ := 2) (t := t) (R := (17 / 10 : ℝ))
      (H := |t| - (17 / 10 : ℝ)) (by simpa [c] using hu)
      (by linarith) (by linarith)
  have hs_ne : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [s, hσ1])
  have hRnorm : ‖Rpart‖ ≤ E := by
    simpa [Rpart, S, s, c] using hregular s hs hs_ne
  have hprincipal : 1 / (σ - β) ≤ S.re := by
    have hsub : 0 < s.re - rho.re := by simp [s, rho]; linarith
    have h := ZeroFreeRegion.one_div_le_re_finsum_riemannZeta_divisor_mul_inv
      havoid (by simp [s, hσ1]) hrho (by simpa [rho] using hzero)
      (by simp [s, rho]) hsub
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

/-- The same fixed-disk regularized bound controls the boundary-strip real
part without assuming that the disk is zero free. -/
theorem re_neg_deriv_div_riemannZeta_le_of_fixed_regularized_bound
    {E σ t : ℝ}
    (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (ht : 4 ≤ |t|)
    (hregular : ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) 1,
      riemannZeta z ≠ 0 →
      ‖logDeriv riemannZeta z -
          ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
            (Metric.closedBall ((2 : ℂ) + I * t) (17 / 10 : ℝ)) u : ℂ) *
              (z - u)⁻¹‖ ≤ E) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re ≤ E := by
  let c : ℂ := (2 : ℂ) + I * t
  let s : ℂ := (σ : ℂ) + I * t
  let S : ℂ := ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
    (Metric.closedBall c (17 / 10 : ℝ)) u : ℂ) * (s - u)⁻¹
  let Rpart : ℂ := logDeriv riemannZeta s - S
  have hs : s ∈ Metric.closedBall c 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : s - c = ((σ - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s, c]
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have havoid : ∀ u : ℂ,
      u ∈ Metric.closedBall c (17 / 10 : ℝ) → u ≠ 1 := by
    intro u hu
    exact ZeroFreeRegion.closedBall_sigma_it_ne_one_of_height_add_le
      (z := u) (σ := 2) (t := t) (R := (17 / 10 : ℝ))
      (H := |t| - (17 / 10 : ℝ)) (by simpa [c] using hu)
      (by linarith) (by linarith)
  have hs_ne : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [s, hσ1])
  have hRnorm : ‖Rpart‖ ≤ E := by
    simpa [Rpart, S, s, c] using hregular s hs hs_ne
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

/-- Fixed-disk zeta growth gives the candidate-zero logarithmic-derivative
bound needed by the `3-4-1` zero-free closure. -/
theorem re_neg_deriv_div_riemannZeta_le_neg_inv_add_of_fixed_jensen_log_growth
    {K σ β t : ℝ} (hK : 0 ≤ K)
    (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (ht : 4 ≤ |t|)
    (hβ0 : (3 / 10 : ℝ) ≤ β) (hβ1 : β < 1)
    (hzero : riemannZeta ((β : ℂ) + I * t) = 0)
    (houter : ∀ z : ℂ,
      z ∈ Metric.sphere ((2 : ℂ) + I * t) (7 / 4 : ℝ) →
        ‖riemannZeta z‖ ≤ Real.exp K)
    (hinner : ∀ z ∈ Metric.closedBall
      ((2 : ℂ) + I * t) (8 / 5 : ℝ),
        Real.log ‖riemannZeta z‖ ≤ K) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re ≤
      -1 / (σ - β) + fixedJensenLogEnvelope K := by
  apply re_neg_deriv_div_riemannZeta_le_neg_inv_add_of_fixed_regularized_bound
    hσ1 hσ2 ht hβ0 hβ1 hzero
  exact norm_regularized_logDeriv_riemannZeta_le_of_fixed_jensen_log_growth
    (by linarith) hK houter hinner

/-- Fixed-disk zeta growth also controls the twice-height boundary term in
the `3-4-1` argument. -/
theorem re_neg_deriv_div_riemannZeta_le_of_fixed_jensen_log_growth
    {K σ t : ℝ} (hK : 0 ≤ K)
    (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (ht : 4 ≤ |t|)
    (houter : ∀ z : ℂ,
      z ∈ Metric.sphere ((2 : ℂ) + I * t) (7 / 4 : ℝ) →
        ‖riemannZeta z‖ ≤ Real.exp K)
    (hinner : ∀ z ∈ Metric.closedBall
      ((2 : ℂ) + I * t) (8 / 5 : ℝ),
        Real.log ‖riemannZeta z‖ ≤ K) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re ≤
      fixedJensenLogEnvelope K := by
  apply re_neg_deriv_div_riemannZeta_le_of_fixed_regularized_bound hσ1 hσ2 ht
  exact norm_regularized_logDeriv_riemannZeta_le_of_fixed_jensen_log_growth
    (by linarith) hK houter hinner

end ZeroFreeRegion.VinogradovKorobov
