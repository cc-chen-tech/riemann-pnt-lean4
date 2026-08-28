import PrimeNumberTheorem.CarlsonGaussianPoleFreeDerivMajorant
import PrimeNumberTheorem.CarlsonGaussianPoleFreeSectionDerivMemLp

/-!
# A neighborhood-uniform bound for the concrete Carlson derivative section

The center strip and radius are chosen so that the closed ball remains in the
wide strip on which the pole-free error derivative has degree-20 square
growth.  The lost half of the Gaussian decay absorbs the imaginary movement
inside the ball.
-/

open Complex Set

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

private theorem norm_add_sq_le_two_mul_add_sq (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hnorm := norm_add_le a b
  have hpow := pow_le_pow_left₀ (norm_nonneg (a + b)) hnorm 2
  have hdiff := sq_nonneg (‖a‖ - ‖b‖)
  nlinarith only [hpow, hdiff]

private theorem shifted_gaussian_half_decay
    {Delta x u e : ℝ} (hDelta : 0 < Delta)
    (hx : |x| ≤ 4) (he : |e| ≤ (1 / 48 : ℝ)) :
    Real.exp ((x ^ 2 - (u + e) ^ 2) / Delta ^ 2) ≤
      Real.exp ((16 + (1 / 48 : ℝ) ^ 2) / Delta ^ 2) *
        Real.exp (-(1 / (2 * Delta ^ 2)) * u ^ 2) := by
  have hDelta0 : Delta ≠ 0 := ne_of_gt hDelta
  have hquad : u ^ 2 / 2 - e ^ 2 ≤ (u + e) ^ 2 := by
    have hsquare := sq_nonneg (u + 2 * e)
    nlinarith only [hsquare]
  have heSq : e ^ 2 ≤ (1 / 48 : ℝ) ^ 2 := by
    rw [← sq_abs e]
    exact (sq_le_sq₀ (abs_nonneg e) (by norm_num)).2 he
  have hxSq : x ^ 2 ≤ 16 := by
    rw [← sq_abs x, show (16 : ℝ) = 4 ^ 2 by norm_num]
    exact (sq_le_sq₀ (abs_nonneg x) (by norm_num)).2 hx
  have hnum :
      x ^ 2 - (u + e) ^ 2 ≤
        16 + (1 / 48 : ℝ) ^ 2 - u ^ 2 / 2 := by
    linarith only [hquad, heSq, hxSq]
  have hDeltaSq : 0 < Delta ^ 2 := sq_pos_of_pos hDelta
  have hexponent :
      (x ^ 2 - (u + e) ^ 2) / Delta ^ 2 ≤
        (16 + (1 / 48 : ℝ) ^ 2) / Delta ^ 2 -
          (1 / (2 * Delta ^ 2)) * u ^ 2 := by
    calc
      (x ^ 2 - (u + e) ^ 2) / Delta ^ 2 ≤
          (16 + (1 / 48 : ℝ) ^ 2 - u ^ 2 / 2) / Delta ^ 2 :=
        div_le_div_of_nonneg_right hnum hDeltaSq.le
      _ = (16 + (1 / 48 : ℝ) ^ 2) / Delta ^ 2 -
            (1 / (2 * Delta ^ 2)) * u ^ 2 := by
        field_simp [pow_ne_zero 2 hDelta0]
  calc
    Real.exp ((x ^ 2 - (u + e) ^ 2) / Delta ^ 2)
        ≤ Real.exp ((16 + (1 / 48 : ℝ) ^ 2) / Delta ^ 2 -
            (1 / (2 * Delta ^ 2)) * u ^ 2) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp ((16 + (1 / 48 : ℝ) ^ 2) / Delta ^ 2) *
          Real.exp (-(1 / (2 * Delta ^ 2)) * u ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

private theorem linear_factor_sq_le_degree_twenty
    {Delta C D P : ℝ} (hDelta : 0 < Delta) (hC : 0 ≤ C)
    (hP : 1 ≤ P) {q Hval : ℂ}
    (hq : ‖q‖ ^ 2 ≤ 25 * P ^ 2)
    (hH : ‖Hval‖ ^ 2 ≤ C * D ^ 10 * P ^ 10) :
    ‖q / (Delta : ℂ) ^ 2 * Hval‖ ^ 2 ≤
      (25 * C * D ^ 10 / Delta ^ 4) * P ^ 20 := by
  have hDelta0 : Delta ≠ 0 := ne_of_gt hDelta
  have hfactor :
      ‖q / (Delta : ℂ) ^ 2‖ ^ 2 ≤ (25 / Delta ^ 4) * P ^ 2 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hDelta]
    calc
      (‖q‖ / Delta ^ 2) ^ 2 = ‖q‖ ^ 2 / Delta ^ 4 := by ring
      _ ≤ (25 * P ^ 2) / Delta ^ 4 :=
        div_le_div_of_nonneg_right hq (by positivity)
      _ = (25 / Delta ^ 4) * P ^ 2 := by ring
  rw [norm_mul, mul_pow]
  calc
    ‖q / (Delta : ℂ) ^ 2‖ ^ 2 * ‖Hval‖ ^ 2
        ≤ ((25 / Delta ^ 4) * P ^ 2) *
            (C * D ^ 10 * P ^ 10) := by gcongr
    _ = (25 * C * D ^ 10 / Delta ^ 4) * P ^ 12 := by
      field_simp [pow_ne_zero 4 hDelta0]
    _ ≤ (25 * C * D ^ 10 / Delta ^ 4) * P ^ 20 := by
      apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP (by norm_num))
      positivity

private theorem two_weighted_sq_bounds
    {W A0 A1 P L D : ℝ} (hW : 0 ≤ W)
    (hL : L ≤ A0 * P ^ 20) (hD : D ≤ A1 * P ^ 20) :
    2 * (W * L + W * D) ≤ W * (2 * (A0 + A1) * P ^ 20) := by
  calc
    2 * (W * L + W * D) ≤
        2 * (W * (A0 * P ^ 20) + W * (A1 * P ^ 20)) := by
      gcongr
    _ = W * (2 * (A0 + A1) * P ^ 20) := by ring

set_option maxHeartbeats 500000 in
/-- On any sufficiently small ball staying a double-radius away from the
strip boundary, the exact concrete derivative is bounded by one integrable
centered Gaussian majorant. -/
theorem exists_carlsonGaussianDerivativeMajorant_bound_on_closedBall_of_radius
    {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {rho : ℝ} (hrho : 0 < rho) (hrhoSmall : rho ≤ 1 / 48)
    (hleft : 1 / 2 + 2 * rho ≤ z.re)
    (hright : z.re + 2 * rho ≤ 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v ∈ Metric.closedBall z rho, ∀ t : ℝ,
      ‖carlsonGaussianHilbertSectionDeriv Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1) v t‖ ^ 2 ≤
        carlsonGaussianDerivativeMajorant Delta w z.im K t := by
  rcases
      exists_norm_sq_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_half_four
        hY0 hY01 with ⟨C0, hC0, hH⟩
  rcases
      exists_norm_sq_deriv_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_compact_inner_strip
        hY0 hY01 hrho
          (a := z.re - rho) (b := z.re + rho) (r := rho)
          (by linarith) (by linarith) with ⟨C1, hC1, hH'⟩
  have hDelta0 : Delta ≠ 0 := ne_of_gt hDelta
  let D0 : ℝ := |w| + 4
  let D1 : ℝ := |w| + 5
  let A0 : ℝ := 25 * C0 * D0 ^ 10 / Delta ^ 4
  let A1 : ℝ := C1 * D1 ^ 20
  let G : ℝ := Real.exp ((16 + (1 / 48 : ℝ) ^ 2) / Delta ^ 2)
  let K : ℝ := G * (2 * (A0 + A1))
  have hD0 : 1 ≤ D0 := by
    dsimp [D0]
    linarith [abs_nonneg w]
  have hD1 : 1 ≤ D1 := by
    dsimp [D1]
    linarith [abs_nonneg w]
  have hA0 : 0 ≤ A0 := by
    dsimp [A0]
    positivity
  have hA1 : 0 ≤ A1 := by
    dsimp [A1]
    positivity
  have hG : 0 ≤ G := by
    dsimp [G]
    positivity
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro v hv t
  have hdist : dist v z ≤ rho := Metric.mem_closedBall.mp hv
  have hreDiff : |v.re - z.re| ≤ rho := by
    calc
      |v.re - z.re| = |(v - z).re| := by simp
      _ ≤ ‖v - z‖ := Complex.abs_re_le_norm (v - z)
      _ = dist v z := by rw [dist_eq_norm]
      _ ≤ rho := hdist
  have himDiff : |v.im - z.im| ≤ rho := by
    calc
      |v.im - z.im| = |(v - z).im| := by simp
      _ ≤ ‖v - z‖ := Complex.abs_im_le_norm (v - z)
      _ = dist v z := by rw [dist_eq_norm]
      _ ≤ rho := hdist
  have hvreLocal : v.re ∈ Icc (z.re - rho) (z.re + rho) := by
    rw [abs_le] at hreDiff
    constructor <;> linarith
  have hvreHalfFour : v.re ∈ Icc (1 / 2 : ℝ) 4 := by
    constructor <;> linarith [hvreLocal.1, hvreLocal.2, hleft, hright]
  have hvreAbs : |v.re| ≤ 4 := by
    rw [abs_of_nonneg (by linarith [hvreHalfFour.1])]
    exact hvreHalfFour.2
  let u : ℝ := z.im + t - w
  let e : ℝ := v.im - z.im
  let P : ℝ := 1 + |u|
  have heAbs : |e| ≤ rho := by simpa [e] using himDiff
  have heAbs48 : |e| ≤ (1 / 48 : ℝ) := heAbs.trans hrhoSmall
  have hP : 1 ≤ P := by
    dsimp [P]
    linarith [abs_nonneg u]
  have himIdentity : v.im + t = u + w + e := by
    dsimp [u, e]
    ring
  have himAbs : |v.im + t| ≤ |u| + |w| + |e| := by
    rw [himIdentity]
    calc
      |u + w + e| ≤ |u + w| + |e| := abs_add_le _ _
      _ ≤ (|u| + |w|) + |e| := by
        have huw := abs_add_le u w
        linarith
  have hheight0 : |v.im + t| + 3 ≤ D0 * P := by
    have heSmall : |e| ≤ 1 := heAbs48.trans (by norm_num)
    have huD : |u| ≤ D0 * |u| :=
      le_mul_of_one_le_left (abs_nonneg u) hD0
    dsimp [D0, P]
    nlinarith
  have hheight1 : |v.im + t| + 3 + rho ≤ D1 * P := by
    have heSmall : |e| ≤ 1 := heAbs48.trans (by norm_num)
    have hrhoOne : rho ≤ 1 := hrhoSmall.trans (by norm_num)
    have huD : |u| ≤ D1 * |u| :=
      le_mul_of_one_le_left (abs_nonneg u) hD1
    dsimp [D1, P]
    nlinarith
  have hHsq :
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
          (v + I * (t : ℂ))‖ ^ 2 ≤ C0 * D0 ^ 10 * P ^ 10 := by
    have hraw := hH (s := v + I * (t : ℂ)) (by simpa using hvreHalfFour)
    calc
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
          (v + I * (t : ℂ))‖ ^ 2
          ≤ C0 * (|v.im + t| + 3) ^ 10 := by simpa using hraw
      _ ≤ C0 * (D0 * P) ^ 10 := by
        gcongr
      _ = C0 * D0 ^ 10 * P ^ 10 := by ring
  have hHderivSq :
      ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
          (v + I * (t : ℂ))‖ ^ 2 ≤ A1 * P ^ 20 := by
    have hraw := hH' (s := v + I * (t : ℂ)) (by simpa using hvreLocal)
    calc
      ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
          (v + I * (t : ℂ))‖ ^ 2
          ≤ C1 * (|v.im + t| + 3 + rho) ^ 20 := by simpa using hraw
      _ ≤ C1 * (D1 * P) ^ 20 := by
        gcongr
      _ = A1 * P ^ 20 := by
        dsimp [A1]
        ring
  let q : ℂ := v + I * (t : ℂ) - I * (w : ℂ)
  have hqre : q.re = v.re := by simp [q]
  have hqim : q.im = u + e := by
    dsimp [q]
    simp only [mul_im, I_re, ofReal_im, I_im, ofReal_re,
      zero_mul, one_mul]
    dsimp [u, e]
    ring
  have hqnorm : ‖q‖ ≤ 5 * P := by
    calc
      ‖q‖ ≤ |q.re| + |q.im| := Complex.norm_le_abs_re_add_abs_im q
      _ = |v.re| + |u + e| := by rw [hqre, hqim]
      _ ≤ |v.re| + (|u| + |e|) := by gcongr; exact abs_add_le _ _
      _ ≤ 5 * P := by
        have heSmall : |e| ≤ 1 := heAbs48.trans (by norm_num)
        calc
          |v.re| + (|u| + |e|) ≤ 4 + (|u| + 1) := by linarith
          _ ≤ 5 * (1 + |u|) := by linarith [abs_nonneg u]
          _ = 5 * P := by rfl
  have hqSq : ‖q‖ ^ 2 ≤ 25 * P ^ 2 := by
    calc
      ‖q‖ ^ 2 ≤ (5 * P) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg q) hqnorm 2
      _ = 25 * P ^ 2 := by ring
  have hlinearSq :
      ‖carlsonGaussianLinearErrorFactor Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
          (v + I * (t : ℂ))‖ ^ 2 ≤ A0 * P ^ 20 := by
    unfold carlsonGaussianLinearErrorFactor
    change ‖q / (Delta : ℂ) ^ 2 *
        poleFreeTwoScaleMollifiedZetaError Y0 Y1
          (v + I * (t : ℂ))‖ ^ 2 ≤ _
    exact linear_factor_sq_le_degree_twenty hDelta hC0 hP hqSq hHsq
  have hgaussian :
      Real.exp ((v.re ^ 2 - (v.im + t - w) ^ 2) / Delta ^ 2) ≤
        G * Real.exp (-(1 / (2 * Delta ^ 2)) * u ^ 2) := by
    have himShift : v.im + t - w = u + e := by
      dsimp [u, e]
      ring
    rw [himShift]
    exact shifted_gaussian_half_decay hDelta hvreAbs heAbs48
  let S0 := carlsonGaussianHilbertSection Delta w
    (carlsonGaussianLinearErrorFactor Delta w
      (poleFreeTwoScaleMollifiedZetaError Y0 Y1)) v t
  let S1 := carlsonGaussianHilbertSection Delta w
    (deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1)) v t
  have hadd : ‖S0 + S1‖ ^ 2 ≤ 2 * (‖S0‖ ^ 2 + ‖S1‖ ^ 2) :=
    norm_add_sq_le_two_mul_add_sq S0 S1
  have hS0 : ‖S0‖ ^ 2 =
      Real.exp ((v.re ^ 2 - (v.im + t - w) ^ 2) / Delta ^ 2) *
        ‖carlsonGaussianLinearErrorFactor Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
          (v + I * (t : ℂ))‖ ^ 2 := by
    dsimp [S0]
    exact norm_sq_carlsonGaussianHilbertSection hDelta0 _ v t
  have hS1 : ‖S1‖ ^ 2 =
      Real.exp ((v.re ^ 2 - (v.im + t - w) ^ 2) / Delta ^ 2) *
        ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
          (v + I * (t : ℂ))‖ ^ 2 := by
    dsimp [S1]
    exact norm_sq_carlsonGaussianHilbertSection hDelta0 _ v t
  rw [carlsonGaussianHilbertSectionDeriv_eq_add]
  change ‖S0 + S1‖ ^ 2 ≤ _
  calc
    ‖S0 + S1‖ ^ 2
        ≤ 2 * (‖S0‖ ^ 2 + ‖S1‖ ^ 2) := hadd
    _ = 2 * (
          Real.exp ((v.re ^ 2 - (v.im + t - w) ^ 2) / Delta ^ 2) *
              ‖carlsonGaussianLinearErrorFactor Delta w
                (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
                (v + I * (t : ℂ))‖ ^ 2 +
          Real.exp ((v.re ^ 2 - (v.im + t - w) ^ 2) / Delta ^ 2) *
              ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
                (v + I * (t : ℂ))‖ ^ 2) := by rw [hS0, hS1]
    _ ≤ Real.exp ((v.re ^ 2 - (v.im + t - w) ^ 2) / Delta ^ 2) *
          (2 * (A0 + A1) * P ^ 20) := by
        have hweight : 0 ≤
            Real.exp ((v.re ^ 2 - (v.im + t - w) ^ 2) / Delta ^ 2) :=
          (Real.exp_pos _).le
        exact two_weighted_sq_bounds hweight hlinearSq hHderivSq
    _ ≤ (G * Real.exp (-(1 / (2 * Delta ^ 2)) * u ^ 2)) *
          (2 * (A0 + A1) * P ^ 20) := by
        gcongr
    _ = carlsonGaussianDerivativeMajorant Delta w z.im K t := by
        dsimp [carlsonGaussianDerivativeMajorant, K, P, u]
        ring

/-- The fixed-radius interface used by the initial shifted-contour
specialization. -/
theorem exists_carlsonGaussianDerivativeMajorant_bound_on_closedBall
    {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hzre : z.re ∈ Icc (29 / 48 : ℝ) (187 / 48)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v ∈ Metric.closedBall z (1 / 48 : ℝ), ∀ t : ℝ,
      ‖carlsonGaussianHilbertSectionDeriv Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1) v t‖ ^ 2 ≤
        carlsonGaussianDerivativeMajorant Delta w z.im K t := by
  apply
    exists_carlsonGaussianDerivativeMajorant_bound_on_closedBall_of_radius
      hDelta hY0 hY01 (rho := (1 / 48 : ℝ)) (by norm_num) (by norm_num)
  · linarith [hzre.1]
  · linarith [hzre.2]

end CarlsonZeroDensity
end PrimeNumberTheorem
