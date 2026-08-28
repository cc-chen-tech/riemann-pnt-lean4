import PrimeNumberTheorem.CarlsonPoleFreeMollifiedErrorGrowth
import Mathlib.Analysis.Complex.Liouville

/-!
# Cauchy derivative growth for the pole-free Carlson error

A fixed radius `1/24` around the inner strip
`7/12 ≤ Re(s) ≤ 47/12` stays inside the already controlled strip
`1/2 ≤ Re(s) ≤ 4`.  Cauchy's estimate therefore turns the existing
degree-ten square growth of the error into a (deliberately coarse)
degree-twenty square growth bound for its derivative.
-/

open Complex Set

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Cauchy's estimate on an arbitrary compact substrip of
`1/2 < Re(s) < 4`.  The radius is explicit, so later callers may choose it
from the distance of a given point to the two boundary lines. -/
theorem
    exists_norm_sq_deriv_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_compact_inner_strip
    {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {a b r : ℝ} (hr : 0 < r)
    (ha : 1 / 2 + r ≤ a) (hb : b + r ≤ 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {s : ℂ},
      s.re ∈ Icc a b →
      ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1) s‖ ^ 2 ≤
        K * (|s.im| + 3 + r) ^ 20 := by
  rcases
      exists_norm_sq_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_half_four
        hY0 hY01 with ⟨C, hC, hgrowth⟩
  let K : ℝ := ((C + 1) / r) ^ 2
  refine ⟨K, sq_nonneg _, ?_⟩
  intro s hsre
  have hdiffClosed : DifferentiableOn ℂ
      (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
      (Metric.closedBall s r) := by
    intro z hz
    have hdist : dist z s ≤ r := Metric.mem_closedBall.mp hz
    have hreDiff : |z.re - s.re| ≤ r := by
      calc
        |z.re - s.re| = |(z - s).re| := by simp
        _ ≤ ‖z - s‖ := Complex.abs_re_le_norm (z - s)
        _ = dist z s := by rw [dist_eq_norm]
        _ ≤ r := hdist
    have hzre : 0 < z.re := by
      rw [abs_le] at hreDiff
      linarith [hsre.1, ha]
    exact
      (analyticOnNhd_poleFreeTwoScaleMollifiedZetaError_re_gt
        (theta := 0) le_rfl Y0 Y1 z hzre).differentiableAt.differentiableWithinAt
  have hdiff : DiffContOnCl ℂ
      (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
      (Metric.ball s r) :=
    hdiffClosed.diffContOnCl_ball subset_rfl
  let A : ℝ := |s.im| + 3 + r
  have hA : 1 ≤ A := by
    dsimp [A]
    linarith [abs_nonneg s.im]
  have hsphere : ∀ z ∈ Metric.sphere s r,
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 z‖ ≤
        (C + 1) * A ^ 10 := by
    intro z hz
    have hdist : dist z s = r := Metric.mem_sphere.mp hz
    have hreDiff : |z.re - s.re| ≤ r := by
      calc
        |z.re - s.re| = |(z - s).re| := by simp
        _ ≤ ‖z - s‖ := Complex.abs_re_le_norm (z - s)
        _ = dist z s := by rw [dist_eq_norm]
        _ = r := hdist
    have hzre : z.re ∈ Icc (1 / 2 : ℝ) 4 := by
      rw [abs_le] at hreDiff
      constructor <;> linarith [hsre.1, hsre.2, ha, hb]
    have himDiff : |z.im - s.im| ≤ r := by
      calc
        |z.im - s.im| = |(z - s).im| := by simp
        _ ≤ ‖z - s‖ := Complex.abs_im_le_norm (z - s)
        _ = dist z s := by rw [dist_eq_norm]
        _ = r := hdist
    have hheight : |z.im| + 3 ≤ A := by
      have hzabs : |z.im| ≤ |s.im| + |z.im - s.im| := by
        calc
          |z.im| = |s.im + (z.im - s.im)| := by congr 1 <;> ring
          _ ≤ |s.im| + |z.im - s.im| := abs_add_le _ _
      dsimp [A]
      linarith
    have hpow : (|z.im| + 3) ^ 10 ≤ A ^ 10 :=
      pow_le_pow_left₀ (by positivity) hheight 10
    have hraw := hgrowth (s := z) hzre
    have hnormLinear :
        ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 z‖ ≤
          ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 z‖ ^ 2 + 1 := by
      nlinarith [sq_nonneg
        (‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 z‖ - 1 / 2)]
    calc
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 z‖
          ≤ ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 z‖ ^ 2 + 1 :=
            hnormLinear
      _ ≤ C * (|z.im| + 3) ^ 10 + 1 := by linarith [hraw]
      _ ≤ C * A ^ 10 + 1 := by
        have hpolyC := mul_le_mul_of_nonneg_left hpow hC
        linarith
      _ ≤ C * A ^ 10 + A ^ 10 := by
        have hA10 : 1 ≤ A ^ 10 := one_le_pow₀ hA
        linarith
      _ = (C + 1) * A ^ 10 := by ring
  have hderiv := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (c := s) (R := r) (C := (C + 1) * A ^ 10)
    hr hdiff hsphere
  calc
    ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1) s‖ ^ 2
        ≤ (((C + 1) * A ^ 10) / r) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hderiv 2
    _ = K * (|s.im| + 3 + r) ^ 20 := by
      dsimp [K, A]
      ring

/-- The derivative of the pole-free two-scale error has uniform polynomial
square growth on a fixed inner substrip.  The loss from degree ten to degree
twenty avoids square roots and is harmless under the Gaussian weight. -/
theorem
    exists_norm_sq_deriv_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_wide_inner_strip
    {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℂ},
      s.re ∈ Icc (7 / 12 : ℝ) (47 / 12) →
      ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1) s‖ ^ 2 ≤
        C * (|s.im| + 4) ^ 20 := by
  rcases
      exists_norm_sq_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_half_four
        hY0 hY01 with ⟨C, hC, hgrowth⟩
  let K : ℝ := (24 * (C + 1)) ^ 2
  refine ⟨K, sq_nonneg _, ?_⟩
  intro s hsre
  have hdiffClosed : DifferentiableOn ℂ
      (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
      (Metric.closedBall s (1 / 24 : ℝ)) := by
    intro z hz
    have hdist : dist z s ≤ (1 / 24 : ℝ) :=
      Metric.mem_closedBall.mp hz
    have hreDiff : |z.re - s.re| ≤ (1 / 24 : ℝ) := by
      calc
        |z.re - s.re| = |(z - s).re| := by simp
        _ ≤ ‖z - s‖ := Complex.abs_re_le_norm (z - s)
        _ = dist z s := by rw [dist_eq_norm]
        _ ≤ 1 / 24 := hdist
    have hzre : 0 < z.re := by
      rw [abs_le] at hreDiff
      linarith [hsre.1]
    exact
      (analyticOnNhd_poleFreeTwoScaleMollifiedZetaError_re_gt
        (theta := 0) le_rfl Y0 Y1 z hzre).differentiableAt.differentiableWithinAt
  have hdiff : DiffContOnCl ℂ
      (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
      (Metric.ball s (1 / 24 : ℝ)) :=
    hdiffClosed.diffContOnCl_ball subset_rfl
  let A : ℝ := |s.im| + 4
  have hA : 1 ≤ A := by
    dsimp [A]
    linarith [abs_nonneg s.im]
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hsphere : ∀ z ∈ Metric.sphere s (1 / 24 : ℝ),
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 z‖ ≤
        (C + 1) * A ^ 10 := by
    intro z hz
    have hdist : dist z s = (1 / 24 : ℝ) := Metric.mem_sphere.mp hz
    have hreDiff : |z.re - s.re| ≤ (1 / 24 : ℝ) := by
      calc
        |z.re - s.re| = |(z - s).re| := by simp
        _ ≤ ‖z - s‖ := Complex.abs_re_le_norm (z - s)
        _ = dist z s := by rw [dist_eq_norm]
        _ = 1 / 24 := hdist
    have hzre : z.re ∈ Icc (1 / 2 : ℝ) 4 := by
      rw [abs_le] at hreDiff
      constructor <;> linarith [hsre.1, hsre.2]
    have himDiff : |z.im - s.im| ≤ (1 / 24 : ℝ) := by
      calc
        |z.im - s.im| = |(z - s).im| := by simp
        _ ≤ ‖z - s‖ := Complex.abs_im_le_norm (z - s)
        _ = dist z s := by rw [dist_eq_norm]
        _ = 1 / 24 := hdist
    have hheight : |z.im| + 3 ≤ A := by
      have hzabs : |z.im| ≤ |s.im| + |z.im - s.im| := by
        calc
          |z.im| = |s.im + (z.im - s.im)| := by congr 1 <;> ring
          _ ≤ |s.im| + |z.im - s.im| := abs_add_le _ _
      dsimp [A]
      linarith
    have hpow : (|z.im| + 3) ^ 10 ≤ A ^ 10 :=
      pow_le_pow_left₀ (by positivity) hheight 10
    have hraw := hgrowth (s := z) hzre
    have hnormLinear :
        ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 z‖ ≤
          ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 z‖ ^ 2 + 1 := by
      nlinarith [sq_nonneg
        (‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 z‖ - 1 / 2)]
    calc
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 z‖
          ≤ ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 z‖ ^ 2 + 1 :=
            hnormLinear
      _ ≤ C * (|z.im| + 3) ^ 10 + 1 := by
        linarith [hraw]
      _ ≤ C * A ^ 10 + 1 := by
        have hpolyC : C * (|z.im| + 3) ^ 10 ≤ C * A ^ 10 :=
          mul_le_mul_of_nonneg_left hpow hC
        linarith
      _ ≤ C * A ^ 10 + A ^ 10 := by
        have hA10 : 1 ≤ A ^ 10 := one_le_pow₀ hA
        linarith
      _ = (C + 1) * A ^ 10 := by ring
  have hderiv := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (c := s) (R := (1 / 24 : ℝ)) (C := (C + 1) * A ^ 10)
    (by norm_num) hdiff hsphere
  have hderiv' :
      ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1) s‖ ≤
        24 * (C + 1) * A ^ 10 := by
    calc
      ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1) s‖
          ≤ ((C + 1) * A ^ 10) / (1 / 24 : ℝ) := hderiv
      _ = 24 * (C + 1) * A ^ 10 := by ring
  calc
    ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1) s‖ ^ 2
        ≤ (24 * (C + 1) * A ^ 10) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hderiv' 2
    _ = K * (|s.im| + 4) ^ 20 := by
      dsimp [K, A]
      ring

/-- The original narrower-strip interface, retained as a direct corollary of
the wider Cauchy estimate. -/
theorem
    exists_norm_sq_deriv_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_inner_strip
    {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℂ},
      s.re ∈ Icc (2 / 3 : ℝ) (47 / 12) →
      ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1) s‖ ^ 2 ≤
        C * (|s.im| + 4) ^ 20 := by
  rcases
      exists_norm_sq_deriv_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_wide_inner_strip
        hY0 hY01 with ⟨C, hC, hwide⟩
  refine ⟨C, hC, ?_⟩
  intro s hs
  apply hwide
  constructor <;> linarith [hs.1, hs.2]

end CarlsonZeroDensity
end PrimeNumberTheorem
