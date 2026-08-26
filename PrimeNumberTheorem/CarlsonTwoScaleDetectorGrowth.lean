import PrimeNumberTheorem.CarlsonDetectorGrowth
import PrimeNumberTheorem.CarlsonTwoScaleFarRight

open Complex MeromorphicOn

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-!
# Fixed Jensen-circle growth for the two-scale Carlson detector

This file supplies the two detector-specific inputs used by the otherwise
coefficient-generic Jensen and horizontal-side argument: polynomial growth
on the outer circle and a quantitative lower bound at its right-line center.
-/

/-- The fixed outer Jensen disk stays in `Re(s)>0`, where the regularized
two-scale detector is analytic. -/
theorem analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_fixedJensenOuterDisk
    (Y0 Y1 : ℕ) (T : ℝ) :
    AnalyticOnNhd ℂ (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
      (Metric.closedBall
        ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ)) := by
  intro z hz
  have hdist :
      ‖z - ((4 : ℂ) + I * (T + 1 / 2))‖ ≤ (31 / 8 : ℝ) := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
  have hreAbs :=
    Complex.abs_re_le_norm (z - ((4 : ℂ) + I * (T + 1 / 2)))
  have hzre : 0 < z.re := by
    have : |z.re - 4| ≤ (31 / 8 : ℝ) := by
      simpa using hreAbs.trans hdist
    rw [abs_le] at this
    linarith
  exact analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_re_gt
    (theta := (0 : ℝ)) le_rfl Y0 Y1 z hzre

/-- The regularized two-scale detector has the same polynomial fixed-circle
growth as the sharp detector, with the outer support `Y1` replacing `X`. -/
theorem exists_norm_regularizedTwoScaleCarlsonZeroDetector_le_fixedJensenSphere :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 1 ≤ Y0 → Y0 < Y1 →
      ∀ {T : ℝ}, 5 ≤ T → ∀ {z : ℂ},
        z ∈ Metric.sphere
          ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ) →
        ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 z‖ ≤
          C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10 := by
  rcases exists_norm_riemannZeta_le_fixedJensenSphere with
    ⟨C₀, hC₀, hzeta⟩
  refine ⟨2 * C₀ ^ 2, by nlinarith, ?_⟩
  intro Y0 Y1 hY0 hY01 T hT z hz
  let U : ℝ := T + 14
  let A : ℝ := C₀ * (Y1 : ℝ) * U ^ 4
  have hU : 1 ≤ U := by dsimp [U]; linarith
  have hY1 : 1 ≤ Y1 := hY0.trans hY01.le
  have hY1Real : 1 ≤ (Y1 : ℝ) := by exact_mod_cast hY1
  have hUPow : 1 ≤ U ^ 4 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hU 4
  have hA : 2 ≤ A := by
    dsimp [A]
    nlinarith [mul_nonneg (show 0 ≤ C₀ by linarith)
        (show 0 ≤ (Y1 : ℝ) by positivity),
      mul_nonneg (show 0 ≤ C₀ * (Y1 : ℝ) by positivity)
        (show 0 ≤ U ^ 4 by positivity)]
  have hre := fixedJensenSphere_re_mem_Icc hT hz
  have him := fixedJensenSphere_abs_im_mem_Icc hT hz
  have hz0 : z ≠ 0 := by
    intro hz0
    subst z
    norm_num at him
  have hz1 : z ≠ 1 := by
    intro hz1
    subst z
    norm_num at him
  have hmollifier :
      ‖HardyTheorem.twoScaleSelbergMollifier Y0 Y1 z‖ ≤ (Y1 : ℝ) :=
    HardyTheorem.norm_twoScaleSelbergMollifier_le_natCast hY0 hY01 hre.1
  have hw :
      ‖riemannZeta z * HardyTheorem.twoScaleSelbergMollifier Y0 Y1 z‖ ≤ A := by
    rw [norm_mul]
    have hmul := mul_le_mul (hzeta hT hz) hmollifier
      (norm_nonneg (HardyTheorem.twoScaleSelbergMollifier Y0 Y1 z))
      (mul_nonneg (show 0 ≤ C₀ by linarith) (pow_nonneg (by positivity) 4))
    simpa [A, U, mul_assoc, mul_left_comm, mul_comm] using hmul
  let w : ℂ :=
    riemannZeta z * HardyTheorem.twoScaleSelbergMollifier Y0 Y1 z
  have htwoSub : ‖(2 : ℂ) - w‖ ≤ 2 + A := by
    calc
      ‖(2 : ℂ) - w‖ ≤ ‖(2 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ 2 + A := by simpa [w] using add_le_add_left hw 2
  have hdetector : ‖w * (2 - w)‖ ≤ 2 * A ^ 2 := by
    calc
      ‖w * (2 - w)‖ = ‖w‖ * ‖(2 : ℂ) - w‖ := norm_mul _ _
      _ ≤ A * (2 + A) :=
        mul_le_mul (by simpa [w] using hw) htwoSub (norm_nonneg _)
          (by positivity)
      _ ≤ A * (2 * A) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = 2 * A ^ 2 := by ring
  have hsub := norm_sub_one_le_on_fixedJensenSphere hT hz
  have hsubPow : ‖z - 1‖ ^ 2 ≤ U ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa [U] using hsub
  rw [regularizedTwoScaleCarlsonZeroDetector_eq_sub_one_sq_mul hz0 hz1,
    twoScaleCarlsonZeroDetector_factorization]
  change ‖(z - 1) ^ 2 * (w * (2 - w))‖ ≤ _
  calc
    ‖(z - 1) ^ 2 * (w * (2 - w))‖ =
        ‖z - 1‖ ^ 2 * ‖w * (2 - w)‖ := by rw [norm_mul, norm_pow]
    _ ≤ U ^ 2 * (2 * A ^ 2) :=
      mul_le_mul hsubPow hdetector (norm_nonneg _)
        (pow_nonneg (by positivity) 2)
    _ = (2 * C₀ ^ 2) * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10 := by
      dsimp [A, U]
      ring

/-- Complete multiplicity in the inner factorization disk, measured using
the divisor on the enclosing Jensen disk. -/
noncomputable def regularizedTwoScaleCarlsonFactorDiskZeroMass
    (Y0 Y1 : ℕ) (T : ℝ) : ℝ :=
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let outer := Metric.closedBall c (31 / 8 : ℝ)
  ∑ᶠ u ∈ (Metric.closedBall c (123 / 32 : ℝ) : Set ℂ),
    (MeromorphicOn.divisor
      (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) outer u : ℝ)

/-- Jensen converts the outer-circle polynomial bound and a quantitative
right-line center bound into logarithmic local divisor mass. -/
theorem exists_regularizedTwoScaleCarlsonFactorDiskZeroMass_le_logPolynomial :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 1 ≤ Y0 → Y0 < Y1 →
      ∀ {T : ℝ}, 5 ≤ T →
        ‖twoScaleMollifiedZetaError Y0 Y1
          ((4 : ℂ) + I * (T + 1 / 2))‖ ≤ (1 / 3 : ℝ) →
        regularizedTwoScaleCarlsonFactorDiskZeroMass Y0 Y1 T ≤
          Real.log (C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10) /
            Real.log ((31 / 8 : ℝ) / (123 / 32 : ℝ)) := by
  rcases
      exists_norm_regularizedTwoScaleCarlsonZeroDetector_le_fixedJensenSphere with
    ⟨C, hC, hsphere⟩
  refine ⟨C, hC, ?_⟩
  intro Y0 Y1 hY0 hY01 T hT herr
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let M : ℝ := C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10
  have hY1 : 1 ≤ Y1 := hY0.trans hY01.le
  have hY1Real : 1 ≤ (Y1 : ℝ) := by exact_mod_cast hY1
  have hTPow : 1 ≤ (T + 14) ^ 10 := by
    have hTBase : 1 ≤ T + 14 := by linarith
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hTBase 10
  have hY1Pow : 1 ≤ (Y1 : ℝ) ^ 2 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hY1Real 2
  have hM : 1 ≤ M := by
    dsimp [M]
    simpa using
      mul_le_mul (mul_le_mul hC hY1Pow (by norm_num) (by positivity))
        hTPow (by norm_num) (by positivity)
  have hanalytic : AnalyticOnNhd ℂ
      (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
      (Metric.closedBall c (31 / 8 : ℝ)) := by
    simpa [c] using
      analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_fixedJensenOuterDisk
        Y0 Y1 T
  have hcenter :
      1 ≤ ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 c‖ := by
    apply one_le_norm_regularizedTwoScaleCarlsonZeroDetector_of_four_le_re
    · simp [c]
    · simpa [c] using herr
  have hcircle : Real.circleAverage
      (Real.log ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 ·‖)
        c (31 / 8 : ℝ) ≤ Real.log M := by
    apply circleAverage_log_norm_le_log_of_norm_le
    · norm_num
    · exact hanalytic.meromorphicOn
    · exact hM
    · intro z hz
      simpa [c, M] using hsphere hY0 hY01 hT (by simpa [c] using hz)
  have hjensen := jensen_inner_zero_multiplicity_le_log_div
    (c := c) (f := regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
    (r := (123 / 32 : ℝ)) (R := (31 / 8 : ℝ)) (K := Real.log M)
    (m := (1 : ℝ)) (by norm_num) (by norm_num) hanalytic one_pos
    hcenter hcircle
  simpa [regularizedTwoScaleCarlsonFactorDiskZeroMass, c, M] using hjensen

/-- The two-scale plateau automatically supplies the quantitative Jensen
center bound, so the local divisor-mass estimate has no remaining far-right
hypothesis. -/
theorem exists_regularizedTwoScaleCarlsonFactorDiskZeroMass_le_logPolynomial_of_two_le_inner :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 2 ≤ Y0 → Y0 < Y1 →
      ∀ {T : ℝ}, 5 ≤ T →
        regularizedTwoScaleCarlsonFactorDiskZeroMass Y0 Y1 T ≤
          Real.log (C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10) /
            Real.log ((31 / 8 : ℝ) / (123 / 32 : ℝ)) := by
  rcases
      exists_regularizedTwoScaleCarlsonFactorDiskZeroMass_le_logPolynomial with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro Y0 Y1 hY0 hY01 T hT
  apply hbound (le_trans (by norm_num) hY0) hY01 hT
  apply norm_twoScaleMollifiedZetaError_le_one_div_three_of_four_le_re
    hY0 hY01
  simp

end CarlsonZeroDensity
end PrimeNumberTheorem
