import PrimeNumberTheorem.CarlsonDetectorCount
import ZeroFreeRegion.PhragmenLindelofZeta

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The fixed Jensen sphere used for Carlson's unit-height rectangles stays in
the strip `0 <= Re(s) <= 8`. -/
theorem fixedJensenSphere_re_mem_Icc
    {T : ℝ} (_hT : 5 ≤ T) {z : ℂ}
    (hz : z ∈ Metric.sphere
      ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ)) :
    z.re ∈ Set.Icc (0 : ℝ) 8 := by
  have hdist :
      ‖z - ((4 : ℂ) + I * (T + 1 / 2))‖ = (31 / 8 : ℝ) := by
    simpa [Metric.mem_sphere, Complex.dist_eq] using hz
  have hreAbs :=
    Complex.abs_re_le_norm (z - ((4 : ℂ) + I * (T + 1 / 2)))
  have hre : |z.re - 4| ≤ (31 / 8 : ℝ) := by
    simpa using hreAbs.trans_eq hdist
  rw [abs_le] at hre
  constructor <;> linarith

/-- At height at least five, the fixed Jensen sphere stays away from the real
axis and has ordinate at most `T + 5`. -/
theorem fixedJensenSphere_abs_im_mem_Icc
    {T : ℝ} (hT : 5 ≤ T) {z : ℂ}
    (hz : z ∈ Metric.sphere
      ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ)) :
    |z.im| ∈ Set.Icc (1 : ℝ) (T + 5) := by
  have hdist :
      ‖z - ((4 : ℂ) + I * (T + 1 / 2))‖ = (31 / 8 : ℝ) := by
    simpa [Metric.mem_sphere, Complex.dist_eq] using hz
  have himAbs :=
    Complex.abs_im_le_norm (z - ((4 : ℂ) + I * (T + 1 / 2)))
  have him : |z.im - (T + 1 / 2)| ≤ (31 / 8 : ℝ) := by
    simpa using himAbs.trans_eq hdist
  rw [abs_le] at him
  have hzImPos : 0 < z.im := by linarith
  rw [abs_of_pos hzImPos]
  constructor <;> linarith

/-- The pole-cancelling factor has polynomial size on the fixed Jensen
sphere. -/
theorem norm_sub_one_le_on_fixedJensenSphere
    {T : ℝ} (hT : 5 ≤ T) {z : ℂ}
    (hz : z ∈ Metric.sphere
      ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ)) :
    ‖z - 1‖ ≤ T + 14 := by
  have hre := fixedJensenSphere_re_mem_Icc hT hz
  have him := fixedJensenSphere_abs_im_mem_Icc hT hz
  have hreSub : |z.re - 1| ≤ 7 := by
    rw [abs_le]
    constructor <;> linarith [hre.1, hre.2]
  calc
    ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| :=
      Complex.norm_le_abs_re_add_abs_im (z - 1)
    _ = |z.re - 1| + |z.im| := by simp
    _ ≤ 7 + (T + 5) := add_le_add hreSub him.2
    _ ≤ T + 14 := by linarith

/-- Uniform polynomial zeta growth on the fixed Carlson--Jensen sphere. -/
theorem exists_norm_riemannZeta_le_fixedJensenSphere :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ {T : ℝ}, 5 ≤ T → ∀ {z : ℂ},
      z ∈ Metric.sphere
        ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ) →
      ‖riemannZeta z‖ ≤ C * (T + 14) ^ 4 := by
  rcases ZeroFreeRegion.exists_norm_riemannZeta_le_polynomial_on_zero_four with
    ⟨C₀, hC₀, hstrip⟩
  let C := max C₀ 2
  refine ⟨C, le_max_right C₀ 2, ?_⟩
  intro T hT z hz
  have hre := fixedJensenSphere_re_mem_Icc hT hz
  have him := fixedJensenSphere_abs_im_mem_Icc hT hz
  have hbase : 1 ≤ T + 14 := by linarith
  have himShift : |z.im| + 3 ≤ T + 14 := by linarith [him.2]
  have himPow : (|z.im| + 3) ^ 4 ≤ (T + 14) ^ 4 :=
    pow_le_pow_left₀ (by positivity) himShift 4
  by_cases hzre : z.re ≤ 4
  · calc
      ‖riemannZeta z‖ ≤ C₀ * (|z.im| + 3) ^ 4 :=
        hstrip z ⟨hre.1, hzre⟩ him.1
      _ ≤ C₀ * (T + 14) ^ 4 :=
        mul_le_mul_of_nonneg_left himPow hC₀
      _ ≤ C * (T + 14) ^ 4 :=
        mul_le_mul_of_nonneg_right (le_max_left C₀ 2)
          (pow_nonneg (by positivity) 4)
  · have hzreOne : 1 ≤ z.re := by linarith
    have hzNorm : ‖z‖ ≤ T + 14 := by
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ = z.re + |z.im| := by rw [abs_of_nonneg hre.1]
        _ ≤ 8 + (T + 5) := add_le_add hre.2 him.2
        _ ≤ T + 14 := by linarith
    have hbasePow : T + 14 ≤ (T + 14) ^ 4 := by
      simpa using pow_le_pow_right₀ hbase (by norm_num : (1 : ℕ) ≤ 4)
    calc
      ‖riemannZeta z‖ ≤ 2 * ‖z‖ :=
        ZeroFreeRegion.norm_riemannZeta_le_two_mul_norm_of_one_le_re_of_one_le_abs_im
          z hzreOne him.1
      _ ≤ 2 * (T + 14) := mul_le_mul_of_nonneg_left hzNorm (by norm_num)
      _ ≤ 2 * (T + 14) ^ 4 :=
        mul_le_mul_of_nonneg_left hbasePow (by norm_num)
      _ ≤ C * (T + 14) ^ 4 :=
        mul_le_mul_of_nonneg_right (le_max_right C₀ 2)
          (pow_nonneg (by positivity) 4)

/-- The regularized Carlson detector has a uniform polynomial bound on the
fixed Jensen sphere.  This is the growth input needed by the local Jensen
zero-counting inequality. -/
theorem exists_norm_regularizedCarlsonZeroDetector_le_fixedJensenSphere :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {X : ℕ}, 1 ≤ X → ∀ {T : ℝ}, 5 ≤ T →
      ∀ {z : ℂ}, z ∈ Metric.sphere
        ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ) →
      ‖regularizedCarlsonZeroDetector X z‖ ≤
        C * (X : ℝ) ^ 2 * (T + 14) ^ 10 := by
  rcases exists_norm_riemannZeta_le_fixedJensenSphere with ⟨C₀, hC₀, hzeta⟩
  refine ⟨2 * C₀ ^ 2, by nlinarith, ?_⟩
  intro X hX T hT z hz
  let U : ℝ := T + 14
  let A : ℝ := C₀ * (X : ℝ) * U ^ 4
  have hU : 1 ≤ U := by dsimp [U]; linarith
  have hXReal : 1 ≤ (X : ℝ) := by exact_mod_cast hX
  have hUPow : 1 ≤ U ^ 4 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hU 4
  have hA : 2 ≤ A := by
    dsimp [A]
    nlinarith [mul_nonneg (show 0 ≤ C₀ by linarith) (show 0 ≤ (X : ℝ) by positivity),
      mul_nonneg (show 0 ≤ C₀ * (X : ℝ) by positivity)
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
  have hmollifier : ‖mobiusMollifier X z‖ ≤ (X : ℝ) :=
    norm_mobiusMollifier_le_natCast hre.1
  have hw : ‖riemannZeta z * mobiusMollifier X z‖ ≤ A := by
    rw [norm_mul]
    have hmul := mul_le_mul (hzeta hT hz) hmollifier
      (norm_nonneg (mobiusMollifier X z))
      (mul_nonneg (show 0 ≤ C₀ by linarith) (pow_nonneg (by positivity) 4))
    simpa [A, U, mul_assoc, mul_left_comm, mul_comm] using hmul
  let w : ℂ := riemannZeta z * mobiusMollifier X z
  have htwoSub : ‖(2 : ℂ) - w‖ ≤ 2 + A := by
    calc
      ‖(2 : ℂ) - w‖ ≤ ‖(2 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ 2 + A := by
        simpa [w] using add_le_add_left hw 2
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
  rw [regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X hz0 hz1,
    carlsonZeroDetector_eq_zeta_mul_mollifier_factorization]
  change ‖(z - 1) ^ 2 * (w * (2 - w))‖ ≤ _
  calc
    ‖(z - 1) ^ 2 * (w * (2 - w))‖ =
        ‖z - 1‖ ^ 2 * ‖w * (2 - w)‖ := by rw [norm_mul, norm_pow]
    _ ≤ U ^ 2 * (2 * A ^ 2) :=
      mul_le_mul hsubPow hdetector (norm_nonneg _) (pow_nonneg (by positivity) 2)
    _ = (2 * C₀ ^ 2) * (X : ℝ) ^ 2 * (T + 14) ^ 10 := by
      dsimp [A, U]
      ring

/-- The fixed-circle growth estimate closes the local Jensen step: detector
zero multiplicity in every unit-height Carlson rectangle is logarithmic in
the polynomial sphere majorant. -/
theorem exists_regularizedCarlsonDetectorRectangleZeroCount_le_logPolynomial :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {X : ℕ}, 1 ≤ X → ∀ {sigma T : ℝ},
      1 / 2 < sigma → 5 ≤ T →
      (regularizedCarlsonDetectorRectangleZeroCount
          X sigma 4 T (T + 1) : ℝ) ≤
        Real.log (C * (X : ℝ) ^ 2 * (T + 14) ^ 10) /
          Real.log ((31 / 8 : ℝ) / (15 / 4 : ℝ)) := by
  rcases exists_norm_regularizedCarlsonZeroDetector_le_fixedJensenSphere with
    ⟨C, hC, hsphere⟩
  refine ⟨C, hC, ?_⟩
  intro X hX sigma T hsigma hT
  have hXReal : 1 ≤ (X : ℝ) := by exact_mod_cast hX
  have hXPow : 1 ≤ (X : ℝ) ^ 2 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hXReal 2
  have hTPow : 1 ≤ (T + 14) ^ 10 := by
    have hTBase : 1 ≤ T + 14 := by linarith
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hTBase 10
  have hCX : 1 ≤ C * (X : ℝ) ^ 2 := by
    simpa using mul_le_mul hC hXPow (by norm_num) (by linarith)
  have hM : 1 ≤ C * (X : ℝ) ^ 2 * (T + 14) ^ 10 := by
    simpa using mul_le_mul hCX hTPow (by norm_num)
      (mul_nonneg (by linarith) (by positivity))
  apply regularizedCarlsonDetectorRectangleZeroCount_le_fixedJensenSphereNorm
    hX hsigma hM
  intro z hz
  exact hsphere hX hT hz

end CarlsonZeroDensity
end PrimeNumberTheorem
