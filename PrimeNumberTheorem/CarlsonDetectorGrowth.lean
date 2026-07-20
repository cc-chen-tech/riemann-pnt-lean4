import PrimeNumberTheorem.CarlsonDetectorCount
import PrimeNumberTheorem.AnalyticBorel
import PrimeNumberTheorem.FiniteZeroGoodRadius
import ZeroFreeRegion.PhragmenLindelofZeta

open Complex MeromorphicOn

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

/-- The logarithmic majorant produced by the fixed Jensen geometry. -/
noncomputable def regularizedCarlsonLocalZeroLogMajorant
    (C : ℝ) (X : ℕ) (T : ℝ) : ℝ :=
  Real.log (C * (X : ℝ) ^ 2 * (T + 14) ^ 10) /
    Real.log ((31 / 8 : ℝ) / (15 / 4 : ℝ))

/-- The local logarithmic count also controls the principal part on a
quantitatively selected horizontal segment. -/
theorem exists_regularizedCarlson_horizontal_principalPart_le_logPolynomial :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {X : ℕ}, 1 ≤ X → ∀ {sigma T : ℝ},
      1 / 2 < sigma → 5 ≤ T →
      ∃ t ∈ Set.Icc T (T + 1),
        (∀ x ∈ Set.Icc sigma 4,
          regularizedCarlsonZeroDetector X
            ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
        ∀ x ∈ Set.Icc sigma 4,
          ‖regularizedCarlsonDetectorRectanglePrincipalPart
            X sigma 4 T (T + 1) ((x : ℂ) + (t : ℂ) * I)‖ ≤
            regularizedCarlsonLocalZeroLogMajorant C X T /
              (1 / ((4 : ℝ) *
                (regularizedCarlsonLocalZeroLogMajorant C X T + 1))) := by
  rcases exists_regularizedCarlsonDetectorRectangleZeroCount_le_logPolynomial with
    ⟨C, hC, hcount⟩
  refine ⟨C, hC, ?_⟩
  intro X hX sigma T hsigma hT
  rcases
      exists_regularizedCarlsonZeroDetector_horizontal_principalPart_le_zeroCount
        hX (by linarith) (sigma := sigma) (alpha := (4 : ℝ)) (T := T) with
    ⟨t, ht, hne, hprincipal⟩
  refine ⟨t, ht, hne, ?_⟩
  intro x hx
  refine (hprincipal x hx).trans ?_
  have hcountBound :
      (regularizedCarlsonDetectorRectangleZeroCount
          X sigma 4 T (T + 1) : ℝ) ≤
        regularizedCarlsonLocalZeroLogMajorant C X T := by
    simpa [regularizedCarlsonLocalZeroLogMajorant] using
      hcount hX hsigma hT
  have hmajorantNonneg :
      0 ≤ regularizedCarlsonLocalZeroLogMajorant C X T :=
    (Nat.cast_nonneg _).trans hcountBound
  simp only [div_eq_mul_inv]
  gcongr

/-- Once the analytic regular part is bounded, the selected horizontal
logarithmic derivative now depends only on the explicit logarithmic local
majorant, rather than an unevaluated rectangle zero count. -/
theorem exists_regularizedCarlson_horizontal_logDeriv_le_regular_add_logPolynomial :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {X : ℕ}, 1 ≤ X → ∀ {sigma T M : ℝ},
      1 / 2 < sigma → 5 ≤ T →
      (∀ t ∈ Set.Icc T (T + 1), ∀ x ∈ Set.Icc sigma 4,
        ‖regularizedCarlsonDetectorRectangleRegularPart
          X sigma 4 T (T + 1) ((x : ℂ) + (t : ℂ) * I)‖ ≤ M) →
      ∃ t ∈ Set.Icc T (T + 1),
        (∀ x ∈ Set.Icc sigma 4,
          regularizedCarlsonZeroDetector X
            ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
        ∀ x ∈ Set.Icc sigma 4,
          ‖logDeriv (regularizedCarlsonZeroDetector X)
            ((x : ℂ) + (t : ℂ) * I)‖ ≤
            M + regularizedCarlsonLocalZeroLogMajorant C X T /
              (1 / ((4 : ℝ) *
                (regularizedCarlsonLocalZeroLogMajorant C X T + 1))) := by
  rcases exists_regularizedCarlsonDetectorRectangleZeroCount_le_logPolynomial with
    ⟨C, hC, hcount⟩
  refine ⟨C, hC, ?_⟩
  intro X hX sigma T M hsigma hT hregular
  rcases
      exists_regularizedCarlsonZeroDetector_horizontal_logDeriv_le_regular_add_zeroCount
        hX (by linarith) hregular with
    ⟨t, ht, hne, hlogDeriv⟩
  refine ⟨t, ht, hne, ?_⟩
  intro x hx
  refine (hlogDeriv x hx).trans ?_
  have hcountBound :
      (regularizedCarlsonDetectorRectangleZeroCount
          X sigma 4 T (T + 1) : ℝ) ≤
        regularizedCarlsonLocalZeroLogMajorant C X T := by
    simpa [regularizedCarlsonLocalZeroLogMajorant] using
      hcount hX hsigma hT
  have hmajorantNonneg :
      0 ≤ regularizedCarlsonLocalZeroLogMajorant C X T :=
    (Nat.cast_nonneg _).trans hcountBound
  simp only [div_eq_mul_inv]
  gcongr

/-- On a slightly smaller factorization disk, all detector zeros can be
removed into an analytic nonvanishing factor whose center value is bounded
below by the local divisor mass. -/
theorem exists_regularizedCarlsonZeroDetector_fixedJensenFactor_center_lower
    {X : ℕ} (hX : 1 ≤ X) {T : ℝ} :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g
        (Metric.closedBall ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) ∧
      (∀ u : (Metric.closedBall
          ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ) : Set ℂ),
        g u ≠ 0) ∧
      -Real.log (123 / 32 : ℝ) *
          (∑ᶠ u,
            (MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
              (Metric.closedBall
                ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) u : ℝ)) ≤
        Real.log ‖g ((4 : ℂ) + I * (T + 1 / 2))‖ := by
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let b : ℝ := 123 / 32
  have hanalytic : AnalyticOnNhd ℂ (regularizedCarlsonZeroDetector X)
      (Metric.closedBall c b) := by
    apply
      (analyticOnNhd_regularizedCarlsonZeroDetector_fixedJensenOuterDisk
        X T).mono
    exact Metric.closedBall_subset_closedBall (by norm_num [b])
  have hcenter : regularizedCarlsonZeroDetector X c ≠ 0 := by
    apply regularizedCarlsonZeroDetector_ne_zero_of_four_le_re hX
    simp [c]
  have hnotop : ∀ u : (Metric.closedBall c b : Set ℂ),
      meromorphicOrderAt (regularizedCarlsonZeroDetector X) u ≠ ⊤ := by
    intro u
    have hdist : ‖(u : ℂ) - c‖ ≤ b := by
      have hdist' : dist (u : ℂ) c ≤ b :=
        Metric.mem_closedBall.mp u.property
      simpa [Complex.dist_eq] using hdist'
    have hreAbs := Complex.abs_re_le_norm ((u : ℂ) - c)
    have hre : 0 < (u : ℂ).re := by
      have : |(u : ℂ).re - 4| ≤ b := by
        simpa [c] using hreAbs.trans hdist
      rw [abs_le] at this
      dsimp [b] at this
      linarith
    rw [(hanalytic u u.property).meromorphicOrderAt_eq]
    intro htop
    apply analyticOrderAt_regularizedCarlsonZeroDetector_ne_top X hX hre
    exact ENat.map_eq_top_iff.mp htop
  rcases exists_analytic_nonzero_factor_log_norm_at_center
      (f := regularizedCarlsonZeroDetector X) (c := c) (R := b)
      (by norm_num [b]) hanalytic hnotop hcenter with
    ⟨g, hg, hgne, hfactor⟩
  have hsum := finsum_divisor_mul_log_norm_center_sub_le_log_mul_mass
    (f := regularizedCarlsonZeroDetector X) (c := c) (b := b)
    (by norm_num [b]) hanalytic hcenter
  have hcenterLog : 0 ≤ Real.log ‖regularizedCarlsonZeroDetector X c‖ :=
    Real.log_nonneg
      (one_le_norm_regularizedCarlsonZeroDetector_of_four_le_re hX (by simp [c]))
  refine ⟨g, by simpa [c, b] using hg, by simpa [c, b] using hgne, ?_⟩
  dsimp [c, b] at hfactor hsum hcenterLog ⊢
  linarith

/-- Jensen majorant for the total detector divisor mass on the factorization
disk of radius `123/32`. -/
noncomputable def regularizedCarlsonFactorZeroLogMajorant
    (C : ℝ) (X : ℕ) (T : ℝ) : ℝ :=
  Real.log (C * (X : ℝ) ^ 2 * (T + 14) ^ 10) /
    Real.log ((31 / 8 : ℝ) / (123 / 32 : ℝ))

/-- Distinct zeros of the regularized detector in the fixed factorization
disk.  Multiplicity is retained separately by the divisor. -/
noncomputable def regularizedCarlsonFactorDiskZeroSupport
    (X : ℕ) (T : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
      (Metric.closedBall
        ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ))).finiteSupport
    (isCompact_closedBall
      ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ))).toFinset

/-- Total analytic zero multiplicity in the fixed factorization disk. -/
noncomputable def regularizedCarlsonFactorDiskZeroMass
    (X : ℕ) (T : ℝ) : ℝ :=
  ∑ᶠ u,
    (MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
      (Metric.closedBall
        ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) u : ℝ)

/-- Imaginary parts of the distinct detector zeros in the fixed
factorization disk. -/
noncomputable def regularizedCarlsonFactorDiskZeroHeights
    (X : ℕ) (T : ℝ) : Finset ℝ :=
  (regularizedCarlsonFactorDiskZeroSupport X T).image Complex.im

/-- Pigeonhole separation available for a horizontal line through a
unit-height Carlson rectangle. -/
noncomputable def regularizedCarlsonFactorHorizontalSeparation
    (X : ℕ) (T : ℝ) : ℝ :=
  1 / (4 * (((regularizedCarlsonFactorDiskZeroHeights X T).card : ℝ) + 1))

/-- Quantitative separation supplied by the fixed good-circle interval. -/
noncomputable def regularizedCarlsonFactorDiskSeparation
    (X : ℕ) (T : ℝ) : ℝ :=
  ((122 / 32 : ℝ) - 121 / 32) /
    (4 * ((((regularizedCarlsonFactorDiskZeroSupport X T).image
      (dist ((4 : ℂ) + I * (T + 1 / 2)))).card : ℝ) + 1))

/-- Logarithmic norm majorant for the extracted nonzero factor on its selected
good circle. -/
noncomputable def regularizedCarlsonFactorCircleLogUpper
    (C : ℝ) (X : ℕ) (T : ℝ) : ℝ :=
  Real.log (C * (X : ℝ) ^ 2 * (T + 14) ^ 10) -
    Real.log (regularizedCarlsonFactorDiskSeparation X T) *
      regularizedCarlsonFactorDiskZeroMass X T

/-- Center lower bound for the same extracted nonzero factor. -/
noncomputable def regularizedCarlsonFactorCenterLogLower
    (X : ℕ) (T : ℝ) : ℝ :=
  -Real.log (123 / 32 : ℝ) *
    regularizedCarlsonFactorDiskZeroMass X T

/-- An explicit upper bound for the logarithmic variation of the extracted
factor, assuming `L` bounds the complete divisor mass in the factorization
disk. -/
noncomputable def regularizedCarlsonFactorLogVariationMajorant
    (C : ℝ) (X : ℕ) (T L : ℝ) : ℝ :=
  Real.log (C * (X : ℝ) ^ 2 * (T + 14) ^ 10) +
    (-Real.log (1 / (128 * (L + 1))) + Real.log (123 / 32 : ℝ)) * L

private theorem fixedJensenFactorDisk_re_pos
    {T : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall
      ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) :
    0 < z.re := by
  have hdist :
      ‖z - ((4 : ℂ) + I * (T + 1 / 2))‖ ≤ (123 / 32 : ℝ) := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
  have hreAbs :=
    Complex.abs_re_le_norm (z - ((4 : ℂ) + I * (T + 1 / 2)))
  have hre : |z.re - 4| ≤ (123 / 32 : ℝ) := by
    simpa using hreAbs.trans hdist
  rw [abs_le] at hre
  linarith

private theorem fixedJensenFactorDisk_meromorphicOrder_ne_top
    {X : ℕ} (hX : 1 ≤ X) {T : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall
      ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) :
    meromorphicOrderAt (regularizedCarlsonZeroDetector X) z ≠ ⊤ := by
  have hanalytic : AnalyticAt ℂ (regularizedCarlsonZeroDetector X) z := by
    exact analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X z (fixedJensenFactorDisk_re_pos hz)
  rw [hanalytic.meromorphicOrderAt_eq]
  intro htop
  apply analyticOrderAt_regularizedCarlsonZeroDetector_ne_top X hX
    (fixedJensenFactorDisk_re_pos hz)
  exact ENat.map_eq_top_iff.mp htop

/-- On the factorization disk, the finite divisor support is exactly the
zero set of the regularized Carlson detector. -/
theorem mem_regularizedCarlsonFactorDiskZeroSupport_iff_zero
    {X : ℕ} (hX : 1 ≤ X) {T : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall
      ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) :
    z ∈ regularizedCarlsonFactorDiskZeroSupport X T ↔
      regularizedCarlsonZeroDetector X z = 0 := by
  classical
  let U : Set ℂ := Metric.closedBall
    ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X) U
  have hanalytic : AnalyticOnNhd ℂ (regularizedCarlsonZeroDetector X) U := by
    apply
      (analyticOnNhd_regularizedCarlsonZeroDetector_fixedJensenOuterDisk
        X T).mono
    exact Metric.closedBall_subset_closedBall (by norm_num [U])
  have hzre : 0 < z.re := fixedJensenFactorDisk_re_pos hz
  have horder : analyticOrderAt (regularizedCarlsonZeroDetector X) z ≠ ⊤ :=
    analyticOrderAt_regularizedCarlsonZeroDetector_ne_top X hX hzre
  have hdivisor : D z =
      (analyticOrderNatAt (regularizedCarlsonZeroDetector X) z : ℤ) := by
    rw [MeromorphicOn.divisor_apply hanalytic.meromorphicOn (by simpa [U] using hz),
      (hanalytic z (by simpa [U] using hz)).meromorphicOrderAt_eq]
    have hcast := Nat.cast_analyticOrderNatAt horder
    rw [← hcast]
    simp
  have hz_analytic : AnalyticAt ℂ (regularizedCarlsonZeroDetector X) z :=
    hanalytic z (by simpa [U] using hz)
  have hnatCast := Nat.cast_analyticOrderNatAt horder
  rw [regularizedCarlsonFactorDiskZeroSupport]
  rw [(D.finiteSupport (isCompact_closedBall
    ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ))).mem_toFinset]
  simp only [Function.mem_support]
  rw [show MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
      (Metric.closedBall
        ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) z = D z by rfl,
    hdivisor, Int.ofNat_ne_zero]
  constructor
  · intro hnat
    apply hz_analytic.analyticOrderAt_ne_zero.mp
    intro hzero
    have hcastZero :
        (analyticOrderNatAt (regularizedCarlsonZeroDetector X) z : ℕ∞) = 0 :=
      hnatCast.trans hzero
    exact hnat (by simpa using hcastZero)
  · intro hzero hnatZero
    have horderZero :
        analyticOrderAt (regularizedCarlsonZeroDetector X) z = 0 := by
      rw [← hnatCast, hnatZero]
      rfl
    exact (hz_analytic.analyticOrderAt_eq_zero.mp horderZero) hzero

/-- Any upper bound for the total divisor mass gives a concrete lower bound
for the good-circle separation scale. -/
theorem regularizedCarlsonFactorDiskSeparation_lower_of_mass_le
    {X : ℕ} {T L : ℝ}
    (hmass : regularizedCarlsonFactorDiskZeroMass X T ≤ L) :
    0 < 1 / (128 * (L + 1)) ∧
      1 / (128 * (L + 1)) ≤
        regularizedCarlsonFactorDiskSeparation X T := by
  classical
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let b : ℝ := 123 / 32
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
    (Metric.closedBall c b)
  let zeros := regularizedCarlsonFactorDiskZeroSupport X T
  let radialCard : ℝ :=
    (((zeros.image (dist c)).card : ℕ) : ℝ)
  have hanalyticFactor : AnalyticOnNhd ℂ
      (regularizedCarlsonZeroDetector X) (Metric.closedBall c b) := by
    apply
      (analyticOnNhd_regularizedCarlsonZeroDetector_fixedJensenOuterDisk
        X T).mono
    exact Metric.closedBall_subset_closedBall (by norm_num [b])
  have hDnonneg : 0 ≤ D := hanalyticFactor.divisor_nonneg
  have hmassNonneg : 0 ≤ regularizedCarlsonFactorDiskZeroMass X T := by
    change 0 ≤ ∑ᶠ u, (D u : ℝ)
    apply finsum_nonneg
    intro u
    exact_mod_cast hDnonneg u
  have hLnonneg : 0 ≤ L := hmassNonneg.trans hmass
  have hsupportMass : (zeros.card : ℝ) ≤
      regularizedCarlsonFactorDiskZeroMass X T := by
    have h := card_divisor_support_le_finsum_mass hanalyticFactor
    simpa [zeros, D, c, b, regularizedCarlsonFactorDiskZeroSupport,
      regularizedCarlsonFactorDiskZeroMass] using h
  have hradialNat : (zeros.image (dist c)).card ≤ zeros.card :=
    Finset.card_image_le
  have hradialSupport : radialCard ≤ (zeros.card : ℝ) := by
    dsimp [radialCard]
    exact_mod_cast hradialNat
  have hradialL : radialCard ≤ L :=
    hradialSupport.trans (hsupportMass.trans hmass)
  have hsmallDenPos : 0 < 128 * (radialCard + 1) := by positivity
  have hlargeDenPos : 0 < 128 * (L + 1) := by positivity
  have hdenLe : 128 * (radialCard + 1) ≤ 128 * (L + 1) := by
    nlinarith
  have hrecip : 1 / (128 * (L + 1)) ≤
      1 / (128 * (radialCard + 1)) :=
    one_div_le_one_div_of_le hsmallDenPos hdenLe
  have hsepEq : regularizedCarlsonFactorDiskSeparation X T =
      1 / (128 * (radialCard + 1)) := by
    dsimp only [regularizedCarlsonFactorDiskSeparation, zeros, c]
    change ((122 / 32 : ℝ) - 121 / 32) /
        (4 * (radialCard + 1)) = 1 / (128 * (radialCard + 1))
    have hk : radialCard + 1 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hk]
    ring
  refine ⟨one_div_pos.mpr hlargeDenPos, ?_⟩
  rw [hsepEq]
  exact hrecip

/-- A divisor-mass bound also controls the pigeonhole separation for the
horizontal side, because the number of distinct zero heights is no larger
than the total zero multiplicity. -/
theorem regularizedCarlsonFactorHorizontalSeparation_lower_of_mass_le
    {X : ℕ} {T L : ℝ}
    (hmass : regularizedCarlsonFactorDiskZeroMass X T ≤ L) :
    0 < 1 / (4 * (L + 1)) ∧
      1 / (4 * (L + 1)) ≤
        regularizedCarlsonFactorHorizontalSeparation X T := by
  classical
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let b : ℝ := 123 / 32
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
    (Metric.closedBall c b)
  let zeros := regularizedCarlsonFactorDiskZeroSupport X T
  let heights := regularizedCarlsonFactorDiskZeroHeights X T
  have hanalyticFactor : AnalyticOnNhd ℂ
      (regularizedCarlsonZeroDetector X) (Metric.closedBall c b) := by
    apply
      (analyticOnNhd_regularizedCarlsonZeroDetector_fixedJensenOuterDisk
        X T).mono
    exact Metric.closedBall_subset_closedBall (by norm_num [b])
  have hDnonneg : 0 ≤ D := hanalyticFactor.divisor_nonneg
  have hmassNonneg : 0 ≤ regularizedCarlsonFactorDiskZeroMass X T := by
    change 0 ≤ ∑ᶠ u, (D u : ℝ)
    apply finsum_nonneg
    intro u
    exact_mod_cast hDnonneg u
  have hLnonneg : 0 ≤ L := hmassNonneg.trans hmass
  have hsupportMass : (zeros.card : ℝ) ≤
      regularizedCarlsonFactorDiskZeroMass X T := by
    have h := card_divisor_support_le_finsum_mass hanalyticFactor
    simpa [zeros, D, c, b, regularizedCarlsonFactorDiskZeroSupport,
      regularizedCarlsonFactorDiskZeroMass] using h
  have hheightNat : heights.card ≤ zeros.card := by
    dsimp [heights, regularizedCarlsonFactorDiskZeroHeights]
    exact Finset.card_image_le
  have hheightMass : (heights.card : ℝ) ≤
      regularizedCarlsonFactorDiskZeroMass X T := by
    have hheightReal : (heights.card : ℝ) ≤ (zeros.card : ℝ) := by
      exact_mod_cast hheightNat
    exact hheightReal.trans hsupportMass
  have hheightL : (heights.card : ℝ) ≤ L :=
    hheightMass.trans hmass
  have hsmallDenPos : 0 < 4 * ((heights.card : ℝ) + 1) := by positivity
  have hlargeDenPos : 0 < 4 * (L + 1) := by positivity
  have hdenLe : 4 * ((heights.card : ℝ) + 1) ≤ 4 * (L + 1) := by
    nlinarith
  have hrecip : 1 / (4 * (L + 1)) ≤
      1 / (4 * ((heights.card : ℝ) + 1)) :=
    one_div_le_one_div_of_le hsmallDenPos hdenLe
  refine ⟨one_div_pos.mpr hlargeDenPos, ?_⟩
  simpa [regularizedCarlsonFactorHorizontalSeparation, heights] using hrecip

/-- Replacing the actual divisor mass and good-circle separation by a common
mass majorant gives a fully explicit logarithmic-variation bound. -/
theorem regularizedCarlsonFactorLogVariation_le_of_mass_le
    {C T L : ℝ} {X : ℕ}
    (hmass : regularizedCarlsonFactorDiskZeroMass X T ≤ L) :
    regularizedCarlsonFactorCircleLogUpper C X T -
        regularizedCarlsonFactorCenterLogLower X T ≤
      regularizedCarlsonFactorLogVariationMajorant C X T L := by
  let m := regularizedCarlsonFactorDiskZeroMass X T
  let sep := regularizedCarlsonFactorDiskSeparation X T
  let delta : ℝ := 1 / (128 * (L + 1))
  have hsep := regularizedCarlsonFactorDiskSeparation_lower_of_mass_le hmass
  have hmNonneg : 0 ≤ m := by
    let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
    let b : ℝ := 123 / 32
    let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
      (Metric.closedBall c b)
    have hanalyticFactor : AnalyticOnNhd ℂ
        (regularizedCarlsonZeroDetector X) (Metric.closedBall c b) := by
      apply
        (analyticOnNhd_regularizedCarlsonZeroDetector_fixedJensenOuterDisk
          X T).mono
      exact Metric.closedBall_subset_closedBall (by norm_num [b])
    have hDnonneg : 0 ≤ D := hanalyticFactor.divisor_nonneg
    change 0 ≤ ∑ᶠ u, (D u : ℝ)
    apply finsum_nonneg
    intro u
    exact_mod_cast hDnonneg u
  have hLNonneg : 0 ≤ L := hmNonneg.trans hmass
  have hdeltaPos : 0 < delta := by simpa [delta] using hsep.1
  have hdeltaSep : delta ≤ sep := by simpa [delta, sep] using hsep.2
  have hlogDeltaSep : Real.log delta ≤ Real.log sep :=
    Real.log_le_log hdeltaPos hdeltaSep
  have hdeltaLeOne : delta ≤ 1 := by
    dsimp [delta]
    have hden : 1 ≤ 128 * (L + 1) := by nlinarith
    calc
      1 / (128 * (L + 1)) ≤ 1 / 1 :=
        one_div_le_one_div_of_le (by norm_num) hden
      _ = 1 := by norm_num
  have hlogDeltaNonpos : Real.log delta ≤ 0 :=
    Real.log_nonpos hdeltaPos.le hdeltaLeOne
  have hlogBNonneg : 0 ≤ Real.log (123 / 32 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hcoeffLe :
      -Real.log sep + Real.log (123 / 32 : ℝ) ≤
        -Real.log delta + Real.log (123 / 32 : ℝ) := by
    linarith
  have hcoeffNonneg :
      0 ≤ -Real.log delta + Real.log (123 / 32 : ℝ) := by
    linarith
  have hweighted :
      (-Real.log sep + Real.log (123 / 32 : ℝ)) * m ≤
        (-Real.log delta + Real.log (123 / 32 : ℝ)) * L := by
    exact (mul_le_mul_of_nonneg_right hcoeffLe hmNonneg).trans
      (mul_le_mul_of_nonneg_left hmass hcoeffNonneg)
  dsimp [regularizedCarlsonFactorCircleLogUpper,
    regularizedCarlsonFactorCenterLogLower,
    regularizedCarlsonFactorLogVariationMajorant, m, sep, delta]
  linarith

/-- A circle strictly inside the factorization disk avoids every detector
zero there, with a quantitative separation from its finite zero support. -/
theorem exists_regularizedCarlsonZeroDetector_goodFactorCircle
    {X : ℕ} (hX : 1 ≤ X) {T : ℝ} :
    ∃ r : ℝ,
      0 < r ∧ r ∈ Set.Icc (121 / 32 : ℝ) (122 / 32 : ℝ) ∧
      (∀ z ∈ Metric.sphere
          ((4 : ℂ) + I * (T + 1 / 2)) r,
        ∀ rho ∈ regularizedCarlsonFactorDiskZeroSupport X T,
          ((122 / 32 : ℝ) - 121 / 32) /
              (4 * ((((regularizedCarlsonFactorDiskZeroSupport X T).image
                (dist ((4 : ℂ) + I * (T + 1 / 2)))).card : ℝ) + 1)) ≤
            dist z rho) ∧
      (∀ z ∈ Metric.sphere
          ((4 : ℂ) + I * (T + 1 / 2)) r,
        z ∈ Metric.closedBall
          ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) ∧
      ∀ z ∈ Metric.sphere
          ((4 : ℂ) + I * (T + 1 / 2)) r,
        regularizedCarlsonZeroDetector X z ≠ 0 := by
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let zeros := regularizedCarlsonFactorDiskZeroSupport X T
  have hcover : ∀ z ∈ Metric.closedBall c (123 / 32 : ℝ),
      regularizedCarlsonZeroDetector X z = 0 → z ∈ zeros := by
    intro z hz hzero
    exact (mem_regularizedCarlsonFactorDiskZeroSupport_iff_zero hX
      (by simpa [c] using hz)).2 hzero
  simpa [c, zeros] using
    (PrimeNumberTheorem.exists_good_radius_avoiding_covered_finset_zeros
      (f := regularizedCarlsonZeroDetector X) zeros c
      (by norm_num : (0 : ℝ) < 121 / 32)
      (by norm_num : (121 / 32 : ℝ) < 122 / 32)
      (by norm_num : (122 / 32 : ℝ) < 123 / 32) hcover)

/-- One zero-avoiding circle and one extracted factor simultaneously carry
the center lower bound, boundary logarithmic growth, and a logarithmic-
derivative bound throughout the disk containing Carlson's unit rectangle. -/
theorem exists_regularizedCarlsonZeroDetector_goodFactor_logDeriv_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {X : ℕ}, 1 ≤ X → ∀ {T : ℝ}, 5 ≤ T →
      ∃ r : ℝ, ∃ g : ℂ → ℂ,
        r ∈ Set.Icc (121 / 32 : ℝ) (122 / 32 : ℝ) ∧
        AnalyticOnNhd ℂ g
          (Metric.closedBall
            ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) ∧
        (∀ u : (Metric.closedBall
            ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ) : Set ℂ),
          g u ≠ 0) ∧
        regularizedCarlsonFactorCenterLogLower X T ≤
          Real.log ‖g ((4 : ℂ) + I * (T + 1 / 2))‖ ∧
        (∀ z ∈ Metric.sphere
            ((4 : ℂ) + I * (T + 1 / 2)) r,
          Real.log ‖g z‖ ≤
            regularizedCarlsonFactorCircleLogUpper C X T) ∧
        (∀ z ∈ Metric.ball
            ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ),
          regularizedCarlsonZeroDetector X z ≠ 0 →
            logDeriv (regularizedCarlsonZeroDetector X) z =
              (∑ᶠ u,
                (MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
                  (Metric.closedBall
                    ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) u : ℂ) *
                  (z - u)⁻¹) + logDeriv g z) ∧
        ∀ z ∈ Metric.closedBall
            ((4 : ℂ) + I * (T + 1 / 2)) (15 / 4 : ℝ),
          ‖logDeriv g z‖ ≤
            4 * max
                (regularizedCarlsonFactorCircleLogUpper C X T -
                  regularizedCarlsonFactorCenterLogLower X T) 1 *
              (r + 15 / 4) / (r - 15 / 4) ^ 2 := by
  rcases exists_norm_regularizedCarlsonZeroDetector_le_fixedJensenSphere with
    ⟨C, hC, hsphereOuter⟩
  refine ⟨C, hC, ?_⟩
  intro X hX T hT
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let b : ℝ := 123 / 32
  let R : ℝ := 31 / 8
  let M : ℝ := C * (X : ℝ) ^ 2 * (T + 14) ^ 10
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
    (Metric.closedBall c b)
  let zeros := regularizedCarlsonFactorDiskZeroSupport X T
  let delta := regularizedCarlsonFactorDiskSeparation X T
  have hXReal : 1 ≤ (X : ℝ) := by exact_mod_cast hX
  have hXPow : 1 ≤ (X : ℝ) ^ 2 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hXReal 2
  have hTBase : 1 ≤ T + 14 := by linarith
  have hTPow : 1 ≤ (T + 14) ^ 10 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hTBase 10
  have hCX : 1 ≤ C * (X : ℝ) ^ 2 := by
    simpa using mul_le_mul hC hXPow (by norm_num) (by linarith)
  have hM : 1 ≤ M := by
    dsimp [M]
    simpa using mul_le_mul hCX hTPow (by norm_num)
      (mul_nonneg (by linarith) (by positivity))
  have hanalyticOuter : AnalyticOnNhd ℂ
      (regularizedCarlsonZeroDetector X) (Metric.closedBall c R) := by
    simpa [c, R] using
      analyticOnNhd_regularizedCarlsonZeroDetector_fixedJensenOuterDisk X T
  have hdiffOuter : DiffContOnCl ℂ (regularizedCarlsonZeroDetector X)
      (Metric.ball c R) :=
    hanalyticOuter.differentiableOn.diffContOnCl_ball subset_rfl
  have hclosedNorm : ∀ z ∈ Metric.closedBall c R,
      ‖regularizedCarlsonZeroDetector X z‖ ≤ M := by
    intro z hz
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball hdiffOuter
    · intro u hu
      have huSphere : u ∈ Metric.sphere c R :=
        Metric.frontier_ball_subset_sphere hu
      simpa [c, R, M] using hsphereOuter hX hT (by simpa [c, R] using huSphere)
    · rw [closure_ball c (by norm_num [R] : R ≠ 0)]
      exact hz
  rcases exists_regularizedCarlsonZeroDetector_goodFactorCircle hX (T := T) with
    ⟨r, hrpos, hrange, hsep, hsphereFactor, hsphereNe⟩
  have hrb : r < b := by
    dsimp [b]
    linarith [hrange.2]
  have hbR : b ≤ R := by norm_num [b, R]
  have hanalyticFactor : AnalyticOnNhd ℂ
      (regularizedCarlsonZeroDetector X) (Metric.closedBall c b) :=
    hanalyticOuter.mono (Metric.closedBall_subset_closedBall hbR)
  have hnotop : ∀ u : (Metric.closedBall c b : Set ℂ),
      meromorphicOrderAt (regularizedCarlsonZeroDetector X) u ≠ ⊤ := by
    intro u
    apply fixedJensenFactorDisk_meromorphicOrder_ne_top hX
    change (u : ℂ) ∈ Metric.closedBall
      ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)
    exact u.property
  rcases
      exists_analytic_nonzero_factor_log_norm_logDeriv_pointwise_of_ne_zero
      (f := regularizedCarlsonZeroDetector X) (c := c) (r := r) (R := b)
      hrb hanalyticFactor hnotop with ⟨g, hg, hgne, hfactor, hld⟩
  have hDfinite : D.support.Finite := by
    exact D.finiteSupport (isCompact_closedBall c b)
  have hDnonneg : 0 ≤ D := hanalyticFactor.divisor_nonneg
  have hcenterNe : regularizedCarlsonZeroDetector X c ≠ 0 := by
    apply regularizedCarlsonZeroDetector_ne_zero_of_four_le_re hX
    simp [c]
  have hcenterEq := hfactor c (by simp [hrpos.le]) hcenterNe
  have hcenterSum :=
    finsum_divisor_mul_log_norm_center_sub_le_log_mul_mass
      (f := regularizedCarlsonZeroDetector X) (c := c) (b := b)
      (by norm_num [b]) hanalyticFactor hcenterNe
  have hcenterF : 0 ≤ Real.log ‖regularizedCarlsonZeroDetector X c‖ :=
    Real.log_nonneg
      (one_le_norm_regularizedCarlsonZeroDetector_of_four_le_re hX (by simp [c]))
  have hcenterG : regularizedCarlsonFactorCenterLogLower X T ≤
      Real.log ‖g c‖ := by
    change -Real.log b * (∑ᶠ u, (D u : ℝ)) ≤ Real.log ‖g c‖
    simpa [D, c, b] using (show
      -Real.log b * (∑ᶠ u, (D u : ℝ)) ≤ Real.log ‖g c‖ by
        linarith)
  have hdelta : 0 < delta := by
    dsimp [delta, regularizedCarlsonFactorDiskSeparation, zeros, c]
    positivity
  have hsphereG : ∀ z ∈ Metric.sphere c r,
      Real.log ‖g z‖ ≤ regularizedCarlsonFactorCircleLogUpper C X T := by
    intro z hz
    have hzFactor : z ∈ Metric.closedBall c b := hsphereFactor z (by simpa [c] using hz)
    have hzOuter : z ∈ Metric.closedBall c R :=
      Metric.closedBall_subset_closedBall hbR hzFactor
    have hfz : regularizedCarlsonZeroDetector X z ≠ 0 :=
      hsphereNe z (by simpa [c] using hz)
    have hfactorZ := hfactor z
      (Metric.sphere_subset_closedBall (by simpa [c] using hz)) hfz
    have hsepSupport : ∀ u ∈ D.support, delta ≤ ‖z - u‖ := by
      intro u hu
      have huZeros : u ∈ zeros := by
        dsimp [zeros, regularizedCarlsonFactorDiskZeroSupport]
        exact hDfinite.mem_toFinset.mpr hu
      have h := hsep z (by simpa [c] using hz) u (by simpa [zeros] using huZeros)
      simpa [delta, regularizedCarlsonFactorDiskSeparation, c,
        Complex.dist_eq] using h
    have hsumLower :=
      ZeroFreeRegion.log_mul_finsum_le_finsum_mul_log_norm_sub_of_finiteSupport
        hDfinite (fun u => hDnonneg u) hdelta hsepSupport
    have hlogF : Real.log ‖regularizedCarlsonZeroDetector X z‖ ≤ Real.log M :=
      Real.log_le_log (norm_pos_iff.mpr hfz) (hclosedNorm z hzOuter)
    change Real.log ‖g z‖ ≤
      Real.log M - Real.log delta * (∑ᶠ u, (D u : ℝ))
    simpa [D, c, M, delta, regularizedCarlsonFactorCircleLogUpper,
      regularizedCarlsonFactorDiskZeroMass] using (show
        Real.log ‖g z‖ ≤
          Real.log M - Real.log delta * (∑ᶠ u, (D u : ℝ)) by
      linarith)
  have hgCircle : AnalyticOnNhd ℂ g (Metric.closedBall c r) :=
    hg.mono (Metric.closedBall_subset_closedBall hrb.le)
  have hgneCircle : ∀ z ∈ Metric.closedBall c r, g z ≠ 0 := by
    intro z hz
    exact hgne ⟨z, Metric.closedBall_subset_closedBall hrb.le hz⟩
  have hdR : (15 / 4 : ℝ) < r := by linarith [hrange.1]
  have hlogDeriv : ∀ z ∈ Metric.closedBall c (15 / 4 : ℝ),
      ‖logDeriv g z‖ ≤
        4 * max
            (regularizedCarlsonFactorCircleLogUpper C X T -
              regularizedCarlsonFactorCenterLogLower X T) 1 *
          (r + 15 / 4) / (r - 15 / 4) ^ 2 := by
    intro z hz
    exact
      ZeroFreeRegion.norm_logDeriv_le_four_mul_max_sub_mul_add_div_sq_of_sphere_log_norm_le_of_center_lower
        hrpos (by norm_num) hdR hgCircle hgneCircle hcenterG hsphereG hz
  refine ⟨r, g, hrange, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [c, b] using hg
  · simpa [c, b] using hgne
  · simpa [c] using hcenterG
  · intro z hz
    exact hsphereG z (by simpa [c] using hz)
  · intro z hz hfz
    exact hld z (by simpa [c, b] using hz) hfz
  · intro z hz
    exact hlogDeriv z (by simpa [c] using hz)

/-- One horizontal side of the unit Carlson rectangle avoids every zero in
the fixed factorization disk.  On that side, the detector's logarithmic
derivative is bounded by the extracted analytic factor plus the complete
local divisor mass divided by the pigeonhole separation. -/
theorem exists_regularizedCarlson_horizontal_logDeriv_le_factorDisk :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {X : ℕ}, 1 ≤ X →
      ∀ {sigma T : ℝ}, 1 / 2 < sigma → 5 ≤ T →
        ∃ r ∈ Set.Icc (121 / 32 : ℝ) (122 / 32 : ℝ),
        ∃ t ∈ Set.Icc T (T + 1),
          (∀ x ∈ Set.Icc sigma 4,
            regularizedCarlsonZeroDetector X
              ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
          ∀ x ∈ Set.Icc sigma 4,
            ‖logDeriv (regularizedCarlsonZeroDetector X)
              ((x : ℂ) + (t : ℂ) * I)‖ ≤
              4 * max
                  (regularizedCarlsonFactorCircleLogUpper C X T -
                    regularizedCarlsonFactorCenterLogLower X T) 1 *
                (r + 15 / 4) / (r - 15 / 4) ^ 2 +
              regularizedCarlsonFactorDiskZeroMass X T /
                regularizedCarlsonFactorHorizontalSeparation X T := by
  classical
  rcases exists_regularizedCarlsonZeroDetector_goodFactor_logDeriv_le with
    ⟨C, hC, hfactor⟩
  refine ⟨C, hC, ?_⟩
  intro X hX sigma T hsigma hT
  rcases hfactor hX hT with
    ⟨r, g, hr, hg, hgne, hcenter, hsphere, hdecomp, hgBound⟩
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let U : Set ℂ := Metric.closedBall c (123 / 32 : ℝ)
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X) U
  let H := regularizedCarlsonFactorDiskZeroHeights X T
  let delta := regularizedCarlsonFactorHorizontalSeparation X T
  rcases ZeroFreeRegion.exists_radius_separated_from_finset H
      (show T < T + 1 by linarith) with ⟨t, ht, hsep⟩
  have hdelta : 0 < delta := by
    dsimp [delta, regularizedCarlsonFactorHorizontalSeparation]
    positivity
  have hanalyticFactor : AnalyticOnNhd ℂ
      (regularizedCarlsonZeroDetector X) U := by
    simpa [U, c] using
      (analyticOnNhd_regularizedCarlsonZeroDetector_fixedJensenOuterDisk X T).mono
        (Metric.closedBall_subset_closedBall (by norm_num))
  have hDfinite : D.support.Finite := by
    exact D.finiteSupport (by simpa [U] using isCompact_closedBall c (123 / 32 : ℝ))
  have hDnonneg : 0 ≤ D := hanalyticFactor.divisor_nonneg
  refine ⟨r, hr, t, ht, ?_, ?_⟩
  · intro x hx
    let z : ℂ := (x : ℂ) + (t : ℂ) * I
    have hzRectangle : z ∈ carlsonDetectorRectangle sigma 4 T (T + 1) := by
      change z.re ∈ Set.Icc sigma 4 ∧ z.im ∈ Set.Icc T (T + 1)
      constructor
      · simpa [z] using hx
      · simpa [z] using ht
    have hzInner : z ∈ Metric.closedBall c (15 / 4 : ℝ) := by
      simpa [c] using
        (carlsonDetectorRectangle_subset_fixedJensenInnerDisk hsigma hzRectangle)
    have hzFactor : z ∈ U := by
      dsimp [U]
      exact Metric.closedBall_subset_closedBall (by norm_num) hzInner
    intro hzero
    have hzSupport : z ∈ regularizedCarlsonFactorDiskZeroSupport X T :=
      (mem_regularizedCarlsonFactorDiskZeroSupport_iff_zero hX
        (by simpa [U, c] using hzFactor)).2 hzero
    have hzHeight : z.im ∈ H := by
      dsimp [H, regularizedCarlsonFactorDiskZeroHeights]
      exact Finset.mem_image.mpr ⟨z, hzSupport, rfl⟩
    have hzeroDistance : delta ≤ 0 := by
      simpa [z, delta, regularizedCarlsonFactorHorizontalSeparation, H] using
        hsep z.im hzHeight
    exact (not_lt_of_ge hzeroDistance) hdelta
  · intro x hx
    let z : ℂ := (x : ℂ) + (t : ℂ) * I
    have hzRectangle : z ∈ carlsonDetectorRectangle sigma 4 T (T + 1) := by
      change z.re ∈ Set.Icc sigma 4 ∧ z.im ∈ Set.Icc T (T + 1)
      constructor
      · simpa [z] using hx
      · simpa [z] using ht
    have hzInner : z ∈ Metric.closedBall c (15 / 4 : ℝ) := by
      simpa [c] using
        (carlsonDetectorRectangle_subset_fixedJensenInnerDisk hsigma hzRectangle)
    have hzFactor : z ∈ U := by
      dsimp [U]
      exact Metric.closedBall_subset_closedBall (by norm_num) hzInner
    have hzFactorBall : z ∈ Metric.ball c (123 / 32 : ℝ) :=
      Metric.closedBall_subset_ball (by norm_num) hzInner
    have hzNe : regularizedCarlsonZeroDetector X z ≠ 0 := by
      intro hzero
      have hzSupport : z ∈ regularizedCarlsonFactorDiskZeroSupport X T :=
        (mem_regularizedCarlsonFactorDiskZeroSupport_iff_zero hX
          (by simpa [U, c] using hzFactor)).2 hzero
      have hzHeight : z.im ∈ H := by
        dsimp [H, regularizedCarlsonFactorDiskZeroHeights]
        exact Finset.mem_image.mpr ⟨z, hzSupport, rfl⟩
      have hzeroDistance : delta ≤ 0 := by
        simpa [z, delta, regularizedCarlsonFactorHorizontalSeparation, H] using
          hsep z.im hzHeight
      exact (not_lt_of_ge hzeroDistance) hdelta
    have hprincipal :
        ‖∑ᶠ u, (D u : ℂ) * (z - u)⁻¹‖ ≤
          regularizedCarlsonFactorDiskZeroMass X T / delta := by
      have hbound := ZeroFreeRegion.norm_finsum_divisor_mul_inv_le_mass_div
        hDfinite (fun u => hDnonneg u) hdelta (by
          intro u hu
          have huSupport : u ∈ regularizedCarlsonFactorDiskZeroSupport X T := by
            dsimp [regularizedCarlsonFactorDiskZeroSupport]
            exact hDfinite.mem_toFinset.mpr hu
          have huHeight : u.im ∈ H := by
            dsimp [H, regularizedCarlsonFactorDiskZeroHeights]
            exact Finset.mem_image.mpr ⟨u, huSupport, rfl⟩
          have hheight : delta ≤ |t - u.im| := by
            simpa [delta, regularizedCarlsonFactorHorizontalSeparation, H] using
              hsep u.im huHeight
          have him : |(z - u).im| ≤ ‖z - u‖ := Complex.abs_im_le_norm (z - u)
          have hrewrite : |(z - u).im| = |t - u.im| := by simp [z]
          rw [hrewrite] at him
          exact hheight.trans him)
      simpa [D, U, c, regularizedCarlsonFactorDiskZeroMass] using hbound
    have hsplit := hdecomp z (by simpa [c] using hzFactorBall) hzNe
    have hgAt := hgBound z (by simpa [c] using hzInner)
    rw [show logDeriv (regularizedCarlsonZeroDetector X) z =
        (∑ᶠ u, (D u : ℂ) * (z - u)⁻¹) + logDeriv g z by
      simpa [D, U, c] using hsplit]
    calc
      ‖(∑ᶠ u, (D u : ℂ) * (z - u)⁻¹) + logDeriv g z‖ ≤
          ‖∑ᶠ u, (D u : ℂ) * (z - u)⁻¹‖ + ‖logDeriv g z‖ :=
        norm_add_le _ _
      _ ≤ regularizedCarlsonFactorDiskZeroMass X T / delta +
          4 * max
              (regularizedCarlsonFactorCircleLogUpper C X T -
                regularizedCarlsonFactorCenterLogLower X T) 1 *
            (r + 15 / 4) / (r - 15 / 4) ^ 2 :=
        add_le_add hprincipal hgAt
      _ = 4 * max
              (regularizedCarlsonFactorCircleLogUpper C X T -
                regularizedCarlsonFactorCenterLogLower X T) 1 *
            (r + 15 / 4) / (r - 15 / 4) ^ 2 +
          regularizedCarlsonFactorDiskZeroMass X T /
            regularizedCarlsonFactorHorizontalSeparation X T := by
        rw [add_comm]

/-- The preceding horizontal logarithmic-derivative estimate with its
principal-part term expressed using any available upper bound for the local
divisor mass. -/
theorem exists_regularizedCarlson_horizontal_logDeriv_le_of_factorDiskMass_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {X : ℕ}, 1 ≤ X →
      ∀ {sigma T L : ℝ}, 1 / 2 < sigma → 5 ≤ T →
        regularizedCarlsonFactorDiskZeroMass X T ≤ L →
        ∃ r ∈ Set.Icc (121 / 32 : ℝ) (122 / 32 : ℝ),
        ∃ t ∈ Set.Icc T (T + 1),
          (∀ x ∈ Set.Icc sigma 4,
            regularizedCarlsonZeroDetector X
              ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
          ∀ x ∈ Set.Icc sigma 4,
            ‖logDeriv (regularizedCarlsonZeroDetector X)
              ((x : ℂ) + (t : ℂ) * I)‖ ≤
              4 * max
                  (regularizedCarlsonFactorCircleLogUpper C X T -
                    regularizedCarlsonFactorCenterLogLower X T) 1 *
                (r + 15 / 4) / (r - 15 / 4) ^ 2 +
              L / (1 / (4 * (L + 1))) := by
  rcases exists_regularizedCarlson_horizontal_logDeriv_le_factorDisk with
    ⟨C, hC, hhorizontal⟩
  refine ⟨C, hC, ?_⟩
  intro X hX sigma T L hsigma hT hmass
  rcases hhorizontal hX hsigma hT with ⟨r, hr, t, ht, hne, hbound⟩
  have hsep :=
    regularizedCarlsonFactorHorizontalSeparation_lower_of_mass_le hmass
  have hmassNonneg : 0 ≤ regularizedCarlsonFactorDiskZeroMass X T := by
    let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
    let b : ℝ := 123 / 32
    let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
      (Metric.closedBall c b)
    have hanalyticFactor : AnalyticOnNhd ℂ
        (regularizedCarlsonZeroDetector X) (Metric.closedBall c b) := by
      apply
        (analyticOnNhd_regularizedCarlsonZeroDetector_fixedJensenOuterDisk
          X T).mono
      exact Metric.closedBall_subset_closedBall (by norm_num [b])
    have hDnonneg : 0 ≤ D := hanalyticFactor.divisor_nonneg
    change 0 ≤ ∑ᶠ u, (D u : ℝ)
    apply finsum_nonneg
    intro u
    exact_mod_cast hDnonneg u
  have hprincipal :
      regularizedCarlsonFactorDiskZeroMass X T /
          regularizedCarlsonFactorHorizontalSeparation X T ≤
        L / (1 / (4 * (L + 1))) := by
    calc
      regularizedCarlsonFactorDiskZeroMass X T /
          regularizedCarlsonFactorHorizontalSeparation X T ≤
          regularizedCarlsonFactorDiskZeroMass X T /
            (1 / (4 * (L + 1))) :=
        div_le_div_of_nonneg_left hmassNonneg hsep.1 hsep.2
      _ ≤ L / (1 / (4 * (L + 1))) :=
        div_le_div_of_nonneg_right hmass hsep.1.le
  refine ⟨r, hr, t, ht, hne, ?_⟩
  intro x hx
  exact (hbound x hx).trans (add_le_add_right hprincipal _)

/-- The horizontal logarithmic-derivative bound with both the regular factor
and the principal part expressed only through an assumed divisor-mass
majorant. -/
theorem
    exists_regularizedCarlson_horizontal_logDeriv_le_of_factorDiskMass_le_explicit :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {X : ℕ}, 1 ≤ X →
      ∀ {sigma T L : ℝ}, 1 / 2 < sigma → 5 ≤ T →
        regularizedCarlsonFactorDiskZeroMass X T ≤ L →
        ∃ r ∈ Set.Icc (121 / 32 : ℝ) (122 / 32 : ℝ),
        ∃ t ∈ Set.Icc T (T + 1),
          (∀ x ∈ Set.Icc sigma 4,
            regularizedCarlsonZeroDetector X
              ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
          ∀ x ∈ Set.Icc sigma 4,
            ‖logDeriv (regularizedCarlsonZeroDetector X)
              ((x : ℂ) + (t : ℂ) * I)‖ ≤
              4 * max
                  (regularizedCarlsonFactorLogVariationMajorant C X T L) 1 *
                (r + 15 / 4) / (r - 15 / 4) ^ 2 +
              L / (1 / (4 * (L + 1))) := by
  rcases
      exists_regularizedCarlson_horizontal_logDeriv_le_of_factorDiskMass_le with
    ⟨C, hC, hhorizontal⟩
  refine ⟨C, hC, ?_⟩
  intro X hX sigma T L hsigma hT hmass
  rcases hhorizontal hX hsigma hT hmass with
    ⟨r, hr, t, ht, hne, hbound⟩
  have hvariation :=
    regularizedCarlsonFactorLogVariation_le_of_mass_le
      (C := C) hmass
  have hrPos : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
  have hgapPos : 0 < r - 15 / 4 := by linarith [hr.1]
  have hregular :
      4 * max
          (regularizedCarlsonFactorCircleLogUpper C X T -
            regularizedCarlsonFactorCenterLogLower X T) 1 *
          (r + 15 / 4) / (r - 15 / 4) ^ 2 ≤
        4 * max
          (regularizedCarlsonFactorLogVariationMajorant C X T L) 1 *
          (r + 15 / 4) / (r - 15 / 4) ^ 2 := by
    have hmax := max_le_max_right (1 : ℝ) hvariation
    have hnum : 0 ≤ r + 15 / 4 := by positivity
    have hinv : 0 ≤ ((r - 15 / 4) ^ 2)⁻¹ := by positivity
    have hfour := mul_le_mul_of_nonneg_left hmax (by norm_num : (0 : ℝ) ≤ 4)
    have hnumerator := mul_le_mul_of_nonneg_right hfour hnum
    simpa [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_right hnumerator hinv)
  refine ⟨r, hr, t, ht, hne, ?_⟩
  intro x hx
  exact (hbound x hx).trans (add_le_add_left hregular _)

/-- The complete divisor mass on the factorization disk is explicitly
controlled by the detector's polynomial outer-circle growth. -/
theorem exists_regularizedCarlsonFactorZeroMass_le_logPolynomial :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {X : ℕ}, 1 ≤ X → ∀ {T : ℝ}, 5 ≤ T →
      (∑ᶠ u,
        (MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
          (Metric.closedBall
            ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) u : ℝ)) ≤
        regularizedCarlsonFactorZeroLogMajorant C X T := by
  rcases exists_norm_regularizedCarlsonZeroDetector_le_fixedJensenSphere with
    ⟨C, hC, hsphere⟩
  refine ⟨C, hC, ?_⟩
  intro X hX T hT
  let c : ℂ := (4 : ℂ) + I * (T + 1 / 2)
  let M : ℝ := C * (X : ℝ) ^ 2 * (T + 14) ^ 10
  have hXReal : 1 ≤ (X : ℝ) := by exact_mod_cast hX
  have hXPow : 1 ≤ (X : ℝ) ^ 2 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hXReal 2
  have hTBase : 1 ≤ T + 14 := by linarith
  have hTPow : 1 ≤ (T + 14) ^ 10 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hTBase 10
  have hCX : 1 ≤ C * (X : ℝ) ^ 2 := by
    simpa using mul_le_mul hC hXPow (by norm_num) (by linarith)
  have hM : 1 ≤ M := by
    dsimp [M]
    simpa using mul_le_mul hCX hTPow (by norm_num)
      (mul_nonneg (by linarith) (by positivity))
  have hanalytic :=
    analyticOnNhd_regularizedCarlsonZeroDetector_fixedJensenOuterDisk X T
  have hcircle : Real.circleAverage
      (Real.log ‖regularizedCarlsonZeroDetector X ·‖) c (31 / 8 : ℝ) ≤
        Real.log M := by
    apply circleAverage_log_norm_le_log_of_norm_le
      (by norm_num) hanalytic.meromorphicOn hM
    intro z hz
    simpa [M, c] using hsphere hX hT (by simpa [c] using hz)
  have hjensen := jensen_inner_zero_multiplicity_le_log_div
    (f := regularizedCarlsonZeroDetector X) (c := c)
    (r := (123 / 32 : ℝ)) (R := (31 / 8 : ℝ))
    (K := Real.log M) (m := (1 : ℝ))
    (by norm_num) (by norm_num) hanalytic one_pos
    (one_le_norm_regularizedCarlsonZeroDetector_of_four_le_re hX (by simp [c]))
    hcircle
  have hlocal := finsum_divisor_closedBall_eq_finsum_mem_of_le
    (f := regularizedCarlsonZeroDetector X) (c := c)
    (b := (123 / 32 : ℝ)) (R := (31 / 8 : ℝ))
    (by norm_num) hanalytic.meromorphicOn
  rw [hlocal]
  simpa [regularizedCarlsonFactorZeroLogMajorant, M, c] using hjensen

/-- The zero-removed detector factor has an explicit center lower bound in
terms of `X` and `T`; no unevaluated divisor mass remains. -/
theorem exists_regularizedCarlsonZeroDetector_fixedJensenFactor_explicit_center_lower :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {X : ℕ}, 1 ≤ X → ∀ {T : ℝ}, 5 ≤ T →
      ∃ g : ℂ → ℂ,
        AnalyticOnNhd ℂ g
          (Metric.closedBall
            ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) ∧
        (∀ u : (Metric.closedBall
            ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ) : Set ℂ),
          g u ≠ 0) ∧
        -Real.log (123 / 32 : ℝ) *
            regularizedCarlsonFactorZeroLogMajorant C X T ≤
          Real.log ‖g ((4 : ℂ) + I * (T + 1 / 2))‖ := by
  rcases exists_regularizedCarlsonFactorZeroMass_le_logPolynomial with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro X hX T hT
  rcases exists_regularizedCarlsonZeroDetector_fixedJensenFactor_center_lower
      hX (T := T) with ⟨g, hg, hgne, hcenter⟩
  refine ⟨g, hg, hgne, ?_⟩
  have hlogNonneg : 0 ≤ Real.log (123 / 32 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hmul := mul_le_mul_of_nonpos_left (hmass hX hT)
    (neg_nonpos.mpr hlogNonneg)
  exact hmul.trans hcenter

end CarlsonZeroDensity
end PrimeNumberTheorem
