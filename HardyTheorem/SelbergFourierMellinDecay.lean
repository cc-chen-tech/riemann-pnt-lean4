import HardyTheorem.SelbergFourierMellinContour
import ZeroFreeRegion.PhragmenLindelofZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators Interval

namespace HardyTheorem

/-!
# Uniform decay on the horizontal sides of Selberg's Mellin rectangle

The exact Fourier tilt grows like `exp (angle * t)`.  The rotated Gamma
estimate absorbs it and leaves `exp (-(delta/4) * |t|)`.  The remaining
zeta factor has only fourth-degree polynomial growth, and both mollifiers
are finite Dirichlet polynomials uniformly bounded on `-1 ≤ Re(s)`.
-/

/-- A crude finite bound for the square-root-zeta mollifier throughout the
strip used by the contour shift. -/
noncomputable def selbergSqrtZetaPsiStripBound (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X,
    ‖(selbergSqrtZetaTaperedCoeff X n : ℂ)‖ * (n : ℝ)

theorem selbergSqrtZetaPsiStripBound_nonneg (X : ℕ) :
    0 ≤ selbergSqrtZetaPsiStripBound X := by
  unfold selbergSqrtZetaPsiStripBound
  positivity

/-- On `Re(s) ≥ -1`, each reciprocal power is at most `n`, giving a
uniform finite bound for the mollifier. -/
theorem norm_selbergSqrtZetaPsi_le_stripBound
    {X : ℕ} {s : ℂ} (hs : -1 ≤ s.re) :
    ‖selbergSqrtZetaPsi X s‖ ≤ selbergSqrtZetaPsiStripBound X := by
  unfold selbergSqrtZetaPsi selbergMollifier
  calc
    ‖∑ n ∈ Finset.Icc 1 X,
        (selbergSqrtZetaTaperedCoeff X n : ℂ) *
          (1 / (n : ℂ) ^ s)‖ ≤
      ∑ n ∈ Finset.Icc 1 X,
        ‖(selbergSqrtZetaTaperedCoeff X n : ℂ) *
          (1 / (n : ℂ) ^ s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 X,
        ‖(selbergSqrtZetaTaperedCoeff X n : ℂ)‖ * (n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      have hrpow : ((n : ℝ) ^ s.re)⁻¹ ≤ (n : ℝ) := by
        calc
          ((n : ℝ) ^ s.re)⁻¹ = (n : ℝ) ^ (-s.re) := by
            rw [Real.rpow_neg (Nat.cast_nonneg n)]
          _ ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hnone (by linarith)
          _ = (n : ℝ) := Real.rpow_one _
      rw [norm_mul, norm_div, norm_one,
        Complex.norm_natCast_cpow_of_pos hnpos, one_div]
      exact mul_le_mul_of_nonneg_left hrpow (norm_nonneg _)
    _ = selbergSqrtZetaPsiStripBound X := rfl

/-- A uniform elementary bound for the real Gamma factor occurring when
`1/2 ≤ sigma ≤ 2`: here `1/4 ≤ sigma/2 ≤ 1`. -/
theorem real_Gamma_half_le_four
    {sigma : ℝ} (hsigma0 : 1 / 2 ≤ sigma) (hsigma2 : sigma ≤ 2) :
    Real.Gamma (sigma / 2) ≤ 4 := by
  let x := sigma / 2
  have hx0 : 0 < x := by dsimp [x]; linarith
  have hxquarter : 1 / 4 ≤ x := by dsimp [x]; linarith
  have hxone : x ≤ 1 := by dsimp [x]; linarith
  have hshift : Real.Gamma (x + 1) ≤ 1 :=
    ZeroFreeRegion.real_Gamma_le_one_of_one_le_of_le_two
      (by linarith) (by linarith)
  rw [Real.Gamma_add_one hx0.ne'] at hshift
  have hGnonneg : 0 ≤ Real.Gamma x :=
    (Real.Gamma_pos_of_pos hx0).le
  nlinarith [mul_nonneg (sub_nonneg.mpr hxquarter) hGnonneg]

/-- The archimedean factor together with Selberg's complex power has a
uniform exponential decay bound on `1/2 ≤ sigma ≤ 2`. -/
theorem norm_GammaR_mul_norm_selbergFourierZ_cpow_le
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ)
    {sigma t : ℝ} (hsigma0 : 1 / 2 ≤ sigma) (hsigma2 : sigma ≤ 2) :
    ‖Gammaℝ ((sigma : ℂ) + I * t)‖ *
        ‖selbergFourierZ delta y ^ ((sigma : ℂ) + I * t)‖ ≤
      4 * (Real.cos (selbergGammaRayAngle delta))⁻¹ *
        Real.exp (2 * |y|) * Real.exp (-(delta / 4) * |t|) := by
  let s : ℂ := (sigma : ℂ) + I * t
  let b : ℝ := Real.cos (selbergGammaRayAngle delta)
  change ‖Gammaℝ s‖ * ‖selbergFourierZ delta y ^ s‖ ≤
    4 * b⁻¹ * Real.exp (2 * |y|) *
      Real.exp (-(delta / 4) * |t|)
  have heta := selbergGammaRayAngle_mem hdelta0
    (hdeltaPi.trans (by linarith [Real.pi_pos]))
  have hbpos : 0 < b := by
    exact Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], heta.2⟩
  have hble : b ≤ 1 := by
    dsimp [b]
    exact Real.cos_le_one _
  have hpi : Real.pi ^ (-sigma / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [Real.pi_gt_three]) (by linarith)
  have hGammaR :
      ‖Gammaℝ s‖ ≤ ‖Complex.Gamma (s / 2)‖ := by
    rw [Gammaℝ_def, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-s / 2).re = -sigma / 2 := by
      dsimp [s]
      norm_num
    rw [hre]
    simpa using mul_le_mul_of_nonneg_right hpi (norm_nonneg _)
  have hgammaTilt := selbergGammaHalf_mul_fourierTilt_le_abs
    hdelta0 hdeltaPi (lt_of_lt_of_le (by norm_num) hsigma0) (t := t)
  have hGammaReal : Real.Gamma (sigma / 2) ≤ 4 :=
    real_Gamma_half_le_four hsigma0 hsigma2
  have hbpow : b ^ (-sigma / 2) ≤ b⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hbpos hble (by linarith)
  have hcoeff :
      Real.Gamma (sigma / 2) * b ^ (-sigma / 2) ≤ 4 * b⁻¹ := by
    exact mul_le_mul hGammaReal hbpow (Real.rpow_nonneg hbpos.le _)
      (by norm_num)
  have hyexp : Real.exp (-y * sigma) ≤ Real.exp (2 * |y|) := by
    apply Real.exp_le_exp.mpr
    have hy : -y ≤ |y| := neg_le_abs y
    have hsnonneg : 0 ≤ sigma := by linarith
    calc
      -y * sigma ≤ |y| * sigma :=
        mul_le_mul_of_nonneg_right hy hsnonneg
      _ ≤ |y| * 2 := mul_le_mul_of_nonneg_left hsigma2 (abs_nonneg y)
      _ = 2 * |y| := by ring
  have hzpow := norm_selbergFourierZ_cpow hdelta0 hdeltaPi y sigma t
  have hgammaTilt' :
      ‖Complex.Gamma (s / 2)‖ *
          Real.exp (selbergFourierAngle delta * t) ≤
        (4 * b⁻¹) * Real.exp (-(delta / 4) * |t|) := by
    have h := hgammaTilt
    change ‖Complex.Gamma (s / 2)‖ *
        Real.exp (selbergFourierAngle delta * t) ≤ _ at h
    calc
      _ ≤ (Real.Gamma (sigma / 2) * b ^ (-sigma / 2)) *
          Real.exp (-(delta / 4) * |t|) := h
      _ ≤ (4 * b⁻¹) * Real.exp (-(delta / 4) * |t|) :=
        mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le
  have hzexp : Real.exp (-y * sigma + selbergFourierAngle delta * t) =
      Real.exp (-y * sigma) *
        Real.exp (selbergFourierAngle delta * t) := by
    rw [← Real.exp_add]
  rw [hzpow, hzexp]
  calc
    ‖Gammaℝ s‖ *
        (Real.exp (-y * sigma) * Real.exp (selbergFourierAngle delta * t)) ≤
      ‖Complex.Gamma (s / 2)‖ *
        (Real.exp (-y * sigma) * Real.exp (selbergFourierAngle delta * t)) :=
      mul_le_mul_of_nonneg_right hGammaR
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp (-y * sigma) *
        (‖Complex.Gamma (s / 2)‖ *
          Real.exp (selbergFourierAngle delta * t)) := by ring
    _ ≤ Real.exp (2 * |y|) *
        ((4 * b⁻¹) * Real.exp (-(delta / 4) * |t|)) :=
      mul_le_mul hyexp hgammaTilt' (mul_nonneg (norm_nonneg _)
        (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = 4 * b⁻¹ * Real.exp (2 * |y|) *
        Real.exp (-(delta / 4) * |t|) := by ring

/-- Uniform polynomial-times-exponential bound for the complete Selberg
integrand on both horizontal sides. -/
theorem exists_norm_selbergMellinRaw_horizontal_le
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ sigma t : ℝ,
      sigma ∈ Set.Icc (1 / 2 : ℝ) 2 → 1 ≤ |t| →
      ‖selbergMellinRawIntegrand (selbergFourierZ delta y) X
          ((sigma : ℂ) + I * t)‖ ≤
        K * (|t| + 3) ^ 4 * Real.exp (-(delta / 4) * |t|) := by
  rcases ZeroFreeRegion.exists_norm_riemannZeta_le_polynomial_on_zero_four with
    ⟨C, hC, hZeta⟩
  let M := selbergSqrtZetaPsiStripBound X
  let G := 4 * (Real.cos (selbergGammaRayAngle delta))⁻¹ *
    Real.exp (2 * |y|)
  let K := G * C * M ^ 2
  have hM : 0 ≤ M := selbergSqrtZetaPsiStripBound_nonneg X
  have hbpos : 0 < Real.cos (selbergGammaRayAngle delta) := by
    have heta := selbergGammaRayAngle_mem hdelta0
      (hdeltaPi.trans (by linarith [Real.pi_pos]))
    exact Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], heta.2⟩
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro sigma t hsigma ht
  let s : ℂ := (sigma : ℂ) + I * t
  have hsre : s.re ∈ Set.Icc (0 : ℝ) 4 := by
    dsimp [s]
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    exact ⟨by linarith [hsigma.1], by linarith [hsigma.2]⟩
  have hzim : |s.im| = |t| := by dsimp [s]; simp
  have hzeta : ‖riemannZeta s‖ ≤ C * (|t| + 3) ^ 4 := by
    simpa [hzim] using hZeta s hsre (by simpa [hzim] using ht)
  have hpsi : ‖selbergSqrtZetaPsi X s‖ ≤ M := by
    apply norm_selbergSqrtZetaPsi_le_stripBound
    dsimp [s]
    simp
    linarith [hsigma.1]
  have hreflect : ‖selbergSqrtZetaPsi X (1 - s)‖ ≤ M := by
    apply norm_selbergSqrtZetaPsi_le_stripBound
    dsimp [s]
    simp
    linarith [hsigma.2]
  have harch := norm_GammaR_mul_norm_selbergFourierZ_cpow_le
    hdelta0 hdeltaPi y hsigma.1 hsigma.2 (t := t)
  change ‖Gammaℝ s * selbergSqrtZetaPsi X s *
      selbergSqrtZetaPsi X (1 - s) *
      selbergFourierZ delta y ^ s * riemannZeta s‖ ≤ _
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have hnonnegPoly : 0 ≤ (|t| + 3) ^ 4 := pow_nonneg (by positivity) _
  calc
    ‖Gammaℝ s‖ * ‖selbergSqrtZetaPsi X s‖ *
          ‖selbergSqrtZetaPsi X (1 - s)‖ *
          ‖selbergFourierZ delta y ^ s‖ * ‖riemannZeta s‖ =
      (‖Gammaℝ s‖ * ‖selbergFourierZ delta y ^ s‖) *
        ‖riemannZeta s‖ * ‖selbergSqrtZetaPsi X s‖ *
          ‖selbergSqrtZetaPsi X (1 - s)‖ := by ring
    _ ≤ (G * Real.exp (-(delta / 4) * |t|)) *
        (C * (|t| + 3) ^ 4) * M * M := by
      gcongr
    _ = K * (|t| + 3) ^ 4 * Real.exp (-(delta / 4) * |t|) := by
      dsimp [K]
      ring

theorem tendsto_shifted_pow_four_mul_exp_neg
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun T : ℝ => (T + 3) ^ 4 * Real.exp (-a * T))
      atTop (𝓝 0) := by
  have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((4 : ℕ) : ℝ) a ha
  have hshift : Tendsto (fun T : ℝ => T + 3) atTop atTop :=
    tendsto_atTop_add_const_right atTop 3 tendsto_id
  have hcomp := hbase.comp hshift
  have hscaled := hcomp.const_mul (Real.exp (3 * a))
  have hscaled0 :
      Tendsto
        (fun T : ℝ => Real.exp (3 * a) *
          ((T + 3) ^ 4 * Real.exp (-a * (T + 3))))
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero, Real.rpow_natCast] using hscaled
  apply hscaled0.congr'
  filter_upwards [] with T
  symm
  ·
    have hexp : Real.exp (3 * a) * Real.exp (-a * (T + 3)) =
        Real.exp (-a * T) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hexp]
    ring

/-- The upper horizontal side tends to zero as its height tends to infinity. -/
theorem tendsto_selbergMellinRaw_upper_horizontalIntegral_zero
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ) :
    Tendsto
      (fun T : ℝ => ∫ sigma : ℝ in (1 / 2)..2,
        selbergMellinRawIntegrand (selbergFourierZ delta y) X
          ((sigma : ℂ) + I * T))
      atTop (𝓝 0) := by
  rcases exists_norm_selbergMellinRaw_horizontal_le
    hdelta0 hdeltaPi y X with ⟨K, hK, hbound⟩
  have henv := tendsto_shifted_pow_four_mul_exp_neg
    (show 0 < delta / 4 by positivity)
  have hnorm : Tendsto (fun T : ℝ =>
      ‖∫ sigma : ℝ in (1 / 2)..2,
        selbergMellinRawIntegrand (selbergFourierZ delta y) X
          ((sigma : ℂ) + I * T)‖) atTop (𝓝 0) := by
    apply squeeze_zero'
      (g := fun T : ℝ =>
        (K * (T + 3) ^ 4 * Real.exp (-(delta / 4) * T)) * (3 / 2))
      (Eventually.of_forall fun _ => norm_nonneg _)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hpoint : ∀ sigma ∈ Set.uIoc (1 / 2 : ℝ) 2,
          ‖selbergMellinRawIntegrand (selbergFourierZ delta y) X
            ((sigma : ℂ) + I * T)‖ ≤
          K * (T + 3) ^ 4 * Real.exp (-(delta / 4) * T) := by
        intro sigma hsigma
        rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hsigma
        have hsigma' : sigma ∈ Set.Icc (1 / 2 : ℝ) 2 :=
          ⟨hsigma.1.le, hsigma.2⟩
        have hT0 : 0 ≤ T := zero_le_one.trans hT
        simpa [abs_of_nonneg hT0] using hbound sigma T hsigma' (by simpa [abs_of_nonneg hT0] using hT)
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun sigma : ℝ =>
          selbergMellinRawIntegrand (selbergFourierZ delta y) X
            ((sigma : ℂ) + I * T))
        (a := (1 / 2 : ℝ)) (b := 2)
        (C := K * (T + 3) ^ 4 * Real.exp (-(delta / 4) * T)) hpoint
      norm_num at hi
      simpa only [neg_mul] using hi
    · convert henv.const_mul (K * (3 / 2 : ℝ)) using 1
      · funext T
        ring
      · simp
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- The lower horizontal side tends to zero as its absolute height tends to
infinity. -/
theorem tendsto_selbergMellinRaw_lower_horizontalIntegral_zero
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ) :
    Tendsto
      (fun T : ℝ => ∫ sigma : ℝ in (1 / 2)..2,
        selbergMellinRawIntegrand (selbergFourierZ delta y) X
          ((sigma : ℂ) - I * T))
      atTop (𝓝 0) := by
  rcases exists_norm_selbergMellinRaw_horizontal_le
    hdelta0 hdeltaPi y X with ⟨K, hK, hbound⟩
  have henv := tendsto_shifted_pow_four_mul_exp_neg
    (show 0 < delta / 4 by positivity)
  have hnorm : Tendsto (fun T : ℝ =>
      ‖∫ sigma : ℝ in (1 / 2)..2,
        selbergMellinRawIntegrand (selbergFourierZ delta y) X
          ((sigma : ℂ) - I * T)‖) atTop (𝓝 0) := by
    apply squeeze_zero'
      (g := fun T : ℝ =>
        (K * (T + 3) ^ 4 * Real.exp (-(delta / 4) * T)) * (3 / 2))
      (Eventually.of_forall fun _ => norm_nonneg _)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hpoint : ∀ sigma ∈ Set.uIoc (1 / 2 : ℝ) 2,
          ‖selbergMellinRawIntegrand (selbergFourierZ delta y) X
            ((sigma : ℂ) - I * T)‖ ≤
          K * (T + 3) ^ 4 * Real.exp (-(delta / 4) * T) := by
        intro sigma hsigma
        rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hsigma
        have hsigma' : sigma ∈ Set.Icc (1 / 2 : ℝ) 2 :=
          ⟨hsigma.1.le, hsigma.2⟩
        have hT0 : 0 ≤ T := zero_le_one.trans hT
        have hb := hbound sigma (-T) hsigma' (by
          simpa [abs_of_nonneg hT0] using hT)
        simpa [sub_eq_add_neg, abs_of_nonneg hT0] using hb
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun sigma : ℝ =>
          selbergMellinRawIntegrand (selbergFourierZ delta y) X
            ((sigma : ℂ) - I * T))
        (a := (1 / 2 : ℝ)) (b := 2)
        (C := K * (T + 3) ^ 4 * Real.exp (-(delta / 4) * T)) hpoint
      norm_num at hi
      simpa only [neg_mul] using hi
    · convert henv.const_mul (K * (3 / 2 : ℝ)) using 1
      · funext T
        ring
      · simp
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

end HardyTheorem
