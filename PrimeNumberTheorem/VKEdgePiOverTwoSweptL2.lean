import PrimeNumberTheorem.VKEdgePiOverTwoOrdinaryL2

open Complex Filter MeasureTheory Polynomial Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/--
An integrable fixed-variance envelope for the Gaussian kernels obtained while
the scale `m` sweeps through `[M, R * M]`.
-/
def sweptGaussianEnvelope (q M R m y : ℝ) : ℝ :=
  Real.exp 2 * Real.sqrt (2 * R) *
    normalizedGaussian (2 * R * M) (q * m - y)

private theorem scaledGaussian_completion_square
    {m t : ℝ} (hm : 0 < m) :
    Real.exp |(Real.sqrt m)⁻¹ * t| *
        normalizedGaussian m t ≤
      Real.exp 2 *
        (Real.exp (-t ^ 2 / (8 * m)) /
          (2 * Real.sqrt (Real.pi * m))) := by
  have hsqrtPos : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  let u : ℝ := (Real.sqrt m)⁻¹ * t
  have huSq : u ^ 2 = t ^ 2 / m := by
    dsimp [u]
    rw [inv_mul_eq_div, div_pow, Real.sq_sqrt hm.le]
  have hquad : |u| - u ^ 2 / 4 ≤ 2 - u ^ 2 / 8 := by
    nlinarith [sq_nonneg (|u| - 4), sq_abs u]
  have hexp :
      Real.exp (|u| - u ^ 2 / 4) ≤
        Real.exp (2 - u ^ 2 / 8) :=
    Real.exp_le_exp.mpr hquad
  have hdenomPos : 0 < 2 * Real.sqrt (Real.pi * m) := by
    positivity
  unfold normalizedGaussian
  calc
    Real.exp |(Real.sqrt m)⁻¹ * t| *
          (Real.exp (-t ^ 2 / (4 * m)) /
            (2 * Real.sqrt (Real.pi * m))) =
        Real.exp (|u| - u ^ 2 / 4) /
          (2 * Real.sqrt (Real.pi * m)) := by
      rw [← mul_div_assoc, ← Real.exp_add]
      congr 2
      rw [huSq]
      ring
    _ ≤ Real.exp (2 - u ^ 2 / 8) /
          (2 * Real.sqrt (Real.pi * m)) :=
      div_le_div_of_nonneg_right hexp hdenomPos.le
    _ = Real.exp 2 *
          (Real.exp (-t ^ 2 / (8 * m)) /
            (2 * Real.sqrt (Real.pi * m))) := by
      rw [← mul_div_assoc, ← Real.exp_add]
      congr 2
      rw [huSq]
      field_simp
      ring

theorem exp_scaled_abs_mul_normalizedGaussian_le_sweptEnvelope
    {q M R m y : ℝ}
    (hM : 1 ≤ M) (hR : 1 ≤ R)
    (hmLower : M ≤ m) (hmUpper : m ≤ R * M) :
    Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
        normalizedGaussian m (q * m - y) ≤
      sweptGaussianEnvelope q M R m y := by
  have hMPos : 0 < M := zero_lt_one.trans_le hM
  have hmPos : 0 < m := hMPos.trans_le hmLower
  have hRPos : 0 < R := zero_lt_one.trans_le hR
  have hRMPos : 0 < R * M := mul_pos hRPos hMPos
  have hscalePos : 0 < 2 * R * M := by positivity
  have hbase :=
    scaledGaussian_completion_square
      (m := m) (t := q * m - y) hmPos
  rw [sweptGaussianEnvelope]
  calc
    Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
          normalizedGaussian m (q * m - y) ≤
        Real.exp 2 *
          (Real.exp (-(q * m - y) ^ 2 / (8 * m)) /
            (2 * Real.sqrt (Real.pi * m))) := hbase
    _ ≤ Real.exp 2 * Real.sqrt (2 * R) *
          normalizedGaussian (2 * R * M) (q * m - y) := by
      unfold normalizedGaussian
      have hexponent :
          Real.exp (-(q * m - y) ^ 2 / (8 * m)) ≤
            Real.exp (-(q * m - y) ^ 2 /
              (4 * (2 * R * M))) := by
        apply Real.exp_le_exp.mpr
        have hsquare : 0 ≤ (q * m - y) ^ 2 := sq_nonneg _
        have hdenom : m ≤ R * M := hmUpper
        apply (div_le_div_iff₀ (by positivity : 0 < 8 * m)
          (by positivity : 0 < 4 * (2 * R * M))).2
        nlinarith
      have hsqrtM :
          Real.sqrt (Real.pi * M) ≤
            Real.sqrt (Real.pi * m) := by
        exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hmLower Real.pi_pos.le)
      have hsqrtIdentity :
          Real.sqrt (2 * R) * Real.sqrt (Real.pi * M) =
            Real.sqrt (Real.pi * (2 * R * M)) := by
        rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * R)]
        congr 1
        ring
      have hprefactor :
          1 / (2 * Real.sqrt (Real.pi * m)) ≤
            Real.sqrt (2 * R) /
              (2 * Real.sqrt (Real.pi * (2 * R * M))) := by
        rw [← hsqrtIdentity]
        have hsqrtRPos : 0 < Real.sqrt (2 * R) := by positivity
        field_simp
        nlinarith
      have hexpNonneg :
          0 ≤ Real.exp (-(q * m - y) ^ 2 / (8 * m)) :=
        (Real.exp_pos _).le
      have hrightNonneg :
          0 ≤ Real.sqrt (2 * R) /
            (2 * Real.sqrt (Real.pi * (2 * R * M))) := by
        positivity
      calc
        Real.exp 2 *
              (Real.exp (-(q * m - y) ^ 2 / (8 * m)) /
                (2 * Real.sqrt (Real.pi * m))) =
            Real.exp 2 *
              (Real.exp (-(q * m - y) ^ 2 / (8 * m)) *
                (1 / (2 * Real.sqrt (Real.pi * m)))) := by ring
        _ ≤ Real.exp 2 *
              (Real.exp (-(q * m - y) ^ 2 / (8 * m)) *
                (Real.sqrt (2 * R) /
                  (2 * Real.sqrt (Real.pi * (2 * R * M))))) := by
          gcongr
        _ ≤ Real.exp 2 *
              (Real.exp (-(q * m - y) ^ 2 /
                  (4 * (2 * R * M))) *
                (Real.sqrt (2 * R) /
                  (2 * Real.sqrt (Real.pi * (2 * R * M))))) := by
          gcongr
        _ = Real.exp 2 * Real.sqrt (2 * R) *
              (Real.exp (-(q * m - y) ^ 2 /
                  (4 * (2 * R * M))) /
                (2 * Real.sqrt (Real.pi * (2 * R * M)))) := by ring

private theorem integral_normalizedGaussian_affine
    {q v y : ℝ} (hq : 0 < q) (hv : 0 < v) :
    (∫ m : ℝ, normalizedGaussian v (q * m - y)) = 1 / q := by
  have hshift :
      (∫ u : ℝ, normalizedGaussian v (u - y)) =
        ∫ u : ℝ, normalizedGaussian v u := by
    simpa [sub_eq_add_neg] using
      (integral_add_right_eq_self (normalizedGaussian v) (-y))
  have hscale :=
    Measure.integral_comp_mul_left
      (fun u : ℝ => normalizedGaussian v (u - y)) q
  rw [hshift, integral_normalizedGaussian hv] at hscale
  simpa [abs_of_pos (inv_pos.mpr hq), one_div] using hscale

theorem integral_sweptGaussianEnvelope_le
    {q M R y : ℝ}
    (hq : 0 < q) (hM : 0 < M) (hR : 0 < R) :
    (∫ m in Set.Icc M (R * M),
        sweptGaussianEnvelope q M R m y) ≤
      Real.exp 2 * Real.sqrt (2 * R) / q := by
  have hscalePos : 0 < 2 * R * M := by positivity
  have hbaseInt :
      Integrable
        (fun m : ℝ => normalizedGaussian (2 * R * M) (q * m - y)) := by
    have hshift :=
      (integrable_normalizedGaussian hscalePos).comp_add_right (-y)
    simpa [sub_eq_add_neg] using hshift.comp_mul_left' hq.ne'
  have henvelopeInt :
      Integrable (fun m : ℝ => sweptGaussianEnvelope q M R m y) := by
    simpa only [sweptGaussianEnvelope] using
      hbaseInt.const_mul (Real.exp 2 * Real.sqrt (2 * R))
  have hnonneg :
      ∀ᶠ m : ℝ in ae (volume.restrict Set.univ),
        0 ≤ sweptGaussianEnvelope q M R m y := by
    filter_upwards with m
    unfold sweptGaussianEnvelope
    exact mul_nonneg (by positivity)
      (normalizedGaussian_pos hscalePos (q * m - y)).le
  calc
    (∫ m in Set.Icc M (R * M),
        sweptGaussianEnvelope q M R m y) ≤
        ∫ m in Set.univ, sweptGaussianEnvelope q M R m y := by
      apply setIntegral_mono_set henvelopeInt.integrableOn hnonneg
      filter_upwards with m
      intro _hm
      exact Set.mem_univ m
    _ = ∫ m : ℝ, sweptGaussianEnvelope q M R m y := by simp
    _ = Real.exp 2 * Real.sqrt (2 * R) / q := by
      rw [show
          (fun m : ℝ => sweptGaussianEnvelope q M R m y) =
            fun m : ℝ =>
              (Real.exp 2 * Real.sqrt (2 * R)) *
                normalizedGaussian (2 * R * M) (q * m - y) by
        funext m
        rfl]
      rw [integral_const_mul, integral_normalizedGaussian_affine hq hscalePos]
      ring

private theorem measurable_normalizedPsiError_swept (rho : ℂ) :
    Measurable (normalizedPsiError rho) := by
  have hpsi : Measurable chebyshevPsi := by
    simpa only [chebyshevPsi_eq_mathlib] using
      Chebyshev.psi_mono.measurable
  unfold normalizedPsiError
  fun_prop

private theorem sweptGaussianEnvelope_nonneg
    {q M R m y : ℝ} (hscale : 0 < 2 * R * M) :
    0 ≤ sweptGaussianEnvelope q M R m y := by
  unfold sweptGaussianEnvelope
  exact mul_nonneg (by positivity)
    (normalizedGaussian_pos hscale (q * m - y)).le

private theorem sweptGaussianEnvelope_le_peak
    {q M R m y : ℝ} (hR : 0 < R) (hM : 0 < M) :
    sweptGaussianEnvelope q M R m y ≤
      Real.exp 2 * Real.sqrt (2 * R) /
        (2 * Real.sqrt (Real.pi * (2 * R * M))) := by
  have hscale : 0 < 2 * R * M := by positivity
  have hexponent :
      Real.exp (-(q * m - y) ^ 2 / (4 * (2 * R * M))) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  unfold sweptGaussianEnvelope normalizedGaussian
  have hdenom : 0 ≤ 2 * Real.sqrt (Real.pi * (2 * R * M)) := by
    positivity
  calc
    Real.exp 2 * Real.sqrt (2 * R) *
          (Real.exp (-(q * m - y) ^ 2 / (4 * (2 * R * M))) /
            (2 * Real.sqrt (Real.pi * (2 * R * M)))) ≤
        Real.exp 2 * Real.sqrt (2 * R) *
          (1 / (2 * Real.sqrt (Real.pi * (2 * R * M)))) := by
      gcongr
    _ = _ := by
      simp [div_eq_mul_inv, mul_assoc]

/--
Sweeping a fixed positive weighted second-moment lower bound across a
nontrivial interval of Gaussian scales forces an ordinary second moment
proportional to the scale interval length.
-/
theorem ordinarySecondMoment_linear_lower_of_sweptWeightedLower
    {q d M R a b C2 K B : ℝ} {rho : ℂ}
    {kernel : ℝ → ℝ → ℝ}
    (hM : 1 ≤ M) (hq : 0 < q) (hR : 1 < R)
    (hK : 0 ≤ K) (hB : 0 ≤ B)
    (herrorBound :
      ∀ y ∈ Set.Icc a b, normalizedPsiError rho y ^ 2 ≤ B)
    (hwindow :
      ∀ m ∈ Set.Icc M (R * M),
        localizedGaussianLogWindow q d m ⊆ Set.Icc a b)
    (hkernel :
      ∀ m ∈ Set.Icc M (R * M),
        ∀ y ∈ localizedGaussianLogWindow q d m,
          |kernel m y| ≤
            K *
              (Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
                normalizedGaussian m (q * m - y)))
    (hweightedInt :
      ∀ m ∈ Set.Icc M (R * M),
        IntegrableOn
          (fun y =>
            normalizedPsiError rho y ^ 2 * |kernel m y|)
          (localizedGaussianLogWindow q d m))
    (hweighted :
      ∀ m ∈ Set.Icc M (R * M),
        C2 <
          centeredNormalizedWindowSecondMoment q d rho kernel m) :
    C2 * (R - 1) * M ≤
      K * (Real.exp 2 * Real.sqrt (2 * R) / q) *
        ∫ y in Set.Icc a b, normalizedPsiError rho y ^ 2 := by
  have hMPos : 0 < M := zero_lt_one.trans_le hM
  have hRPos : 0 < R := zero_lt_one.trans hR
  have hscale : 0 < 2 * R * M := by positivity
  have hsweepLe : M ≤ R * M := by
    nlinarith
  let sweep : Set ℝ := Set.Icc M (R * M)
  let window : Set ℝ := Set.Icc a b
  let μ : Measure ℝ := volume.restrict sweep
  let ν : Measure ℝ := volume.restrict window
  let f : ℝ → ℝ := fun y => normalizedPsiError rho y ^ 2
  let H : ℝ × ℝ → ℝ := fun p =>
    f p.2 * K * sweptGaussianEnvelope q M R p.1 p.2
  have hfMeas : Measurable f := by
    dsimp [f]
    exact (measurable_normalizedPsiError_swept rho).pow_const 2
  have hfNonneg (y : ℝ) : 0 ≤ f y := by
    exact sq_nonneg _
  have hfInt : IntegrableOn f window := by
    apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top
    · exact hfMeas.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (hfNonneg y)]
      exact herrorBound y hy
  have henvMeas :
      Measurable (fun p : ℝ × ℝ =>
        sweptGaussianEnvelope q M R p.1 p.2) := by
    unfold sweptGaussianEnvelope normalizedGaussian
    fun_prop
  have hHMeas : Measurable H := by
    dsimp [H]
    exact ((hfMeas.comp measurable_snd).mul measurable_const).mul henvMeas
  have hpeakNonneg :
      0 ≤ Real.exp 2 * Real.sqrt (2 * R) /
        (2 * Real.sqrt (Real.pi * (2 * R * M))) := by
    positivity
  have hHRect :
      IntegrableOn H (sweep ×ˢ window) (volume.prod volume) := by
    apply IntegrableOn.of_bound
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top
    · exact hHMeas.aestronglyMeasurable.restrict
    · filter_upwards [
          ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
      have hfLe : f p.2 ≤ B := herrorBound p.2 hp.2
      have henvLe :
          sweptGaussianEnvelope q M R p.1 p.2 ≤
            Real.exp 2 * Real.sqrt (2 * R) /
              (2 * Real.sqrt (Real.pi * (2 * R * M))) :=
        sweptGaussianEnvelope_le_peak hRPos hMPos
      have hHNonneg : 0 ≤ H p := by
        dsimp [H]
        exact mul_nonneg (mul_nonneg (hfNonneg p.2) hK)
          (sweptGaussianEnvelope_nonneg hscale)
      rw [Real.norm_eq_abs, abs_of_nonneg hHNonneg]
      dsimp [H]
      have henvNonneg :
          0 ≤ sweptGaussianEnvelope q M R p.1 p.2 :=
        sweptGaussianEnvelope_nonneg hscale
      calc
        f p.2 * K * sweptGaussianEnvelope q M R p.1 p.2 ≤
            B * K * sweptGaussianEnvelope q M R p.1 p.2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hfLe hK) henvNonneg
        _ ≤ B * K *
            (Real.exp 2 * Real.sqrt (2 * R) /
              (2 * Real.sqrt (Real.pi * (2 * R * M)))) := by
          gcongr
  have hHInt : Integrable H (μ.prod ν) := by
    simpa only [μ, ν, sweep, window, Measure.prod_restrict,
      IntegrableOn] using hHRect
  have hpoint :
      ∀ m ∈ sweep, C2 ≤ ∫ y, H (m, y) ∂ν := by
    intro m hm
    have hmOne : 1 ≤ m := hM.trans hm.1
    have hlocalMajorInt :
        IntegrableOn
          (fun y =>
            f y * K * sweptGaussianEnvelope q M R m y)
          (localizedGaussianLogWindow q d m) := by
      apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top
      · exact
          (((hfMeas.mul measurable_const).mul
            (henvMeas.comp
              (measurable_const.prodMk measurable_id))).aestronglyMeasurable).restrict
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        have hyWindow : y ∈ window := hwindow m hm hy
        have hfLe : f y ≤ B := herrorBound y hyWindow
        have henvLe :
            sweptGaussianEnvelope q M R m y ≤
              Real.exp 2 * Real.sqrt (2 * R) /
                (2 * Real.sqrt (Real.pi * (2 * R * M))) :=
          sweptGaussianEnvelope_le_peak hRPos hMPos
        have hnonneg :
            0 ≤ f y * K * sweptGaussianEnvelope q M R m y :=
          mul_nonneg (mul_nonneg (hfNonneg y) hK)
            (sweptGaussianEnvelope_nonneg hscale)
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        have henvNonneg :
            0 ≤ sweptGaussianEnvelope q M R m y :=
          sweptGaussianEnvelope_nonneg hscale
        calc
          f y * K * sweptGaussianEnvelope q M R m y ≤
              B * K * sweptGaussianEnvelope q M R m y := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hfLe hK) henvNonneg
          _ ≤ B * K *
              (Real.exp 2 * Real.sqrt (2 * R) /
                (2 * Real.sqrt (Real.pi * (2 * R * M)))) := by
            gcongr
    have hglobalMajorInt :
        IntegrableOn
          (fun y =>
            f y * K * sweptGaussianEnvelope q M R m y)
          window := by
      apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top
      · exact
          (((hfMeas.mul measurable_const).mul
            (henvMeas.comp
              (measurable_const.prodMk measurable_id))).aestronglyMeasurable).restrict
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        have hfLe : f y ≤ B := herrorBound y hy
        have henvLe :
            sweptGaussianEnvelope q M R m y ≤
              Real.exp 2 * Real.sqrt (2 * R) /
                (2 * Real.sqrt (Real.pi * (2 * R * M))) :=
          sweptGaussianEnvelope_le_peak hRPos hMPos
        have henvNonneg :
            0 ≤ sweptGaussianEnvelope q M R m y :=
          sweptGaussianEnvelope_nonneg hscale
        have hnonneg :
            0 ≤ f y * K * sweptGaussianEnvelope q M R m y :=
          mul_nonneg (mul_nonneg (hfNonneg y) hK) henvNonneg
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        calc
          f y * K * sweptGaussianEnvelope q M R m y ≤
              B * K * sweptGaussianEnvelope q M R m y :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hfLe hK) henvNonneg
          _ ≤ B * K *
              (Real.exp 2 * Real.sqrt (2 * R) /
                (2 * Real.sqrt (Real.pi * (2 * R * M)))) := by
            gcongr
    have htrueLeLocal :
        (∫ y in localizedGaussianLogWindow q d m,
            f y * |kernel m y|) ≤
          ∫ y in localizedGaussianLogWindow q d m,
            f y * K * sweptGaussianEnvelope q M R m y := by
      apply integral_mono_ae (by simpa [f] using hweightedInt m hm)
        hlocalMajorInt
      filter_upwards [
        ae_restrict_mem measurableSet_Icc] with y hy
      have hscaled :=
        exp_scaled_abs_mul_normalizedGaussian_le_sweptEnvelope
          (q := q) (y := y) hM (le_of_lt hR) hm.1 hm.2
      have hkerLe :
          |kernel m y| ≤
            K * sweptGaussianEnvelope q M R m y := by
        exact (hkernel m hm y hy).trans
          (mul_le_mul_of_nonneg_left hscaled hK)
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hkerLe (hfNonneg y)
    have hlocalLeGlobal :
        (∫ y in localizedGaussianLogWindow q d m,
            f y * K * sweptGaussianEnvelope q M R m y) ≤
          ∫ y in window,
            f y * K * sweptGaussianEnvelope q M R m y := by
      apply setIntegral_mono_set hglobalMajorInt
      · filter_upwards with y
        exact mul_nonneg (mul_nonneg (hfNonneg y) hK)
          (sweptGaussianEnvelope_nonneg hscale)
      · filter_upwards with y
        intro hy
        exact hwindow m hm hy
    have hC2 :
        C2 <
          ∫ y in window,
            f y * K * sweptGaussianEnvelope q M R m y := by
      exact (hweighted m hm).trans_le
        (by
          unfold centeredNormalizedWindowSecondMoment
          exact htrueLeLocal.trans hlocalLeGlobal)
    simpa only [ν, H, IntegrableOn] using hC2.le
  have hconstInt : Integrable (fun _m : ℝ => C2) μ := by
    simpa only [μ, sweep, IntegrableOn] using
      (integrableOn_const (μ := volume) (s := Set.Icc M (R * M))
        (measure_Icc_lt_top.ne))
  have houterLe :
      (∫ _m : ℝ, C2 ∂μ) ≤
        ∫ m, ∫ y, H (m, y) ∂ν ∂μ := by
    apply integral_mono_ae hconstInt hHInt.integral_prod_left
    filter_upwards [ae_restrict_mem measurableSet_Icc] with m hm
    exact hpoint m hm
  have hleft :
      (∫ _m : ℝ, C2 ∂μ) = C2 * (R - 1) * M := by
    rw [integral_const]
    change (volume.restrict (Set.Icc M (R * M))).real Set.univ * C2 =
      C2 * (R - 1) * M
    rw [Measure.real, Measure.restrict_apply_univ,
      Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hsweepLe)]
    ring
  have hswap :
      (∫ m, ∫ y, H (m, y) ∂ν ∂μ) =
        ∫ y, ∫ m, H (m, y) ∂μ ∂ν :=
    integral_integral_swap hHInt
  have hinnerLe (y : ℝ) :
      (∫ m, H (m, y) ∂μ) ≤
        f y * K *
          (Real.exp 2 * Real.sqrt (2 * R) / q) := by
    calc
      (∫ m, H (m, y) ∂μ) =
          f y * K *
            ∫ m in sweep, sweptGaussianEnvelope q M R m y := by
        simp only [μ, H]
        rw [integral_const_mul]
      _ ≤ f y * K *
          (Real.exp 2 * Real.sqrt (2 * R) / q) := by
        gcongr
        exact integral_sweptGaussianEnvelope_le hq hMPos hRPos
  have hrightInt :
      Integrable
        (fun y => f y * K *
          (Real.exp 2 * Real.sqrt (2 * R) / q)) ν := by
    have h :=
      hfInt.const_mul
        (K * (Real.exp 2 * Real.sqrt (2 * R) / q))
    change Integrable
      (fun y => f y * K *
        (Real.exp 2 * Real.sqrt (2 * R) / q))
      (volume.restrict window)
    convert h using 1
    funext y
    ring
  have hrightLe :
      (∫ y, ∫ m, H (m, y) ∂μ ∂ν) ≤
        ∫ y, f y * K *
          (Real.exp 2 * Real.sqrt (2 * R) / q) ∂ν := by
    apply integral_mono_ae hHInt.integral_prod_right hrightInt
    exact Filter.Eventually.of_forall hinnerLe
  calc
    C2 * (R - 1) * M =
        ∫ _m : ℝ, C2 ∂μ := hleft.symm
    _ ≤ ∫ m, ∫ y, H (m, y) ∂ν ∂μ := houterLe
    _ = ∫ y, ∫ m, H (m, y) ∂μ ∂ν := hswap
    _ ≤ ∫ y, f y * K *
        (Real.exp 2 * Real.sqrt (2 * R) / q) ∂ν := hrightLe
    _ = K * (Real.exp 2 * Real.sqrt (2 * R) / q) *
        ∫ y in Set.Icc a b, normalizedPsiError rho y ^ 2 := by
      simp only [ν, window, f]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      ring

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
