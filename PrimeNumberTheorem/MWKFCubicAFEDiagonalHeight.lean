import PrimeNumberTheorem.MWKFCubicAFEDiagonalMellinIntegral
import PrimeNumberTheorem.MWKFCubicAFEScalarTime
import Mathlib.Analysis.Normed.Group.FunctionSeries

open Complex Filter MeasureTheory Set
open scoped Topology Interval

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Independent height limit of the literal diagonal Mellin integral

The reciprocal-LCM and zeta factors are the original diagonal kernel.
Its vertical arithmetic bound comes from the actual convergent diagonal
series. A compact-time Gaussian bound proves physical time/height L1.
No residue evaluation, zero-mode identity or T-asymptotic is assumed.
-/

noncomputable def cubicAFEDiagonalMellinMass (d e : ℕ) (X : ℝ) : ℝ :=
  ∑' k : ℕ, ‖cubicAFEDiagonalMellinMonomial d e k (X : ℂ)‖

theorem cubicAFEDiagonalMellinMass_nonneg (d e : ℕ) (X : ℝ) :
    0 ≤ cubicAFEDiagonalMellinMass d e X := tsum_nonneg (fun _ ↦ norm_nonneg _)

private theorem diagonal_product_pos {d e : ℕ} (hd : 0 < d) (he : 0 < e) (k : ℕ) :
    0 < (k + 1)^2 * (d / Nat.gcd d e) * (e / Nat.gcd d e) := by
  rw [← cubicAFEPositiveIndexProduct_diagonalRay hd he k]
  unfold cubicAFEPositiveIndexProduct
  positivity

private theorem monomial_norm {d e : ℕ} (hd : 0 < d) (he : 0 < e) (k : ℕ) (X v : ℝ) :
    ‖cubicAFEDiagonalMellinMonomial d e k (cubicAFEVerticalPoint X v)‖ =
      ‖cubicAFEDiagonalMellinMonomial d e k (X : ℂ)‖ := by
  unfold cubicAFEDiagonalMellinMonomial
  simp only [norm_mul, norm_div, norm_one]
  have hK := diagonal_product_pos hd he k
  have hcast (n : ℕ) : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
  rw [hcast ((k + 1)^2 * (d / Nat.gcd d e) * (e / Nat.gcd d e)),
    norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hK),
    norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hK)]
  simp [cubicAFEVerticalPoint]

private theorem monomial_continuous {d e : ℕ} (hd : 0 < d) (he : 0 < e) (k : ℕ) (X : ℝ) :
    Continuous (fun v : ℝ ↦ cubicAFEDiagonalMellinMonomial d e k (cubicAFEVerticalPoint X v)) := by
  let K := (k + 1)^2 * (d / Nat.gcd d e) * (e / Nat.gcd d e)
  have hK : (K : ℂ) ≠ 0 := by exact_mod_cast (diagonal_product_pos hd he k).ne'
  let : NeZero (K : ℂ) := ⟨hK⟩
  have hz : Continuous (cubicAFEVerticalPoint X) := by unfold cubicAFEVerticalPoint; fun_prop
  have hp := (continuous_const_cpow (K : ℂ)).comp hz
  exact continuous_const.mul (continuous_const.div₀ hp (fun _ ↦ cpow_ne_zero_iff.mpr (Or.inl hK)))

private theorem mass_summable {X : ℝ} (hX : 1 / 2 < X) {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Summable (fun k : ℕ ↦ ‖cubicAFEDiagonalMellinMonomial d e k (X : ℂ)‖) :=
  summable_norm_iff.mpr (hasSum_cubicAFEDiagonalMellinMonomial hd he
    (by simpa using (show 0 < X by linarith))).summable

private theorem kernel_eq_series (t : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) (v : ℝ) :
    cubicAFEDiagonalMellinKernel d e t (cubicAFEVerticalPoint X v) =
      cubicAFEScalar t (cubicAFEVerticalPoint X v) *
        ∑' k : ℕ, cubicAFEDiagonalMellinMonomial d e k (cubicAFEVerticalPoint X v) := by
  rw [(hasSum_cubicAFEDiagonalMellinMonomial hd he
    (by simp [cubicAFEVerticalPoint]; linarith : 0 < (cubicAFEVerticalPoint X v).re)).tsum_eq]
  rfl

theorem cubicAFEDiagonalMellinKernel_norm_le (t : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) (v : ℝ) :
    ‖cubicAFEDiagonalMellinKernel d e t (cubicAFEVerticalPoint X v)‖ ≤
      ‖cubicAFEScalar t (cubicAFEVerticalPoint X v)‖ * cubicAFEDiagonalMellinMass d e X := by
  rw [kernel_eq_series t hX hd he v, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hs : Summable (fun k : ℕ ↦ ‖cubicAFEDiagonalMellinMonomial d e k (cubicAFEVerticalPoint X v)‖) := by
    simpa only [monomial_norm hd he] using mass_summable hX hd he
  simpa only [monomial_norm hd he, cubicAFEDiagonalMellinMass] using norm_tsum_le_tsum_norm hs

theorem continuous_cubicAFEDiagonalMellinKernel_joint {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Continuous (fun p : ℝ × ℝ ↦ cubicAFEDiagonalMellinKernel d e p.1 (cubicAFEVerticalPoint X p.2)) := by
  have hc : Continuous (fun v : ℝ ↦ ∑' k : ℕ,
      cubicAFEDiagonalMellinMonomial d e k (cubicAFEVerticalPoint X v)) :=
    continuous_tsum (fun k ↦ monomial_continuous hd he k X) (mass_summable hX hd he)
      (fun k v ↦ (monomial_norm hd he k X v).le)
  have hh := (continuous_cubicAFEScalar_joint_of_halfPlane (X := X) (by linarith) (by linarith)).mul
    (hc.comp continuous_snd)
  simpa only [kernel_eq_series _ hX hd he, Pi.mul_def, Function.comp_def] using hh

theorem integrable_cubicAFEDiagonalMellinKernel (t : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Integrable (fun v : ℝ ↦ cubicAFEDiagonalMellinKernel d e t (cubicAFEVerticalPoint X v)) :=
  (((integrable_cubicAFEScalar_vertical t (by linarith) (by linarith)).norm).mul_const
    (cubicAFEDiagonalMellinMass d e X)).mono'
      ((continuous_cubicAFEDiagonalMellinKernel_joint hX hd he).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (Eventually.of_forall (cubicAFEDiagonalMellinKernel_norm_le t hX hd he))

noncomputable def cubicAFEDiagonalPhysicalMellinKernel
    (W : CubicTestWeight) (T X : ℝ) (d e : ℕ) (t v : ℝ) : ℂ :=
  cubicAFEDiagonalOuterWeight W T d e t * (1 / (2 * Real.pi) : ℂ) *
    cubicAFEDiagonalMellinKernel d e t (cubicAFEVerticalPoint X v)

theorem continuous_cubicAFEDiagonalPhysicalMellinKernel
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Continuous (Function.uncurry (cubicAFEDiagonalPhysicalMellinKernel W T X d e)) := by
  have hw : Continuous (cubicAFEDiagonalOuterWeight W T d e) := by
    unfold cubicAFEDiagonalOuterWeight
    exact continuous_const.mul (Complex.continuous_ofReal.comp (W.continuous.comp (continuous_id.div_const T)))
  exact ((hw.comp continuous_fst).mul continuous_const).mul
    (continuous_cubicAFEDiagonalMellinKernel_joint hX hd he)

/-- Actual time/height L1, with the reciprocal-LCM and zeta factors intact.
The compact-time scalar bound is proved, not supplied as a new hypothesis. -/
theorem integrable_cubicAFEDiagonalPhysicalMellinKernel
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Integrable (Function.uncurry (cubicAFEDiagonalPhysicalMellinKernel W T X d e)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_cubicAFEScalar_vertical_le_on_compact
    (X := X) (by linarith) (by linarith) (W.hasCompactSupport_dilate hT)
  let A := ‖(cubicMollifierCoefficient T d : ℂ) * (cubicMollifierCoefficient T e : ℂ) * 2‖
  let B := A * ‖(1 / (2 * Real.pi) : ℂ)‖ * C * cubicAFEDiagonalMellinMass d e X
  have hwi : Integrable (fun t : ℝ ↦ ‖W (t / T)‖) :=
    (W.continuous.comp (continuous_id.div_const T)).norm.integrable_of_hasCompactSupport
      (W.hasCompactSupport_dilate hT).norm
  have hb : Integrable (fun p : ℝ × ℝ ↦ (B * ‖W (p.1 / T)‖) * cubicAFEVerticalGaussianMajorant X p.2) :=
    (hwi.const_mul B).mul_prod (integrable_cubicAFEVerticalGaussianMajorant X)
  apply hb.mono' (continuous_cubicAFEDiagonalPhysicalMellinKernel W T hX hd he).aestronglyMeasurable
  filter_upwards [] with p
  by_cases hz : W (p.1 / T) = 0
  · simp [Function.uncurry, cubicAFEDiagonalPhysicalMellinKernel, cubicAFEDiagonalOuterWeight, hz]
  have ht : p.1 ∈ tsupport (fun t : ℝ ↦ W (t / T)) := subset_tsupport _ hz
  have hnorm : ‖cubicAFEDiagonalOuterWeight W T d e p.1‖ = A * ‖W (p.1 / T)‖ := by
    simp only [cubicAFEDiagonalOuterWeight, norm_mul, Complex.norm_real, A]
  change ‖cubicAFEDiagonalOuterWeight W T d e p.1 * (1 / (2 * Real.pi) : ℂ) *
    cubicAFEDiagonalMellinKernel d e p.1 (cubicAFEVerticalPoint X p.2)‖ ≤ _
  rw [norm_mul, norm_mul, hnorm]
  calc
    _ ≤ (A * ‖W (p.1 / T)‖) * ‖(1 / (2 * Real.pi) : ℂ)‖ *
        (‖cubicAFEScalar p.1 (cubicAFEVerticalPoint X p.2)‖ * cubicAFEDiagonalMellinMass d e X) := by
      gcongr
      exact cubicAFEDiagonalMellinKernel_norm_le p.1 hX hd he p.2
    _ ≤ (A * ‖W (p.1 / T)‖) * ‖(1 / (2 * Real.pi) : ℂ)‖ *
        ((C * cubicAFEVerticalGaussianMajorant X p.2) * cubicAFEDiagonalMellinMass d e X) := by
      gcongr
      · exact cubicAFEDiagonalMellinMass_nonneg d e X
      · exact hbound p.1 ht p.2
    _ = _ := by dsimp [B]; ring

/-- The original physical time integral is retained on both sides. Only
the eventually nonnegative height is converted to an indicator cutoff. -/
theorem tendsto_cubicAFEDiagonalPhysicalDoubleIntegral_height
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Tendsto (fun V : ℝ ↦ ∫ t : ℝ, cubicAFEDiagonalOuterWeight W T d e t * (1 / (2 * Real.pi) : ℂ) *
      ∫ v : ℝ in -V..V, cubicAFEDiagonalMellinKernel d e t (cubicAFEVerticalPoint X v)) atTop
      (nhds (∫ t : ℝ, cubicAFEDiagonalOuterWeight W T d e t * (1 / (2 * Real.pi) : ℂ) *
        ∫ v : ℝ, cubicAFEDiagonalMellinKernel d e t (cubicAFEVerticalPoint X v))) := by
  let F : ℝ × ℝ → ℂ := Function.uncurry (cubicAFEDiagonalPhysicalMellinKernel W T X d e)
  let S (V : ℝ) : Set (ℝ × ℝ) := {p | p.2 ∈ Ioc (-V) V}
  have hm (V : ℝ) : MeasurableSet (S V) := measurable_snd measurableSet_Ioc
  have hf : Integrable F := integrable_cubicAFEDiagonalPhysicalMellinKernel W hT hX hd he
  have hl : Tendsto (fun V : ℝ ↦ ∫ p : ℝ × ℝ, (S V).indicator F p) atTop
      (nhds (∫ p : ℝ × ℝ, F p)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun p : ℝ × ℝ ↦ ‖F p‖)
    · exact Eventually.of_forall (fun V ↦ (hf.indicator (hm V)).aestronglyMeasurable)
    · exact Eventually.of_forall (fun _V ↦ Eventually.of_forall (fun p ↦ norm_indicator_le_norm_self F p))
    · exact hf.norm
    · filter_upwards [] with p
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop |p.2|] with V hV
      exact (indicator_of_mem (show p ∈ S V from ⟨by linarith [neg_abs_le p.2], by linarith [le_abs_self p.2]⟩) F).symm
  have heq (V : ℝ) (hV : 0 ≤ V) : (∫ p : ℝ × ℝ, (S V).indicator F p) =
      ∫ t : ℝ, cubicAFEDiagonalOuterWeight W T d e t * (1 / (2 * Real.pi) : ℂ) *
        ∫ v : ℝ in -V..V, cubicAFEDiagonalMellinKernel d e t (cubicAFEVerticalPoint X v) := by
    calc
      _ = ∫ t : ℝ, ∫ v : ℝ, (S V).indicator F (t, v) := integral_prod _ (hf.indicator (hm V))
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with t
        change (∫ v : ℝ, (Ioc (-V) V).indicator (fun v ↦ F (t, v)) v) = _
        rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by linarith : -V ≤ V)]
        simpa only [F, Function.uncurry, cubicAFEDiagonalPhysicalMellinKernel] using
          intervalIntegral.integral_const_mul
            (cubicAFEDiagonalOuterWeight W T d e t * (1 / (2 * Real.pi) : ℂ))
            (fun v : ℝ ↦ cubicAFEDiagonalMellinKernel d e t (cubicAFEVerticalPoint X v))
  have hfull : (∫ p : ℝ × ℝ, F p) =
      ∫ t : ℝ, cubicAFEDiagonalOuterWeight W T d e t * (1 / (2 * Real.pi) : ℂ) *
        ∫ v : ℝ, cubicAFEDiagonalMellinKernel d e t (cubicAFEVerticalPoint X v) := by
    calc
      _ = ∫ t : ℝ, ∫ v : ℝ, F (t, v) := integral_prod _ hf
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with t
        simpa only [F, Function.uncurry, cubicAFEDiagonalPhysicalMellinKernel] using
          integral_const_mul (cubicAFEDiagonalOuterWeight W T d e t * (1 / (2 * Real.pi) : ℂ))
            (fun v : ℝ ↦ cubicAFEDiagonalMellinKernel d e t (cubicAFEVerticalPoint X v))
  rw [hfull] at hl
  apply hl.congr'
  exact (eventually_ge_atTop (0 : ℝ)).mono (fun V hV ↦ heq V hV)

noncomputable def cubicAFEDiagonalMomentVertical (W : CubicTestWeight) (T X : ℝ) : ℂ :=
  ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
    ∫ t : ℝ, cubicAFEDiagonalOuterWeight W T d e t * (1 / (2 * Real.pi) : ℂ) *
      ∫ v : ℝ, cubicAFEDiagonalMellinKernel d e t (cubicAFEVerticalPoint X v)

theorem tendsto_cubicAFEDiagonalMomentFinite_height
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) :
    Tendsto (fun V : ℝ ↦ cubicAFEDiagonalMomentFinite W T X V) atTop
      (nhds (cubicAFEDiagonalMomentVertical W T X)) := by
  simp_rw [cubicAFEDiagonalMomentFinite_eq_mellin W hT hX]
  unfold cubicAFEDiagonalMomentVertical
  apply tendsto_finsetSum
  intro d hd
  apply tendsto_finsetSum
  intro e he
  exact tendsto_cubicAFEDiagonalPhysicalDoubleIntegral_height W hT hX
    (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1

end PrimeNumberTheorem.MWKFCubic
