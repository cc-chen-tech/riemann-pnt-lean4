import PrimeNumberTheorem.MWKFCubicAFEEndpointPower

open Complex Filter MeasureTheory Set
open scoped Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Removing completion under the full physical time integral

At a fixed nonzero shift the two-endpoint majorant is integrable in space
and its actual coefficient is integrable in time. Neither depends on J.
This proves the depth limit after the height limit, at fixed shift and T.
It does not prove a joint depth/height limit or an all-shift interchange.
-/

noncomputable def cubicAFEEndpointTimeMass
    (W : CubicTestWeight) (T X : ℝ) (d e : ℕ) (t : ℝ) : ℝ :=
  ‖(cubicMollifierCoefficient T d : ℂ) * (cubicMollifierCoefficient T e : ℂ) * 2‖ *
    (Real.sqrt (d * e))⁻¹ * ‖W (t / T)‖ +
      cubicAFEPhysicalHeightMass W T (-1 / 4) d e t + cubicAFEPhysicalHeightMass W T X d e t

theorem integrable_cubicAFEEndpointTimeMass
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (d e : ℕ) :
    Integrable (cubicAFEEndpointTimeMass W T X d e) := by
  have hw : Integrable (fun t : ℝ ↦ ‖W (t / T)‖) :=
    (W.continuous.comp (continuous_id.div_const T)).norm.integrable_of_hasCompactSupport
      (W.hasCompactSupport_dilate hT).norm
  exact ((hw.const_mul _).add
    (integrable_cubicAFEPhysicalHeightMass W hT (by norm_num) (by norm_num) d e)).add
      (integrable_cubicAFEPhysicalHeightMass W hT (by linarith) (by linarith) d e)

noncomputable def cubicAFEEndpointSpatialPower (X : ℝ) (d e : ℕ) (δ : ℤ) (x : ℝ) : ℝ :=
  (cubicAFEProgressionDomain d e δ).indicator
    (fun x ↦ cubicAFEEndpointPower X (cubicAFEProgressionRealProduct d e δ x)) x

private theorem reduced_positive {d e : ℕ} (hd : 0 < d) : 0 < d / Nat.gcd d e := by
  have hh := (gcd_extraction (Nat.gcd_pos_of_pos_left e hd).ne').1
  apply Nat.pos_of_ne_zero
  intro hz
  rw [hz, mul_zero] at hh
  exact hd.ne' hh

theorem integrable_cubicAFEEndpointSpatialPower {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) {δ : ℤ} (hδ : δ ≠ 0) :
    Integrable (cubicAFEEndpointSpatialPower X d e δ) := by
  let r : ℝ := ((d / Nat.gcd d e : ℕ) : ℝ)
  let s : ℝ := ((e / Nat.gcd d e : ℕ) : ℝ)
  have hr : 0 < r := by dsimp [r]; exact_mod_cast (reduced_positive (e := e) hd)
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast (show 0 < e / Nat.gcd d e by
      simpa only [Nat.gcd_comm] using (reduced_positive (e := d) he))
  have hδr : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ
  have hprod (x : ℝ) : x * ((δ : ℝ) + r * x) / s = cubicAFEProgressionRealProduct d e δ x := by
    dsimp [r, s, cubicAFEProgressionRealProduct, cubicAFEProgressionRealSecond]
    ring
  have hdomain : {x : ℝ | 0 < x ∧ 0 < (δ : ℝ) + r * x} = cubicAFEProgressionDomain d e δ := by
    ext x
    simp only [cubicAFEProgressionDomain, r, mul_comm]
  have hi : IntegrableOn (fun x ↦ cubicAFEEndpointPower X (cubicAFEProgressionRealProduct d e δ x))
      (cubicAFEProgressionDomain d e δ) := by
    simpa only [hprod, hdomain] using integrableOn_cubicAFEEndpointPower_quadratic hX hr hs hδr
  exact hi.integrable_indicator (isOpen_cubicAFEProgressionDomain d e δ).measurableSet

noncomputable def cubicAFEUncutPhysicalKernel
    (W : CubicTestWeight) (T X : ℝ) (d e : ℕ) (δ : ℤ) (t x : ℝ) : ℂ :=
  (cubicAFEProgressionDomain d e δ).indicator
    (cubicAFEProgressionPhysicalSummandVertical W T X d e δ t) x

private theorem norm_physical_vertical_le_endpoint
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (d e : ℕ) (δ : ℤ) (t : ℝ) {x : ℝ} (hP : 0 < cubicAFEProgressionRealProduct d e δ x) :
    ‖cubicAFEProgressionPhysicalSummandVertical W T X d e δ t x‖ ≤
      cubicAFEEndpointTimeMass W T X d e t * cubicAFEEndpointPower X (cubicAFEProgressionRealProduct d e δ x) := by
  let P := cubicAFEProgressionRealProduct d e δ x
  let C := ‖(cubicMollifierCoefficient T d : ℂ) * (cubicMollifierCoefficient T e : ℂ) * 2‖ *
    (Real.sqrt (d * e))⁻¹
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hroot : ((P ^ (-1 / 2 : ℝ) : ℝ) : ℂ) = (Real.sqrt P : ℂ)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hP.le,
      ← Real.sqrt_eq_rpow, Complex.ofReal_inv]
  have hphase (u : ℝ) : ‖Complex.exp ((I * (u : ℂ)) * t)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hnorm : ‖cubicAFEProgressionPhysicalSummandVertical W T X d e δ t x‖ =
      C * ‖((P ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * cubicAFERealProductWeightVertical t X P‖ * ‖W (t / T)‖ := by
    rw [hroot]
    simp only [cubicAFEProgressionPhysicalSummandVertical, norm_mul, norm_inv,
      hphase, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), C, P]
    ring
  rw [hnorm]
  calc
    _ ≤ C * ((1 + cubicAFEWeightNormMass t (-1 / 4) + cubicAFEWeightNormMass t X) *
        cubicAFEEndpointPower X P) * ‖W (t / T)‖ := by
      gcongr
      exact norm_cubicAFEWeightedProduct_le_endpointPower t hX hP
    _ = _ := by unfold cubicAFEEndpointTimeMass cubicAFEPhysicalHeightMass; dsimp [C, P]; ring

theorem norm_cubicAFEUncutPhysicalKernel_le
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (he : 0 < e) (δ : ℤ) (p : ℝ × ℝ) :
    ‖cubicAFEUncutPhysicalKernel W T X d e δ p.1 p.2‖ ≤
      cubicAFEEndpointTimeMass W T X d e p.1 * cubicAFEEndpointSpatialPower X d e δ p.2 := by
  by_cases hx : p.2 ∈ cubicAFEProgressionDomain d e δ
  · rw [cubicAFEUncutPhysicalKernel, indicator_of_mem hx, cubicAFEEndpointSpatialPower, indicator_of_mem hx]
    exact norm_physical_vertical_le_endpoint W T hX d e δ p.1 (cubicAFEProgressionRealProduct_pos he hx)
  · rw [cubicAFEUncutPhysicalKernel, indicator_of_notMem hx, cubicAFEEndpointSpatialPower,
      indicator_of_notMem hx, norm_zero, mul_zero]

theorem tendsto_cubicAFECompletedPhysicalKernel_depth
    (W : CubicTestWeight) (T X : ℝ) {d e : ℕ} (he : 0 < e) (δ : ℤ) (p : ℝ × ℝ) :
    Tendsto (fun J : ℕ ↦ cubicAFECompletedPhysicalKernelVertical W T X d e δ J p.1 p.2) atTop
      (nhds (cubicAFEUncutPhysicalKernel W T X d e δ p.1 p.2)) := by
  by_cases hx : p.2 ∈ cubicAFEProgressionDomain d e δ
  · rw [cubicAFEUncutPhysicalKernel, indicator_of_mem hx]
    have hy : 0 < cubicAFEProgressionRealSecond d e δ p.2 :=
      (mul_pos_iff_of_pos_left hx.1).mp (cubicAFEProgressionRealProduct_pos he hx)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_cubicAFEDyadicCompletionWeight_eq_one hx.1 hy] with J hJ
    simp only [cubicAFECompletedPhysicalKernelVertical, hJ, Complex.ofReal_one, one_mul]
  · rw [cubicAFEUncutPhysicalKernel, indicator_of_notMem hx]
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall (fun J ↦ by
      change (0 : ℂ) = cubicAFECompletedPhysicalKernelVertical W T X d e δ J p.1 p.2
      rw [cubicAFECompletedPhysicalKernelVertical, cubicAFECompletionWeight_zero_outside_domain d e δ J hx,
        Complex.ofReal_zero, zero_mul])

theorem stronglyMeasurable_cubicAFEUncutPhysicalKernel
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (he : 0 < e) (δ : ℤ) :
    StronglyMeasurable (Function.uncurry (cubicAFEUncutPhysicalKernel W T X d e δ)) := by
  apply stronglyMeasurable_of_tendsto (atTop : Filter ℕ)
    (fun J ↦ stronglyMeasurable_cubicAFECompletedPhysicalKernelVertical W T hX d e δ J)
  exact tendsto_pi_nhds.mpr (tendsto_cubicAFECompletedPhysicalKernel_depth W T X he δ)

theorem integrable_cubicAFEUncutPhysicalKernel
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) {δ : ℤ} (hδ : δ ≠ 0) :
    Integrable (Function.uncurry (cubicAFEUncutPhysicalKernel W T X d e δ)) :=
  ((integrable_cubicAFEEndpointTimeMass W hT hX d e).mul_prod
    (integrable_cubicAFEEndpointSpatialPower hX hd he hδ)).mono'
      (stronglyMeasurable_cubicAFEUncutPhysicalKernel W T hX he δ).aestronglyMeasurable
      (Eventually.of_forall (norm_cubicAFEUncutPhysicalKernel_le W T hX he δ))

theorem norm_cubicAFECompletedPhysicalKernelVertical_le_uncut
    (W : CubicTestWeight) (T X : ℝ) (d e : ℕ) (δ : ℤ) (J : ℕ) (p : ℝ × ℝ) :
    ‖cubicAFECompletedPhysicalKernelVertical W T X d e δ J p.1 p.2‖ ≤
      ‖cubicAFEUncutPhysicalKernel W T X d e δ p.1 p.2‖ := by
  by_cases hx : p.2 ∈ cubicAFEProgressionDomain d e δ
  · rw [cubicAFEUncutPhysicalKernel, indicator_of_mem hx, cubicAFECompletedPhysicalKernelVertical,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (cubicAFECompletionWeight_nonneg _ _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (cubicAFECompletionWeight_le_one _ _ _)
  · rw [cubicAFEUncutPhysicalKernel, indicator_of_notMem hx, cubicAFECompletedPhysicalKernelVertical,
      cubicAFECompletionWeight_zero_outside_domain d e δ J hx, Complex.ofReal_zero, zero_mul]

/-- The completion depth can now be removed after the full physical time
integral, at each fixed nonzero shift. The right side uses the actual domain. -/
theorem tendsto_cubicAFECompletedPhysicalDoubleIntegral_depth
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) {δ : ℤ} (hδ : δ ≠ 0) :
    Tendsto (fun J : ℕ ↦ ∫ t : ℝ, ∫ x : ℝ,
      cubicAFECompletedPhysicalKernelVertical W T X d e δ J t x) atTop
      (nhds (∫ t : ℝ, ∫ x in cubicAFEProgressionDomain d e δ,
        cubicAFEProgressionPhysicalSummandVertical W T X d e δ t x)) := by
  have hu : Integrable (fun p : ℝ × ℝ ↦ cubicAFEUncutPhysicalKernel W T X d e δ p.1 p.2) :=
    integrable_cubicAFEUncutPhysicalKernel W hT hX hd he hδ
  have hc (J : ℕ) : Integrable (fun p : ℝ × ℝ ↦
      cubicAFECompletedPhysicalKernelVertical W T X d e δ J p.1 p.2) :=
    integrable_cubicAFECompletedPhysicalKernelVertical W hT hX d e δ J
  have hl : Tendsto (fun J : ℕ ↦ ∫ p : ℝ × ℝ,
      cubicAFECompletedPhysicalKernelVertical W T X d e δ J p.1 p.2) atTop
      (nhds (∫ p : ℝ × ℝ, cubicAFEUncutPhysicalKernel W T X d e δ p.1 p.2)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun p : ℝ × ℝ ↦ ‖cubicAFEUncutPhysicalKernel W T X d e δ p.1 p.2‖)
    · exact Eventually.of_forall (fun J ↦ (hc J).aestronglyMeasurable)
    · exact Eventually.of_forall (fun J ↦ Eventually.of_forall
        (norm_cubicAFECompletedPhysicalKernelVertical_le_uncut W T X d e δ J))
    · exact hu.norm
    · filter_upwards [] with p
      exact tendsto_cubicAFECompletedPhysicalKernel_depth W T X he δ p
  have hcEq (J : ℕ) : (∫ p : ℝ × ℝ,
      cubicAFECompletedPhysicalKernelVertical W T X d e δ J p.1 p.2) =
      ∫ t : ℝ, ∫ x : ℝ, cubicAFECompletedPhysicalKernelVertical W T X d e δ J t x := integral_prod _ (hc J)
  have huEq : (∫ p : ℝ × ℝ, cubicAFEUncutPhysicalKernel W T X d e δ p.1 p.2) =
      ∫ t : ℝ, ∫ x in cubicAFEProgressionDomain d e δ,
        cubicAFEProgressionPhysicalSummandVertical W T X d e δ t x := by
    calc
      _ = ∫ t : ℝ, ∫ x : ℝ, cubicAFEUncutPhysicalKernel W T X d e δ t x := integral_prod _ hu
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun t ↦ integral_indicator (isOpen_cubicAFEProgressionDomain d e δ).measurableSet)
  simpa only [hcEq, huEq] using hl

end PrimeNumberTheorem.MWKFCubic
