import PrimeNumberTheorem.MWKFCubicAFECompletedPower
import PrimeNumberTheorem.MWKFCubicAFEPhysicalEndpoint

open Complex Filter MeasureTheory Set
open scoped Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Fixed-depth physical height limit under the spatial integral

The dominating function is uniform in every real height V, but retains its
explicit completion-depth factor. The height limit is taken first, at fixed
depth and time. Removing the depth afterwards uses the separate nonzero-shift
endpoint theorem; no joint limit, time integral or shift sum is interchanged.
-/

noncomputable def cubicAFEPhysicalHeightMass
    (W : CubicTestWeight) (T X : ℝ) (d e : ℕ) (t : ℝ) : ℝ :=
  ‖(cubicMollifierCoefficient T d : ℂ) * (cubicMollifierCoefficient T e : ℂ) * 2‖ *
    (Real.sqrt (d * e))⁻¹ * cubicAFEWeightNormMass t X * ‖W (t / T)‖

theorem cubicAFEPhysicalHeightMass_nonneg
    (W : CubicTestWeight) (T X : ℝ) (d e : ℕ) (t : ℝ) :
    0 ≤ cubicAFEPhysicalHeightMass W T X d e t := by
  unfold cubicAFEPhysicalHeightMass
  exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _)
    (inv_nonneg.mpr (Real.sqrt_nonneg _))) (cubicAFEWeightNormMass_nonneg t X))
      (norm_nonneg _)

private theorem physical_envelope_le_heightMass
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (d e : ℕ) (t : ℝ) :
    cubicAFEPhysicalTimeEnvelope W T X V d e t ≤ cubicAFEPhysicalHeightMass W T X d e t := by
  unfold cubicAFEPhysicalTimeEnvelope cubicAFEPhysicalHeightMass
  gcongr
  exact cubicAFEWeightEnvelope_le_normMass t (by linarith) (by linarith) V

/-- Actual completed kernel, with a majorant independent of V. The epsilon
factor is not absorbed into a constant uniform in J. No nonzero-shift
hypothesis is needed until the subsequent removal of the completion. -/
theorem norm_cubicAFECompletedPhysicalSummand_le_heightMass
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (d e : ℕ) (δ : ℤ) (t : ℝ) (J : ℕ) (x : ℝ) :
    ‖(cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) : ℂ) *
      cubicAFEProgressionPhysicalSummand W T X V d e δ t x‖ ≤
      (cubicAFEPhysicalHeightMass W T X d e t *
        cubicAFECompletionLowerEndpoint J ^ (-X - 1 / 2)) * cubicAFECompletedHalfLinePower X J x := by
  let y := cubicAFEProgressionRealSecond d e δ x
  let B := cubicAFEDyadicCompletionWeight J x y
  have hB : 0 ≤ B := cubicAFECompletionWeight_nonneg J x y
  have hM := cubicAFEPhysicalHeightMass_nonneg W T X d e t
  have he := cubicAFECompletionLowerEndpoint_pos J
  by_cases hz : B = 0
  · change ‖(B : ℂ) * _‖ ≤ _
    rw [hz, Complex.ofReal_zero, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg hM (Real.rpow_nonneg he.le _))
      (cubicAFECompletedHalfLinePower_nonneg X J x)
  have hx : cubicAFECompletionLowerEndpoint J < x := by
    by_contra hn
    exact hz (cubicAFECompletionWeight_zero_of_first_le J (le_of_not_gt hn) y)
  have hy : cubicAFECompletionLowerEndpoint J < y := by
    by_contra hn
    exact hz (cubicAFECompletionWeight_zero_of_second_le J x (le_of_not_gt hn))
  have hP : 0 < cubicAFEProgressionRealProduct d e δ x := mul_pos (he.trans hx) (he.trans hy)
  have hk := (norm_cubicAFEProgressionPhysicalSummand_le_envelope W T X V d e δ t hP).trans
    (mul_le_mul_of_nonneg_right (physical_envelope_le_heightMass W T hX V d e t)
      (Real.rpow_nonneg hP.le _))
  change ‖(B : ℂ) * _‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hB]
  calc
    _ ≤ B * (cubicAFEPhysicalHeightMass W T X d e t *
        cubicAFEProgressionRealProduct d e δ x ^ (-X - 1 / 2)) :=
      mul_le_mul_of_nonneg_left hk hB
    _ = cubicAFEPhysicalHeightMass W T X d e t * (B * (x * y) ^ (-X - 1 / 2)) := by
      change B * (_ * (x * y) ^ _) = _
      ring
    _ ≤ cubicAFEPhysicalHeightMass W T X d e t *
        (cubicAFECompletionLowerEndpoint J ^ (-X - 1 / 2) * cubicAFECompletedHalfLinePower X J x) :=
      mul_le_mul_of_nonneg_left (cubicAFECompletionWeight_mul_product_rpow_le hX J x y) hM
    _ = _ := by ring

theorem measurable_cubicAFEProgressionPhysicalSummand
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (d e : ℕ) (δ : ℤ) (t : ℝ) :
    Measurable (cubicAFEProgressionPhysicalSummand W T X V d e δ t) := by
  have hP : Continuous (cubicAFEProgressionRealProduct d e δ) := by
    unfold cubicAFEProgressionRealProduct cubicAFEProgressionRealSecond
    fun_prop
  have hw : Measurable (fun x ↦ cubicAFERealProductWeightFinite t X V
      (cubicAFEProgressionRealProduct d e δ x)) :=
    (differentiable_cubicAFELogProductWeightFinite t X V hX).continuous.measurable.comp
      (Complex.measurable_ofReal.comp (Real.measurable_log.comp hP.measurable))
  unfold cubicAFEProgressionPhysicalSummand
  fun_prop

theorem tendsto_cubicAFECompletedPhysicalSummand_height
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (d e : ℕ) (δ : ℤ) (t : ℝ) (J : ℕ) (x : ℝ) :
    Tendsto (fun V : ℝ ↦
      (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) : ℂ) *
        cubicAFEProgressionPhysicalSummand W T X V d e δ t x) atTop
      (nhds ((cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) : ℂ) *
        cubicAFEProgressionPhysicalSummandVertical W T X d e δ t x)) := by
  let y := cubicAFEProgressionRealSecond d e δ x
  by_cases hz : cubicAFEDyadicCompletionWeight J x y = 0
  · simp only [show cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) = 0
      from hz, Complex.ofReal_zero, zero_mul]
    exact tendsto_const_nhds
  have hx : cubicAFECompletionLowerEndpoint J < x := by
    by_contra hn
    exact hz (cubicAFECompletionWeight_zero_of_first_le J (le_of_not_gt hn) y)
  have hy : cubicAFECompletionLowerEndpoint J < y := by
    by_contra hn
    exact hz (cubicAFECompletionWeight_zero_of_second_le J x (le_of_not_gt hn))
  have hP : 0 < cubicAFEProgressionRealProduct d e δ x :=
    mul_pos ((cubicAFECompletionLowerEndpoint_pos J).trans hx)
      ((cubicAFECompletionLowerEndpoint_pos J).trans hy)
  have hw := tendsto_cubicAFERealProductWeightFinite t (X := X) (by linarith) (by linarith) hP
  exact (((hw.const_mul _).const_mul _).mul_const _).const_mul _

private theorem continuous_completion (d e : ℕ) (δ : ℤ) (J : ℕ) :
    Continuous (fun x ↦
      (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) : ℂ)) := by
  have hc := contDiff_cubicAFEDyadicLowerWeight.continuous
  unfold cubicAFEDyadicCompletionWeight cubicAFEProgressionRealSecond
  fun_prop

/-- Full spatial integral height limit, at fixed completion depth. -/
theorem tendsto_cubicAFECompletedPhysicalIntegral_height
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (d e : ℕ) (δ : ℤ) (t : ℝ) (J : ℕ) :
    Tendsto (fun V : ℝ ↦ ∫ x : ℝ,
      (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) : ℂ) *
        cubicAFEProgressionPhysicalSummand W T X V d e δ t x) atTop
      (nhds (∫ x : ℝ,
        (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) : ℂ) *
          cubicAFEProgressionPhysicalSummandVertical W T X d e δ t x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ (cubicAFEPhysicalHeightMass W T X d e t *
      cubicAFECompletionLowerEndpoint J ^ (-X - 1 / 2)) * cubicAFECompletedHalfLinePower X J x)
  · exact Eventually.of_forall (fun V ↦ (continuous_completion d e δ J).aestronglyMeasurable.mul
      (measurable_cubicAFEProgressionPhysicalSummand W T hX V d e δ t).aestronglyMeasurable)
  · exact Eventually.of_forall (fun V ↦ Eventually.of_forall
      (norm_cubicAFECompletedPhysicalSummand_le_heightMass W T hX V d e δ t J))
  · exact (integrable_cubicAFECompletedHalfLinePower hX J).const_mul _
  · exact Eventually.of_forall (tendsto_cubicAFECompletedPhysicalSummand_height W T hX d e δ t J)

theorem cubicAFECompletionWeight_zero_outside_domain (d e : ℕ) (δ : ℤ) (J : ℕ) {x : ℝ}
    (hx : x ∉ cubicAFEProgressionDomain d e δ) :
    cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) = 0 := by
  by_cases hp : 0 < x
  · have hn : (δ : ℝ) + x * ((d / Nat.gcd d e : ℕ) : ℝ) ≤ 0 := by
      by_contra hh
      exact hx ⟨hp, lt_of_not_ge hh⟩
    have hy : cubicAFEProgressionRealSecond d e δ x ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hn (Nat.cast_nonneg _)
    exact cubicAFECompletionWeight_zero_of_second_le J x
      (hy.trans (cubicAFECompletionLowerEndpoint_pos J).le)
  · exact cubicAFECompletionWeight_zero_of_first_le J
      ((le_of_not_gt hp).trans (cubicAFECompletionLowerEndpoint_pos J).le) _

/-- After taking the height limit at each J, the full-line completed spatial
integral converges to the uncompleted integral over the physical domain. -/
theorem tendsto_cubicAFECompletedPhysicalIntegral_wholeLine
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) {δ : ℤ} (hδ : δ ≠ 0) (t : ℝ) :
    Tendsto (fun J : ℕ ↦ ∫ x : ℝ,
      (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) : ℂ) *
        cubicAFEProgressionPhysicalSummandVertical W T X d e δ t x) atTop
      (nhds (∫ x in cubicAFEProgressionDomain d e δ,
        cubicAFEProgressionPhysicalSummandVertical W T X d e δ t x)) := by
  have heq (J : ℕ) : (∫ x : ℝ,
      (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) : ℂ) *
        cubicAFEProgressionPhysicalSummandVertical W T X d e δ t x) =
      ∫ x in cubicAFEProgressionDomain d e δ,
        (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) : ℂ) *
          cubicAFEProgressionPhysicalSummandVertical W T X d e δ t x := by
    rw [← integral_indicator (isOpen_cubicAFEProgressionDomain d e δ).measurableSet]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ cubicAFEProgressionDomain d e δ
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, cubicAFECompletionWeight_zero_outside_domain d e δ J hx,
        Complex.ofReal_zero, zero_mul]
  simpa only [heq] using tendsto_cubicAFECompletedPhysicalIntegral W T hX hd he hδ t

end PrimeNumberTheorem.MWKFCubic
