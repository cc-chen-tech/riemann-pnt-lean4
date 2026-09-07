import PrimeNumberTheorem.MWKFCubicAFECompletedLattice
import PrimeNumberTheorem.MWKFCubicAFECompletedTime
import Mathlib.Analysis.Normed.Group.Tannery

open Complex Filter MeasureTheory Set
open scoped Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# All-shift height limit at fixed completion depth

The actual physical kernels are bounded by M(t) H_J(x) H_J(y_delta(x)).
The translation-uniform lattice estimate makes the integrals of this
majorant summable over all shifts, uniformly in the Mellin height V.
Tannery then applies to the original double integrals and dyadic zero modes.
The depth J and physical parameters remain fixed throughout.
-/

noncomputable def cubicAFECompletedShiftMajorant
    (W : CubicTestWeight) (T X : ℝ) (d e : ℕ) (J : ℕ) (δ : ℤ) (p : ℝ × ℝ) : ℝ :=
  (cubicAFEPhysicalHeightMass W T X d e p.1 * cubicAFECompletedHalfLinePower X J p.2) *
    cubicAFECompletedHalfLinePower X J (cubicAFEProgressionRealSecond d e δ p.2)

theorem cubicAFECompletedShiftMajorant_nonneg
    (W : CubicTestWeight) (T X : ℝ) (d e : ℕ) (J : ℕ) (δ : ℤ) (p : ℝ × ℝ) :
    0 ≤ cubicAFECompletedShiftMajorant W T X d e J δ p :=
  mul_nonneg (mul_nonneg (cubicAFEPhysicalHeightMass_nonneg W T X d e p.1)
    (cubicAFECompletedHalfLinePower_nonneg X J p.2)) (cubicAFECompletedHalfLinePower_nonneg X J _)

theorem integrable_cubicAFECompletedShiftMajorant
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (d e : ℕ) (J : ℕ) (δ : ℤ) :
    Integrable (cubicAFECompletedShiftMajorant W T X d e J δ) := by
  have hM : Continuous (cubicAFEPhysicalHeightMass W T X d e) :=
    (continuous_const.mul (continuous_cubicAFEWeightNormMass (by linarith) (by linarith))).mul
      (W.continuous.comp (continuous_id.div_const T)).norm
  have hy : Continuous (fun p : ℝ × ℝ ↦ cubicAFEProgressionRealSecond d e δ p.2) := by
    unfold cubicAFEProgressionRealSecond
    fun_prop
  have hm : Measurable (cubicAFECompletedShiftMajorant W T X d e J δ) :=
    ((hM.measurable.comp measurable_fst).mul
      ((measurable_cubicAFECompletedHalfLinePower X J).comp measurable_snd)).mul
        ((measurable_cubicAFECompletedHalfLinePower X J).comp hy.measurable)
  have hb : Integrable (fun p : ℝ × ℝ ↦
      (cubicAFEPhysicalHeightMass W T X d e p.1 * cubicAFECompletedHalfLinePower X J p.2) *
        cubicAFECompletionLowerEndpoint J ^ (-X - 1 / 2)) :=
    ((integrable_cubicAFEPhysicalHeightMass W hT (by linarith) (by linarith) d e).mul_prod
      (integrable_cubicAFECompletedHalfLinePower hX J)).mul_const _
  apply hb.mono' hm.aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_of_nonneg (cubicAFECompletedShiftMajorant_nonneg W T X d e J δ p)]
  exact mul_le_mul_of_nonneg_left (cubicAFECompletedHalfLinePower_le_endpoint hX J _)
    (mul_nonneg (cubicAFEPhysicalHeightMass_nonneg W T X d e p.1)
      (cubicAFECompletedHalfLinePower_nonneg X J p.2))

private theorem reduced_modulus_pos {d e : ℕ} (he : 0 < e) :
    (0 : ℝ) < ((e / Nat.gcd d e : ℕ) : ℝ) := by
  have hp : 0 < e / Nat.gcd d e := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hh := (gcd_extraction (Nat.gcd_pos_of_pos_right d he).ne').2.1
    rw [hz, mul_zero] at hh
    exact he.ne' hh
  exact_mod_cast hp

/-- Integrals of the actual nonnegative majorant are summable over every
integer shift. No height parameter occurs in this series. -/
theorem summable_integral_cubicAFECompletedShiftMajorant
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (he : 0 < e) (J : ℕ) :
    Summable (fun δ : ℤ ↦ ∫ p : ℝ × ℝ, cubicAFECompletedShiftMajorant W T X d e J δ p) := by
  let F := cubicAFECompletedShiftMajorant W T X d e J
  let s : ℝ := ((e / Nat.gcd d e : ℕ) : ℝ)
  let C := cubicAFECompletedLatticeConstant X J s
  have hspos : 0 < s := reduced_modulus_pos he
  have hs (p : ℝ × ℝ) : Summable (fun δ ↦ F δ p) :=
    (summable_cubicAFECompletedLatticePower hX hspos J
      (p.2 * ((d / Nat.gcd d e : ℕ) : ℝ))).mul_left
        (cubicAFEPhysicalHeightMass W T X d e p.1 * cubicAFECompletedHalfLinePower X J p.2)
  have hf (δ : ℤ) : AEStronglyMeasurable (F δ) volume :=
    (integrable_cubicAFECompletedShiftMajorant W hT hX d e J δ).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ ∑' δ, F δ p) volume := by
    apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ℤ))
      (f := fun K p ↦ ∑ δ ∈ K, F δ p)
    · intro K
      exact Finset.aestronglyMeasurable_fun_sum K (fun δ _ ↦ hf δ)
    · exact Eventually.of_forall (fun p ↦ (hs p).hasSum)
  have hb : Integrable (fun p : ℝ × ℝ ↦
      (cubicAFEPhysicalHeightMass W T X d e p.1 * cubicAFECompletedHalfLinePower X J p.2) * C) :=
    ((integrable_cubicAFEPhysicalHeightMass W hT (by linarith) (by linarith) d e).mul_prod
      (integrable_cubicAFECompletedHalfLinePower hX J)).mul_const C
  have htotal : Integrable (fun p : ℝ × ℝ ↦ ∑' δ, F δ p) := by
    apply hb.mono' hmeas
    filter_upwards [] with p
    rw [Real.norm_of_nonneg (tsum_nonneg (fun δ ↦ cubicAFECompletedShiftMajorant_nonneg W T X d e J δ p))]
    calc
      _ = (cubicAFEPhysicalHeightMass W T X d e p.1 * cubicAFECompletedHalfLinePower X J p.2) *
          ∑' δ : ℤ, cubicAFECompletedHalfLinePower X J (cubicAFEProgressionRealSecond d e δ p.2) := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (tsum_cubicAFECompletedLatticePower_le hX hspos J (p.2 * ((d / Nat.gcd d e : ℕ) : ℝ)))
        (mul_nonneg (cubicAFEPhysicalHeightMass_nonneg W T X d e p.1)
          (cubicAFECompletedHalfLinePower_nonneg X J p.2))
  exact (hasSum_integral_of_dominated_convergence (bound := F) hf
    (fun δ ↦ Eventually.of_forall (fun p ↦ by
      rw [Real.norm_of_nonneg (cubicAFECompletedShiftMajorant_nonneg W T X d e J δ p)]))
    (Eventually.of_forall hs) htotal (Eventually.of_forall (fun p ↦ (hs p).hasSum))).summable

private theorem norm_completed_finite_le_shiftMajorant
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (d e : ℕ) (J : ℕ) (δ : ℤ) (p : ℝ × ℝ) :
    ‖cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J p.1 p.2‖ ≤
      cubicAFECompletedShiftMajorant W T X d e J δ p := by
  let x := p.2
  let y := cubicAFEProgressionRealSecond d e δ x
  let B := cubicAFEDyadicCompletionWeight J x y
  have hB : 0 ≤ B := cubicAFECompletionWeight_nonneg J x y
  by_cases hz : B = 0
  · change ‖(B : ℂ) * _‖ ≤ _
    rw [hz, Complex.ofReal_zero, zero_mul, norm_zero]
    exact cubicAFECompletedShiftMajorant_nonneg W T X d e J δ p
  have hx : cubicAFECompletionLowerEndpoint J < x := by
    by_contra hn
    exact hz (cubicAFECompletionWeight_zero_of_first_le J (le_of_not_gt hn) y)
  have hy : cubicAFECompletionLowerEndpoint J < y := by
    by_contra hn
    exact hz (cubicAFECompletionWeight_zero_of_second_le J x (le_of_not_gt hn))
  have hx0 : 0 < x := (cubicAFECompletionLowerEndpoint_pos J).trans hx
  have hy0 : 0 < y := (cubicAFECompletionLowerEndpoint_pos J).trans hy
  have hP : 0 < cubicAFEProgressionRealProduct d e δ x := mul_pos hx0 hy0
  have hmass : cubicAFEPhysicalTimeEnvelope W T X V d e p.1 ≤ cubicAFEPhysicalHeightMass W T X d e p.1 := by
    unfold cubicAFEPhysicalTimeEnvelope cubicAFEPhysicalHeightMass
    gcongr
    exact cubicAFEWeightEnvelope_le_normMass p.1 (by linarith) (by linarith) V
  have hk := (norm_cubicAFEProgressionPhysicalSummand_le_envelope W T X V d e δ p.1 hP).trans
    (mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg hP.le _))
  change ‖(B : ℂ) * _‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hB]
  calc
    _ ≤ B * (cubicAFEPhysicalHeightMass W T X d e p.1 * (x * y) ^ (-X - 1 / 2)) :=
      mul_le_mul_of_nonneg_left hk hB
    _ ≤ cubicAFEPhysicalHeightMass W T X d e p.1 * (x * y) ^ (-X - 1 / 2) :=
      mul_le_of_le_one_left (mul_nonneg (cubicAFEPhysicalHeightMass_nonneg W T X d e p.1)
        (Real.rpow_nonneg hP.le _)) (cubicAFECompletionWeight_le_one J x y)
    _ = _ := by
      rw [Real.mul_rpow hx0.le hy0.le, cubicAFECompletedShiftMajorant,
        cubicAFECompletedHalfLinePower, indicator_of_mem (show x ∈ Ioi _ from hx),
        cubicAFECompletedHalfLinePower, indicator_of_mem (show y ∈ Ioi _ from hy)]
      ring

private theorem norm_completed_vertical_le_shiftMajorant
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (d e : ℕ) (J : ℕ) (δ : ℤ) (p : ℝ × ℝ) :
    ‖cubicAFECompletedPhysicalKernelVertical W T X d e δ J p.1 p.2‖ ≤
      cubicAFECompletedShiftMajorant W T X d e J δ p :=
  le_of_tendsto (tendsto_cubicAFECompletedPhysicalSummand_height W T hX d e δ p.1 J p.2).norm
    (Eventually.of_forall (fun V ↦ norm_completed_finite_le_shiftMajorant W T hX V d e J δ p))

theorem norm_integral_cubicAFECompletedKernel_le_shiftMajorant
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (d e : ℕ) (J : ℕ) (δ : ℤ) :
    ‖∫ t : ℝ, ∫ x : ℝ, cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J t x‖ ≤
      ∫ p : ℝ × ℝ, cubicAFECompletedShiftMajorant W T X d e J δ p := by
  have hi := integrable_cubicAFECompletedPhysicalKernelFinite W hT hX V d e δ J
  calc
    _ = ‖∫ p : ℝ × ℝ, cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J p.1 p.2‖ :=
      congrArg norm (integral_prod _ hi).symm
    _ ≤ ∫ p : ℝ × ℝ, ‖cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J p.1 p.2‖ :=
      norm_integral_le_integral_norm _
    _ ≤ _ := integral_mono hi.norm (integrable_cubicAFECompletedShiftMajorant W hT hX d e J δ)
      (norm_completed_finite_le_shiftMajorant W T hX V d e J δ)

theorem summable_integral_norm_cubicAFECompletedKernelVertical
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (he : 0 < e) (J : ℕ) :
    Summable (fun δ : ℤ ↦ ∫ p : ℝ × ℝ,
      ‖cubicAFECompletedPhysicalKernelVertical W T X d e δ J p.1 p.2‖) := by
  apply Summable.of_nonneg_of_le (fun δ ↦ integral_nonneg (fun p ↦ norm_nonneg _))
    (fun δ ↦ integral_mono (integrable_cubicAFECompletedPhysicalKernelVertical W hT hX d e δ J).norm
      (integrable_cubicAFECompletedShiftMajorant W hT hX d e J δ)
      (norm_completed_vertical_le_shiftMajorant W T hX d e J δ))
    (summable_integral_cubicAFECompletedShiftMajorant W hT hX he J)

/-- The entire nonzero signed-shift series has its own height limit, at
fixed J. This does not use cancellation with the nonzero Poisson modes. -/
theorem tendsto_cubicAFECompletedShiftIntegral_height
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (he : 0 < e) (J : ℕ) :
    Tendsto (fun V : ℝ ↦ ∑' δ : {δ : ℤ // δ ≠ 0}, ∫ t : ℝ, ∫ x : ℝ,
      cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ.val J t x) atTop
      (nhds (∑' δ : {δ : ℤ // δ ≠ 0}, ∫ t : ℝ, ∫ x : ℝ,
        cubicAFECompletedPhysicalKernelVertical W T X d e δ.val J t x)) := by
  exact tendsto_tsum_of_dominated_convergence
    ((summable_integral_cubicAFECompletedShiftMajorant W hT hX he J).subtype _)
    (fun δ ↦ tendsto_cubicAFECompletedPhysicalDoubleIntegral_height W hT hX d e δ.val J)
    (Eventually.of_forall (fun V δ ↦ norm_integral_cubicAFECompletedKernel_le_shiftMajorant W hT hX V d e J δ.val))

/-- Every original completed dyadic zero mode is retained. Dyadic sums
are identified with their physical integrals before the height limit;
the exact inverse reduced modulus is unchanged. -/
theorem tendsto_cubicAFECompletedZeroMode_allShift_height
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) (J : ℕ) :
    Tendsto (fun V : ℝ ↦ ∑' δ : {δ : ℤ // δ ≠ 0}, ∑' jk : ℕ × ℕ,
      cubicAFECompletedZeroModeBox (d := d) W T X V he δ.val J jk) atTop
      (nhds ((((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' δ : {δ : ℤ // δ ≠ 0}, ∫ t : ℝ, ∫ x : ℝ,
        cubicAFECompletedPhysicalKernelVertical W T X d e δ.val J t x)) := by
  have heq (V : ℝ) : (∑' δ : {δ : ℤ // δ ≠ 0}, ∑' jk : ℕ × ℕ,
      cubicAFECompletedZeroModeBox (d := d) W T X V he δ.val J jk) =
      (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' δ : {δ : ℤ // δ ≠ 0}, ∫ t : ℝ, ∫ x : ℝ,
        cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ.val J t x := by
    simp_rw [(fun δ ↦ (hasSum_cubicAFECompletedZeroModeBox_physical W hT hX V hd he δ J).tsum_eq)]
    exact tsum_mul_left
  simpa only [heq] using (tendsto_cubicAFECompletedShiftIntegral_height W hT hX he J).const_mul
    (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹)

end PrimeNumberTheorem.MWKFCubic
