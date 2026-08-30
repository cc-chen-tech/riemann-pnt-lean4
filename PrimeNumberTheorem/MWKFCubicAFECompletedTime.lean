import PrimeNumberTheorem.MWKFCubicAFEScalarTime
import PrimeNumberTheorem.MWKFCubicAFECompletedMoment

open Complex Filter MeasureTheory Set
open scoped Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The height limit of the actual completed physical double integral

At fixed completion depth and fixed shift, the majorant is integrable in
both physical variables and independent of the Mellin height. The original
completed zero-mode series is identified with this double integral before
taking the limit. No summation over all shifts, moving-depth limit or
T-uniform asymptotic bound is asserted.
-/

noncomputable def cubicAFECompletedPhysicalKernelVertical
    (W : CubicTestWeight) (T X : ℝ) (d e : ℕ) (δ : ℤ) (J : ℕ) (t x : ℝ) : ℂ :=
  (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) : ℂ) *
    cubicAFEProgressionPhysicalSummandVertical W T X d e δ t x

noncomputable def cubicAFECompletedPhysicalMajorant
    (W : CubicTestWeight) (T X : ℝ) (d e : ℕ) (J : ℕ) (p : ℝ × ℝ) : ℝ :=
  (cubicAFEPhysicalHeightMass W T X d e p.1 *
    cubicAFECompletionLowerEndpoint J ^ (-X - 1 / 2)) * cubicAFECompletedHalfLinePower X J p.2

theorem integrable_cubicAFECompletedPhysicalMajorant
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (d e : ℕ) (J : ℕ) : Integrable (cubicAFECompletedPhysicalMajorant W T X d e J) :=
  ((integrable_cubicAFEPhysicalHeightMass W hT (by linarith) (by linarith) d e).mul_const
    (cubicAFECompletionLowerEndpoint J ^ (-X - 1 / 2))).mul_prod
      (integrable_cubicAFECompletedHalfLinePower hX J)

private theorem measurable_real_product_weight_joint {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    Measurable (fun p : ℝ × ℝ ↦ cubicAFERealProductWeightFinite p.1 X V p.2) := by
  unfold cubicAFERealProductWeightFinite
  have harg : Measurable (fun p : ℝ × ℝ ↦ (p.1, (Real.log p.2 : ℂ))) :=
    measurable_fst.prodMk (Complex.measurable_ofReal.comp (Real.measurable_log.comp measurable_snd))
  have hbase : Measurable (fun p : ℝ × ℂ ↦ cubicAFELogProductWeightFinite p.1 X V p.2) :=
    (continuous_cubicAFELogProductWeightFinite_joint hX V).measurable
  simpa only [Function.comp_def] using hbase.comp harg

theorem measurable_cubicAFEProgressionPhysicalSummand_joint
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (d e : ℕ) (δ : ℤ) :
    Measurable (fun p : ℝ × ℝ ↦ cubicAFEProgressionPhysicalSummand W T X V d e δ p.1 p.2) := by
  have hP : Continuous (fun p : ℝ × ℝ ↦ cubicAFEProgressionRealProduct d e δ p.2) := by
    unfold cubicAFEProgressionRealProduct cubicAFEProgressionRealSecond
    fun_prop
  have hw : Measurable (fun p : ℝ × ℝ ↦ cubicAFERealProductWeightFinite p.1 X V
      (cubicAFEProgressionRealProduct d e δ p.2)) := by
    simpa only [Function.comp_def] using (measurable_real_product_weight_joint hX V).comp
      (measurable_fst.prodMk hP.measurable)
  have hsqrt : Measurable (fun p : ℝ × ℝ ↦
      (Real.sqrt (cubicAFEProgressionRealProduct d e δ p.2) : ℂ)⁻¹) :=
    (Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hP.measurable)).inv
  have hphase : Measurable (fun p : ℝ × ℝ ↦ Complex.exp ((I *
      (Real.log (1 + (δ : ℝ) / (p.2 * ((d / Nat.gcd d e : ℕ) : ℝ))) : ℂ)) * p.1)) := by
    fun_prop
  have hW : Measurable (fun p : ℝ × ℝ ↦ (W (p.1 / T) : ℂ)) :=
    Complex.measurable_ofReal.comp (W.continuous.measurable.comp (measurable_fst.div_const T))
  have hcoef : Measurable (fun _p : ℝ × ℝ ↦
      (cubicMollifierCoefficient T d : ℂ) * (cubicMollifierCoefficient T e : ℂ) * 2) := measurable_const
  have hscale : Measurable (fun _p : ℝ × ℝ ↦ (Real.sqrt (d * e) : ℂ)⁻¹) := measurable_const
  unfold cubicAFEProgressionPhysicalSummand
  exact (hcoef.mul (((hsqrt.mul hscale).mul hphase).mul hw)).mul hW

private theorem measurable_completed_finite
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (d e : ℕ) (δ : ℤ) (J : ℕ) :
    Measurable (Function.uncurry (cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J)) := by
  have hB : Continuous (fun p : ℝ × ℝ ↦
      (cubicAFEDyadicCompletionWeight J p.2 (cubicAFEProgressionRealSecond d e δ p.2) : ℂ)) := by
    have hc := contDiff_cubicAFEDyadicLowerWeight.continuous
    unfold cubicAFEDyadicCompletionWeight cubicAFEProgressionRealSecond
    fun_prop
  exact hB.measurable.mul (measurable_cubicAFEProgressionPhysicalSummand_joint W T hX V d e δ)

theorem integrable_cubicAFECompletedPhysicalKernelFinite
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (d e : ℕ) (δ : ℤ) (J : ℕ) :
    Integrable (Function.uncurry (cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J)) :=
  (integrable_cubicAFECompletedPhysicalMajorant W hT hX d e J).mono'
    (measurable_completed_finite W T hX V d e δ J).aestronglyMeasurable
    (Eventually.of_forall (fun p ↦
      norm_cubicAFECompletedPhysicalSummand_le_heightMass W T hX V d e δ p.1 J p.2))

theorem stronglyMeasurable_cubicAFECompletedPhysicalKernelVertical
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (d e : ℕ) (δ : ℤ) (J : ℕ) :
    StronglyMeasurable (Function.uncurry (cubicAFECompletedPhysicalKernelVertical W T X d e δ J)) := by
  apply stronglyMeasurable_of_tendsto (atTop : Filter ℝ)
    (fun V ↦ (measurable_completed_finite W T hX V d e δ J).stronglyMeasurable)
  exact tendsto_pi_nhds.mpr (fun p ↦
    tendsto_cubicAFECompletedPhysicalSummand_height W T hX d e δ p.1 J p.2)

theorem norm_cubicAFECompletedPhysicalKernelVertical_le
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (d e : ℕ) (δ : ℤ) (J : ℕ) (p : ℝ × ℝ) :
    ‖cubicAFECompletedPhysicalKernelVertical W T X d e δ J p.1 p.2‖ ≤
      cubicAFECompletedPhysicalMajorant W T X d e J p :=
  le_of_tendsto (tendsto_cubicAFECompletedPhysicalSummand_height W T hX d e δ p.1 J p.2).norm
    (Eventually.of_forall (fun V ↦
      norm_cubicAFECompletedPhysicalSummand_le_heightMass W T hX V d e δ p.1 J p.2))

theorem integrable_cubicAFECompletedPhysicalKernelVertical
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (d e : ℕ) (δ : ℤ) (J : ℕ) :
    Integrable (Function.uncurry (cubicAFECompletedPhysicalKernelVertical W T X d e δ J)) :=
  (integrable_cubicAFECompletedPhysicalMajorant W hT hX d e J).mono'
    (stronglyMeasurable_cubicAFECompletedPhysicalKernelVertical W T hX d e δ J).aestronglyMeasurable
    (Eventually.of_forall (norm_cubicAFECompletedPhysicalKernelVertical_le W T hX d e δ J))

/-- Fubini and dominated convergence apply to the literal completed kernel
with the original time weight and phase. The shift may be zero at fixed J. -/
theorem tendsto_cubicAFECompletedPhysicalDoubleIntegral_height
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (d e : ℕ) (δ : ℤ) (J : ℕ) :
    Tendsto (fun V : ℝ ↦ ∫ t : ℝ, ∫ x : ℝ,
      cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J t x) atTop
      (nhds (∫ t : ℝ, ∫ x : ℝ,
        cubicAFECompletedPhysicalKernelVertical W T X d e δ J t x)) := by
  have hv := integrable_cubicAFECompletedPhysicalKernelVertical W hT hX d e δ J
  have hf (V : ℝ) := integrable_cubicAFECompletedPhysicalKernelFinite W hT hX V d e δ J
  have hl : Tendsto (fun V : ℝ ↦ ∫ p : ℝ × ℝ,
      cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J p.1 p.2) atTop
      (nhds (∫ p : ℝ × ℝ,
        cubicAFECompletedPhysicalKernelVertical W T X d e δ J p.1 p.2)) := by
    apply tendsto_integral_filter_of_dominated_convergence (cubicAFECompletedPhysicalMajorant W T X d e J)
    · exact Eventually.of_forall (fun V ↦ (hf V).aestronglyMeasurable)
    · exact Eventually.of_forall (fun V ↦ Eventually.of_forall (fun p ↦
        norm_cubicAFECompletedPhysicalSummand_le_heightMass W T hX V d e δ p.1 J p.2))
    · exact integrable_cubicAFECompletedPhysicalMajorant W hT hX d e J
    · exact Eventually.of_forall (fun p ↦
        tendsto_cubicAFECompletedPhysicalSummand_height W T hX d e δ p.1 J p.2)
  have hfEq (V : ℝ) : (∫ p : ℝ × ℝ,
      cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J p.1 p.2) =
      ∫ t : ℝ, ∫ x : ℝ, cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J t x :=
    integral_prod _ (hf V)
  have hvEq : (∫ p : ℝ × ℝ,
      cubicAFECompletedPhysicalKernelVertical W T X d e δ J p.1 p.2) =
      ∫ t : ℝ, ∫ x : ℝ, cubicAFECompletedPhysicalKernelVertical W T X d e δ J t x :=
    integral_prod _ hv
  simpa only [hfEq, hvEq] using hl

/-- Height limit of the original infinite dyadic zero-mode sum, at one fixed
shift and completion depth. The Poisson factor 1/s remains explicit. -/
theorem tendsto_cubicAFECompletedZeroMode_height
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J : ℕ) :
    Tendsto (fun V : ℝ ↦ ∑' jk : ℕ × ℕ,
      cubicAFECompletedZeroModeBox (d := d) W T X V he δ J jk) atTop
      (nhds ((((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∫ t : ℝ, ∫ x : ℝ,
        cubicAFECompletedPhysicalKernelVertical W T X d e δ J t x)) := by
  have heq (V : ℝ) := (hasSum_cubicAFECompletedZeroModeBox_physical W hT hX V hd he δ J).tsum_eq
  simp_rw [heq]
  exact (tendsto_cubicAFECompletedPhysicalDoubleIntegral_height W hT hX d e δ J).const_mul _

end PrimeNumberTheorem.MWKFCubic
