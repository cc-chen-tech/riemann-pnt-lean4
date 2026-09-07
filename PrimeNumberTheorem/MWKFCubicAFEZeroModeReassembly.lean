import PrimeNumberTheorem.MWKFCubicAFEPhysicalDecay
import PrimeNumberTheorem.MWKFCubicAFEZeroMode

open Complex Filter MeasureTheory Set
open scoped Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Infinite dyadic zero-mode reassembly at a fixed shift

The actual lower-boundary physical kernel is integrable on time-space.
This proves integrated absolute convergence before summing zero modes.
The outer shift sum and parameter-uniform asymptotics are not asserted here.
-/

noncomputable def cubicAFEBoundaryPhysicalKernel
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ) (δ : ℤ) (t x : ℝ) : ℂ :=
  ((cubicAFEDyadicLowerWeight x *
    cubicAFEDyadicLowerWeight (cubicAFEProgressionRealSecond d e δ x) : ℝ) : ℂ) *
      cubicAFEProgressionPhysicalSummand W T X V d e δ t x

theorem norm_cubicAFEBoundaryPhysicalKernel
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ) (δ : ℤ) (t x : ℝ) :
    ‖cubicAFEBoundaryPhysicalKernel W T X V d e δ t x‖ =
      cubicAFEDyadicLowerWeight x *
        cubicAFEDyadicLowerWeight (cubicAFEProgressionRealSecond d e δ x) *
          ‖cubicAFEProgressionPhysicalSummand W T X V d e δ t x‖ := by
  rw [cubicAFEBoundaryPhysicalKernel, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (cubicAFEDyadicLowerWeight_nonneg _)
      (cubicAFEDyadicLowerWeight_nonneg _))]

theorem norm_cubicAFEBoundaryPhysicalKernel_le
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (d e : ℕ) (δ : ℤ) (t x : ℝ) :
    ‖cubicAFEBoundaryPhysicalKernel W T X V d e δ t x‖ ≤
      cubicAFEPhysicalTimeEnvelope W T X V d e t *
        ((1 / 2 : ℝ) ^ (-X - 1 / 2) * cubicAFEHalfLinePower X x) := by
  rw [norm_cubicAFEBoundaryPhysicalKernel]
  have hC := cubicAFEPhysicalTimeEnvelope_nonneg W T X V d e t
  have hhalf := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (-X - 1 / 2)
  have hright : 0 ≤ cubicAFEPhysicalTimeEnvelope W T X V d e t *
      ((1 / 2 : ℝ) ^ (-X - 1 / 2) * cubicAFEHalfLinePower X x) :=
    mul_nonneg hC (mul_nonneg hhalf (cubicAFEHalfLinePower_nonneg X x))
  by_cases hx : x ≤ 1 / 2
  · rw [cubicAFEDyadicLowerWeight_zero hx, zero_mul, zero_mul]
    exact hright
  let y := cubicAFEProgressionRealSecond d e δ x
  by_cases hy : y ≤ 1 / 2
  · rw [show cubicAFEDyadicLowerWeight (cubicAFEProgressionRealSecond d e δ x) = 0 from
      cubicAFEDyadicLowerWeight_zero hy, mul_zero, zero_mul]
    exact hright
  have hxpos : 0 < x := by linarith [lt_of_not_ge hx]
  have hypos : 0 < y := by linarith [lt_of_not_ge hy]
  have hP : 0 < cubicAFEProgressionRealProduct d e δ x := mul_pos hxpos hypos
  have hybound : cubicAFEDyadicLowerWeight y * y ^ (-X - 1 / 2) ≤
      (1 / 2 : ℝ) ^ (-X - 1 / 2) :=
    (mul_le_of_le_one_left (Real.rpow_nonneg hypos.le _)
      (cubicAFEDyadicLowerWeight_le_one y)).trans
        (Real.rpow_le_rpow_of_nonpos (by norm_num) (le_of_not_ge hy) (by linarith))
  calc
    _ ≤ (cubicAFEDyadicLowerWeight x * cubicAFEDyadicLowerWeight y) *
        (cubicAFEPhysicalTimeEnvelope W T X V d e t *
          (x * y) ^ (-X - 1 / 2)) :=
      mul_le_mul_of_nonneg_left
        (norm_cubicAFEProgressionPhysicalSummand_le_envelope W T X V d e δ t hP)
        (mul_nonneg (cubicAFEDyadicLowerWeight_nonneg _) (cubicAFEDyadicLowerWeight_nonneg _))
    _ = cubicAFEPhysicalTimeEnvelope W T X V d e t *
        ((cubicAFEDyadicLowerWeight y * y ^ (-X - 1 / 2)) *
          (cubicAFEDyadicLowerWeight x * x ^ (-X - 1 / 2))) := by
      rw [Real.mul_rpow hxpos.le hypos.le]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact mul_le_mul hybound (cubicAFEDyadicLowerWeight_mul_rpow_le X x)
        (mul_nonneg (cubicAFEDyadicLowerWeight_nonneg _) (Real.rpow_nonneg hxpos.le _)) hhalf

private theorem dyadicKernel_integrable
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (jk : ℕ × ℕ) :
    Integrable (Function.uncurry (cubicAFEProgressionCutoffSummand W T X V
      (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2))) :=
  (continuous_cubicAFEProgressionCutoffSummand_joint W T X V hd he _ hX).integrable_of_hasCompactSupport
    (hasCompactSupport_cubicAFEProgressionCutoffSummand_joint W hT X V _)

theorem integrable_cubicAFEBoundaryPhysicalKernel
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) :
    Integrable (Function.uncurry (cubicAFEBoundaryPhysicalKernel W T X V d e δ)) := by
  let F (jk : ℕ × ℕ) := Function.uncurry (cubicAFEProgressionCutoffSummand W T X V
    (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2))
  have hmeas : AEStronglyMeasurable
      (Function.uncurry (cubicAFEBoundaryPhysicalKernel W T X V d e δ)) volume := by
    apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset (ℕ × ℕ)))
      (f := fun J p ↦ ∑ jk ∈ J, F jk p)
    · intro J
      exact (continuous_finsetSum J (fun jk _ ↦
        continuous_cubicAFEProgressionCutoffSummand_joint W T X V hd he _ hX)).aestronglyMeasurable
    · filter_upwards with p
      exact hasSum_cubicAFEProgressionDyadicKernel_allReal W T X V he δ p.1 p.2
  have hb : Integrable (fun p : ℝ × ℝ ↦ cubicAFEPhysicalTimeEnvelope W T X V d e p.1 *
      ((1 / 2 : ℝ) ^ (-X - 1 / 2) * cubicAFEHalfLinePower X p.2)) :=
    (integrable_cubicAFEPhysicalTimeEnvelope W hT hX V d e).mul_prod
      ((integrable_cubicAFEHalfLinePower hX).const_mul _)
  exact hb.mono' hmeas (Eventually.of_forall (fun p ↦
    norm_cubicAFEBoundaryPhysicalKernel_le W T hX V d e δ p.1 p.2))

/-- Absolute integrability of the entire dyadic family, not just each box. -/
theorem summable_integral_norm_cubicAFEProgressionDyadicKernel
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) :
    Summable (fun jk : ℕ × ℕ ↦ ∫ p : ℝ × ℝ,
      ‖cubicAFEProgressionCutoffSummand W T X V
        (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) p.1 p.2‖) := by
  let F (jk : ℕ × ℕ) (p : ℝ × ℝ) := ‖cubicAFEProgressionCutoffSummand W T X V
    (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) p.1 p.2‖
  have hsum (p : ℝ × ℝ) : HasSum (fun jk ↦ F jk p)
      ‖cubicAFEBoundaryPhysicalKernel W T X V d e δ p.1 p.2‖ := by
    rw [norm_cubicAFEBoundaryPhysicalKernel]
    exact hasSum_norm_cubicAFEProgressionDyadicKernel_allReal W T X V he δ p.1 p.2
  have hb : Integrable (fun p : ℝ × ℝ ↦ ∑' jk, F jk p) := by
    simpa only [Function.uncurry, (funext fun p ↦ (hsum p).tsum_eq)] using
      (integrable_cubicAFEBoundaryPhysicalKernel W hT hX V hd he δ).norm
  exact (hasSum_integral_of_dominated_convergence (bound := F)
    (fun jk ↦ (dyadicKernel_integrable W hT hX V hd he δ jk).norm.aestronglyMeasurable)
    (fun jk ↦ Eventually.of_forall (fun p ↦ by
      dsimp [F]; simp only [Function.uncurry, abs_of_nonneg (norm_nonneg _), le_refl]))
    (Eventually.of_forall (fun p ↦ (hsum p).summable)) hb
    (Eventually.of_forall hsum)).summable

theorem hasSum_cubicAFEZeroModeBoxFinite
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) :
    HasSum (fun jk : ℕ × ℕ ↦ cubicAFEZeroModeBoxFinite (d := d) W T X V he δ jk)
      ((((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∫ t : ℝ, ∫ x : ℝ,
        cubicAFEBoundaryPhysicalKernel W T X V d e δ t x) := by
  let F (jk : ℕ × ℕ) := Function.uncurry (cubicAFEProgressionCutoffSummand W T X V
    (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2))
  have hh := hasSum_integral_of_summable_integral_norm
    (fun jk ↦ dyadicKernel_integrable W hT hX V hd he δ jk)
    (summable_integral_norm_cubicAFEProgressionDyadicKernel W hT hX V hd he δ)
  have hsum : (fun p : ℝ × ℝ ↦ ∑' jk, F jk p) =
      Function.uncurry (cubicAFEBoundaryPhysicalKernel W T X V d e δ) := by
    funext p
    exact (hasSum_cubicAFEProgressionDyadicKernel_allReal W T X V he δ p.1 p.2).tsum_eq
  change HasSum (fun jk ↦ ∫ p : ℝ × ℝ, F jk p) (∫ p : ℝ × ℝ, ∑' jk, F jk p) at hh
  rw [hsum] at hh
  have hi : (∫ p : ℝ × ℝ, cubicAFEBoundaryPhysicalKernel W T X V d e δ p.1 p.2) =
      ∫ t : ℝ, ∫ x : ℝ, cubicAFEBoundaryPhysicalKernel W T X V d e δ t x :=
    integral_prod _ (integrable_cubicAFEBoundaryPhysicalKernel W hT hX V hd he δ)
  change HasSum (fun jk ↦ ∫ p : ℝ × ℝ, F jk p)
    (∫ p : ℝ × ℝ, cubicAFEBoundaryPhysicalKernel W T X V d e δ p.1 p.2) at hh
  rw [hi] at hh
  apply (hh.mul_left (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹)).congr_fun
  intro jk
  rw [cubicAFEZeroModeBoxFinite_eq_physicalIntegral]
  congr 1
  exact (integral_prod _ (dyadicKernel_integrable W hT hX V hd he δ jk)).symm

theorem summable_cubicAFENonzeroModeBoxFinite
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) :
    Summable (fun jk : ℕ × ℕ ↦ cubicAFENonzeroModeBoxFinite (d := d) W T X V he δ jk) := by
  apply ((summable_cubicAFEFrequencyBoxFinite W hT hX V hd he δ).sub
    (hasSum_cubicAFEZeroModeBoxFinite W hT hX V hd he δ).summable).congr
  intro jk
  rw [cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero W hT hX V hd he δ jk]
  exact add_sub_cancel_left _ _

theorem tsum_cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) :
    (∑' jk : ℕ × ℕ, cubicAFEFrequencyBoxFinite (d := d) W T X V he δ jk) =
      (∑' jk : ℕ × ℕ, cubicAFEZeroModeBoxFinite (d := d) W T X V he δ jk) +
        ∑' jk : ℕ × ℕ, cubicAFENonzeroModeBoxFinite (d := d) W T X V he δ jk := by
  simp_rw [cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero W hT hX V hd he δ]
  exact Summable.tsum_add (hasSum_cubicAFEZeroModeBoxFinite W hT hX V hd he δ).summable
    (summable_cubicAFENonzeroModeBoxFinite W hT hX V hd he δ)

end PrimeNumberTheorem.MWKFCubic
