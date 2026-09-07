import PrimeNumberTheorem.MWKFCubicAFELatticeDecay
import PrimeNumberTheorem.MWKFCubicAFEZeroModeReassembly

open Complex Filter MeasureTheory Set
open scoped Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Absolute shift aggregation of the actual zero-mode kernel

The lattice bound retains modulus dependence but is uniform in its real
translation. It supplies integrated domination for all integer shifts.
Only fixed finite height is asserted; no independent V-limit or o(T) bound.
-/

private theorem reduced_modulus_ge_one {d e : ℕ} (he : 0 < e) :
    (1 : ℝ) ≤ ((e / Nat.gcd d e : ℕ) : ℝ) := by
  have hpos : 0 < e / Nat.gcd d e := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hh := (gcd_extraction (Nat.gcd_pos_of_pos_right d he).ne').2.1
    rw [hz, mul_zero] at hh
    exact he.ne' hh
  exact_mod_cast hpos

private theorem boundary_norm_le_lattice
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ) (δ : ℤ) (t x : ℝ) :
    ‖cubicAFEBoundaryPhysicalKernel W T X V d e δ t x‖ ≤
      (cubicAFEPhysicalTimeEnvelope W T X V d e t * cubicAFEHalfLinePower X x) *
        (cubicAFEDyadicLowerWeight (cubicAFEProgressionRealSecond d e δ x) *
          (cubicAFEProgressionRealSecond d e δ x) ^ (-X - 1 / 2)) := by
  let y := cubicAFEProgressionRealSecond d e δ x
  have hC := cubicAFEPhysicalTimeEnvelope_nonneg W T X V d e t
  have hL : 0 ≤ cubicAFEDyadicLowerWeight y * y ^ (-X - 1 / 2) :=
    cubicAFELatticePower_nonneg X ((e / Nat.gcd d e : ℕ) : ℝ)
      (x * ((d / Nat.gcd d e : ℕ) : ℝ)) δ
  rw [norm_cubicAFEBoundaryPhysicalKernel]
  by_cases hx : x ≤ 1 / 2
  · rw [cubicAFEDyadicLowerWeight_zero hx, zero_mul, zero_mul]
    exact mul_nonneg (mul_nonneg hC (cubicAFEHalfLinePower_nonneg X x)) hL
  by_cases hy : y ≤ 1 / 2
  · have hz : cubicAFEDyadicLowerWeight (cubicAFEProgressionRealSecond d e δ x) = 0 :=
      cubicAFEDyadicLowerWeight_zero hy
    simp only [hz, mul_zero, zero_mul, le_refl]
  have hxpos : 0 < x := by linarith [lt_of_not_ge hx]
  have hypos : 0 < y := by linarith [lt_of_not_ge hy]
  have hP : 0 < cubicAFEProgressionRealProduct d e δ x := mul_pos hxpos hypos
  calc
    _ ≤ (cubicAFEDyadicLowerWeight x * cubicAFEDyadicLowerWeight y) *
        (cubicAFEPhysicalTimeEnvelope W T X V d e t * (x * y) ^ (-X - 1 / 2)) :=
      mul_le_mul_of_nonneg_left
        (norm_cubicAFEProgressionPhysicalSummand_le_envelope W T X V d e δ t hP)
        (mul_nonneg (cubicAFEDyadicLowerWeight_nonneg _) (cubicAFEDyadicLowerWeight_nonneg _))
    _ = (cubicAFEPhysicalTimeEnvelope W T X V d e t *
        (cubicAFEDyadicLowerWeight x * x ^ (-X - 1 / 2))) *
          (cubicAFEDyadicLowerWeight y * y ^ (-X - 1 / 2)) := by
      rw [Real.mul_rpow hxpos.le hypos.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (cubicAFEDyadicLowerWeight_mul_rpow_le X x) hC) hL

private theorem summable_boundary_norm
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (he : 0 < e) (t x : ℝ) :
    Summable (fun δ : ℤ ↦ ‖cubicAFEBoundaryPhysicalKernel W T X V d e δ t x‖) := by
  have hL := summable_cubicAFELatticePower hX (reduced_modulus_ge_one (d := d) he)
    (x * ((d / Nat.gcd d e : ℕ) : ℝ))
  exact Summable.of_nonneg_of_le (fun δ ↦ norm_nonneg _)
    (fun δ ↦ boundary_norm_le_lattice W T X V d e δ t x)
    (hL.mul_left (cubicAFEPhysicalTimeEnvelope W T X V d e t * cubicAFEHalfLinePower X x))

theorem summable_integral_norm_cubicAFEBoundaryPhysicalKernel
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Summable (fun δ : ℤ ↦ ∫ p : ℝ × ℝ,
      ‖cubicAFEBoundaryPhysicalKernel W T X V d e δ p.1 p.2‖) := by
  let F (δ : ℤ) (p : ℝ × ℝ) := ‖cubicAFEBoundaryPhysicalKernel W T X V d e δ p.1 p.2‖
  let C := (1 / (2 * ((e / Nat.gcd d e : ℕ) : ℝ))) ^ (-X - 1 / 2) *
    ∑' n : ℤ, |(n : ℝ)| ^ (-X - 1 / 2)
  have hs (p : ℝ × ℝ) : Summable (fun δ ↦ F δ p) :=
    summable_boundary_norm W T hX V he p.1 p.2
  have hf (δ : ℤ) : AEStronglyMeasurable (F δ) volume :=
    (integrable_cubicAFEBoundaryPhysicalKernel W hT hX V hd he δ).norm.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ ∑' δ, F δ p) volume := by
    apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ℤ))
      (f := fun J p ↦ ∑ δ ∈ J, F δ p)
    · intro J
      exact Finset.aestronglyMeasurable_fun_sum J (fun δ _ ↦ hf δ)
    · exact Eventually.of_forall (fun p ↦ (hs p).hasSum)
  have hb : Integrable (fun p : ℝ × ℝ ↦
      (cubicAFEPhysicalTimeEnvelope W T X V d e p.1 * cubicAFEHalfLinePower X p.2) * C) :=
    ((integrable_cubicAFEPhysicalTimeEnvelope W hT hX V d e).mul_prod
      (integrable_cubicAFEHalfLinePower hX)).mul_const C
  have htotal : Integrable (fun p : ℝ × ℝ ↦ ∑' δ, F δ p) := by
    apply hb.mono' hmeas
    filter_upwards with p
    rw [Real.norm_of_nonneg (tsum_nonneg (fun δ ↦ norm_nonneg _))]
    let H := cubicAFEPhysicalTimeEnvelope W T X V d e p.1 * cubicAFEHalfLinePower X p.2
    have hH : 0 ≤ H := mul_nonneg (cubicAFEPhysicalTimeEnvelope_nonneg W T X V d e p.1)
      (cubicAFEHalfLinePower_nonneg X p.2)
    have hL := summable_cubicAFELatticePower hX (reduced_modulus_ge_one (d := d) he)
      (p.2 * ((d / Nat.gcd d e : ℕ) : ℝ))
    calc
      _ ≤ ∑' δ : ℤ, H *
          (cubicAFEDyadicLowerWeight (cubicAFEProgressionRealSecond d e δ p.2) *
            (cubicAFEProgressionRealSecond d e δ p.2) ^ (-X - 1 / 2)) :=
        Summable.tsum_le_tsum (fun δ ↦ boundary_norm_le_lattice W T X V d e δ p.1 p.2)
          (hs p) (hL.mul_left H)
      _ = H * ∑' δ : ℤ,
          (cubicAFEDyadicLowerWeight (cubicAFEProgressionRealSecond d e δ p.2) *
            (cubicAFEProgressionRealSecond d e δ p.2) ^ (-X - 1 / 2)) := tsum_mul_left
      _ ≤ H * C := mul_le_mul_of_nonneg_left
        (tsum_cubicAFELatticePower_le hX (reduced_modulus_ge_one (d := d) he)
          (p.2 * ((d / Nat.gcd d e : ℕ) : ℝ))) hH
  exact (hasSum_integral_of_dominated_convergence (bound := F) hf
    (fun δ ↦ Eventually.of_forall (fun p ↦ by
      dsimp [F]; rw [abs_of_nonneg (norm_nonneg _)]))
    (Eventually.of_forall hs) htotal (Eventually.of_forall (fun p ↦ (hs p).hasSum))).summable

theorem summable_shift_cubicAFEZeroModeBoxFinite
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Summable (fun δ : ℤ ↦ ∑' jk : ℕ × ℕ,
      cubicAFEZeroModeBoxFinite (d := d) W T X V he δ jk) := by
  have hs : Summable (fun δ : ℤ ↦ ∫ p : ℝ × ℝ,
      cubicAFEBoundaryPhysicalKernel W T X V d e δ p.1 p.2) :=
    (summable_integral_norm_cubicAFEBoundaryPhysicalKernel W hT hX V hd he).of_norm_bounded
      (fun δ ↦ norm_integral_le_integral_norm _)
  apply (hs.mul_left (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹)).congr
  intro δ
  rw [(hasSum_cubicAFEZeroModeBoxFinite W hT hX V hd he δ).tsum_eq]
  congr 1
  exact integral_prod _ (integrable_cubicAFEBoundaryPhysicalKernel W hT hX V hd he δ)

theorem summable_shift_cubicAFENonzeroModeBoxFinite
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Summable (fun δ : {δ : ℤ // δ ≠ 0} ↦ ∑' jk : ℕ × ℕ,
      cubicAFENonzeroModeBoxFinite (d := d) W T X V he δ.val jk) := by
  apply ((summable_shift_cubicAFEFrequencyBoxFinite W hT hX V hd he).sub
    ((summable_shift_cubicAFEZeroModeBoxFinite W hT hX V hd he).subtype _)).congr
  intro δ
  rw [tsum_cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero W hT hX V hd he δ.val]
  exact add_sub_cancel_left _ _

theorem tsum_shift_cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    (∑' δ : {δ : ℤ // δ ≠ 0}, ∑' jk : ℕ × ℕ,
      cubicAFEFrequencyBoxFinite (d := d) W T X V he δ.val jk) =
      (∑' δ : {δ : ℤ // δ ≠ 0}, ∑' jk : ℕ × ℕ,
        cubicAFEZeroModeBoxFinite (d := d) W T X V he δ.val jk) +
      ∑' δ : {δ : ℤ // δ ≠ 0}, ∑' jk : ℕ × ℕ,
        cubicAFENonzeroModeBoxFinite (d := d) W T X V he δ.val jk := by
  simp_rw [tsum_cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero W hT hX V hd he]
  exact Summable.tsum_add ((summable_shift_cubicAFEZeroModeBoxFinite W hT hX V hd he).subtype _)
    (summable_shift_cubicAFENonzeroModeBoxFinite W hT hX V hd he)

end PrimeNumberTheorem.MWKFCubic
