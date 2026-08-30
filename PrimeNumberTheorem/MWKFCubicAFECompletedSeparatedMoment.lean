import PrimeNumberTheorem.MWKFCubicAFECompletedShift

open Complex Filter MeasureTheory
open scoped Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Separate completed modes in the full mollified moment

The proved integrated lattice bound makes each completed mode summable
across shifts, not merely their pair. Finite mollifier sums preserve the
independent zero-mode height limit. Completion depth is fixed, and no
diagonal/main-term or nonzero-mode T-asymptotic is asserted.
-/

theorem summable_shift_cubicAFECompletedZeroModeBox
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (J : ℕ) :
    Summable (fun δ : ℤ ↦ ∑' jk : ℕ × ℕ,
      cubicAFECompletedZeroModeBox (d := d) W T X V he δ J jk) := by
  have hs : Summable (fun δ : ℤ ↦ ∫ t : ℝ, ∫ x : ℝ,
      cubicAFECompletedBoundaryPhysicalKernel W T X V d e δ J t x) :=
    (summable_integral_cubicAFECompletedShiftMajorant W hT hX he J).of_norm_bounded
      (norm_integral_cubicAFECompletedKernel_le_shiftMajorant W hT hX V d e J)
  apply (hs.mul_left (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹)).congr
  intro δ
  exact (hasSum_cubicAFECompletedZeroModeBox_physical W hT hX V hd he δ J).tsum_eq.symm

theorem summable_shift_cubicAFECompletedNonzeroModeBox
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (J : ℕ) :
    Summable (fun δ : {δ : ℤ // δ ≠ 0} ↦ ∑' jk : ℕ × ℕ,
      cubicAFECompletedNonzeroModeBox (d := d) W T X V he δ.val J jk) := by
  apply ((summable_shift_cubicAFECompletedModes W hT hX V hd he J).sub
    ((summable_shift_cubicAFECompletedZeroModeBox W hT hX V hd he J).subtype _)).congr
  intro δ
  exact add_sub_cancel_left _ _

noncomputable def cubicAFECompletedZeroModeMomentFinite
    (W : CubicTestWeight) (T X V : ℝ) (J : ℕ) : ℂ :=
  ∑ d ∈ (cubicMollifierSupport T).attach,
    ∑ e ∈ (cubicMollifierSupport T).attach,
      ∑' δ : {δ : ℤ // δ ≠ 0}, ∑' jk : ℕ × ℕ,
        cubicAFECompletedZeroModeBox (d := d.val) W T X V
          (show 0 < e.val from (Finset.mem_Icc.mp e.property).1) δ.val J jk

noncomputable def cubicAFECompletedNonzeroModeMomentFinite
    (W : CubicTestWeight) (T X V : ℝ) (J : ℕ) : ℂ :=
  ∑ d ∈ (cubicMollifierSupport T).attach,
    ∑ e ∈ (cubicMollifierSupport T).attach,
      ∑' δ : {δ : ℤ // δ ≠ 0}, ∑' jk : ℕ × ℕ,
        cubicAFECompletedNonzeroModeBox (d := d.val) W T X V
          (show 0 < e.val from (Finset.mem_Icc.mp e.property).1) δ.val J jk

noncomputable def cubicAFECompletedZeroModeMomentVertical
    (W : CubicTestWeight) (T X : ℝ) (J : ℕ) : ℂ :=
  ∑ d ∈ (cubicMollifierSupport T).attach,
    ∑ e ∈ (cubicMollifierSupport T).attach,
      (((e.val / Nat.gcd d.val e.val : ℕ) : ℂ)⁻¹) *
        ∑' δ : {δ : ℤ // δ ≠ 0}, ∫ t : ℝ, ∫ x : ℝ,
          cubicAFECompletedPhysicalKernelVertical W T X d.val e.val δ.val J t x

theorem cubicAFECompletedMomentFinite_eq_zero_add_nonzero
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (J : ℕ) :
    cubicAFECompletedMomentFinite W T X V J =
      cubicAFECompletedZeroModeMomentFinite W T X V J +
        cubicAFECompletedNonzeroModeMomentFinite W T X V J := by
  unfold cubicAFECompletedMomentFinite cubicAFECompletedZeroModeMomentFinite
    cubicAFECompletedNonzeroModeMomentFinite
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  exact Summable.tsum_add
    ((summable_shift_cubicAFECompletedZeroModeBox W hT hX V
      (Finset.mem_Icc.mp d.property).1 (Finset.mem_Icc.mp e.property).1 J).subtype _)
    (summable_shift_cubicAFECompletedNonzeroModeBox W hT hX V
      (Finset.mem_Icc.mp d.property).1 (Finset.mem_Icc.mp e.property).1 J)

theorem cubicAFEMollifiedMomentFinite_eq_diagonal_completed_zero_nonzero
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (J : ℕ) :
    cubicAFEMollifiedMomentFinite W T X V =
      (cubicAFEDiagonalMomentFinite W T X V + cubicAFECompletedZeroModeMomentFinite W T X V J) +
        cubicAFECompletedNonzeroModeMomentFinite W T X V J := by
  rw [cubicAFEMollifiedMomentFinite_eq_diagonal_add_completed W hT hX V J,
    cubicAFECompletedMomentFinite_eq_zero_add_nonzero W hT hX V J, add_assoc]

theorem tendsto_cubicAFECompletedZeroModeMoment_height
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (J : ℕ) :
    Tendsto (fun V : ℝ ↦ cubicAFECompletedZeroModeMomentFinite W T X V J) atTop
      (nhds (cubicAFECompletedZeroModeMomentVertical W T X J)) := by
  unfold cubicAFECompletedZeroModeMomentFinite cubicAFECompletedZeroModeMomentVertical
  apply tendsto_finsetSum
  intro d _
  apply tendsto_finsetSum
  intro e _
  exact tendsto_cubicAFECompletedZeroMode_allShift_height W hT hX
    (Finset.mem_Icc.mp d.property).1 (Finset.mem_Icc.mp e.property).1 J

/-- Subtract the independently convergent completed zero mode from the
original moment. This is not a separate limit for the diagonal alone. -/
theorem tendsto_cubicAFEDiagonal_completedNonzero_height
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (J : ℕ) :
    Tendsto (fun V : ℝ ↦ cubicAFEDiagonalMomentFinite W T X V +
      cubicAFECompletedNonzeroModeMomentFinite W T X V J) atTop
      (nhds ((cubicMollifiedSecondMoment W T : ℂ) - cubicAFECompletedZeroModeMomentVertical W T X J)) := by
  apply ((tendsto_cubicAFEMollifiedMomentFinite W hT hX).sub
    (tendsto_cubicAFECompletedZeroModeMoment_height W hT hX J)).congr'
  exact Eventually.of_forall (fun V ↦ by
    change cubicAFEMollifiedMomentFinite W T X V - cubicAFECompletedZeroModeMomentFinite W T X V J =
      cubicAFEDiagonalMomentFinite W T X V + cubicAFECompletedNonzeroModeMomentFinite W T X V J
    rw [cubicAFEMollifiedMomentFinite_eq_diagonal_completed_zero_nonzero W hT hX V J]
    ring)

end PrimeNumberTheorem.MWKFCubic
