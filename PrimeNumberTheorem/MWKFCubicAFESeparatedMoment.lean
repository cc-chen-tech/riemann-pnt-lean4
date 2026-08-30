import PrimeNumberTheorem.MWKFCubicAFEShiftReassembly

open Complex Filter MeasureTheory
open scoped Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Full finite-height diagonal, zero-mode and nonzero-mode decomposition

Infinite dyadic/shift separation is justified by the actual absolute
convergence theorems. Only the recombined expression has a proved height
limit; the diagonal plus zero mode has not yet been evaluated asymptotically.
-/

noncomputable def cubicAFEZeroModeMomentFinite (W : CubicTestWeight) (T X V : ℝ) : ℂ :=
  ∑ d ∈ (cubicMollifierSupport T).attach,
    ∑ e ∈ (cubicMollifierSupport T).attach,
      ∑' δ : {δ : ℤ // δ ≠ 0}, ∑' jk : ℕ × ℕ,
        cubicAFEZeroModeBoxFinite (d := d.val) W T X V
          (show 0 < e.val from (Finset.mem_Icc.mp e.property).1) δ.val jk

noncomputable def cubicAFENonzeroModeMomentFinite (W : CubicTestWeight) (T X V : ℝ) : ℂ :=
  ∑ d ∈ (cubicMollifierSupport T).attach,
    ∑ e ∈ (cubicMollifierSupport T).attach,
      ∑' δ : {δ : ℤ // δ ≠ 0}, ∑' jk : ℕ × ℕ,
        cubicAFENonzeroModeBoxFinite (d := d.val) W T X V
          (show 0 < e.val from (Finset.mem_Icc.mp e.property).1) δ.val jk

theorem cubicAFEFrequencyMomentFinite_eq_zero_add_nonzero
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    cubicAFEFrequencyMomentFinite W T X V =
      cubicAFEZeroModeMomentFinite W T X V + cubicAFENonzeroModeMomentFinite W T X V := by
  unfold cubicAFEFrequencyMomentFinite cubicAFEZeroModeMomentFinite cubicAFENonzeroModeMomentFinite
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  exact tsum_shift_cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero W hT hX V
    (Finset.mem_Icc.mp d.property).1 (Finset.mem_Icc.mp e.property).1

theorem cubicAFEMollifiedMomentFinite_eq_diagonal_zero_nonzero
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    cubicAFEMollifiedMomentFinite W T X V =
      (cubicAFEDiagonalMomentFinite W T X V + cubicAFEZeroModeMomentFinite W T X V) +
        cubicAFENonzeroModeMomentFinite W T X V := by
  rw [cubicAFEMollifiedMomentFinite_eq_diagonal_add_frequency W hT hX V,
    cubicAFEFrequencyMomentFinite_eq_zero_add_nonzero W hT hX V, add_assoc]

theorem tendsto_cubicAFEDiagonal_zero_nonzero
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) :
    Tendsto (fun V : ℝ ↦
      (cubicAFEDiagonalMomentFinite W T X V + cubicAFEZeroModeMomentFinite W T X V) +
        cubicAFENonzeroModeMomentFinite W T X V)
      atTop (𝓝 (cubicMollifiedSecondMoment W T : ℂ)) := by
  apply (tendsto_cubicAFEMollifiedMomentFinite W hT hX).congr'
  exact Eventually.of_forall (fun V ↦
    cubicAFEMollifiedMomentFinite_eq_diagonal_zero_nonzero W hT hX V)

end PrimeNumberTheorem.MWKFCubic
