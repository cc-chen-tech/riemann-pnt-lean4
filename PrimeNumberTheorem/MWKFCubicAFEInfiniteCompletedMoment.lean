import PrimeNumberTheorem.MWKFCubicAFEDiagonalHeight
import PrimeNumberTheorem.MWKFCubicAFECompletedSeparatedMoment

open Complex Filter MeasureTheory
open scoped Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The actual moment after the full summed height limit, at fixed depth

The nonzero mode is the limit of the original full nonzero-mode sum, not
an arbitrary remainder defined by subtracting a proposed main term. Its
convergence follows from the original moment, the independently convergent
diagonal and the all-shift completed zero mode. No individual Fourier-mode
height exchange or completion-depth limit is used.

The exact real identity below has a completion-dependent principal part
Q_J. It supplies neither Q_J -> 4/3 * integral W nor R_J = o(T), and it does
not identify Q_J with the canonical principal part of the parent paper.
-/

private theorem tendsto_nonzeroMode_to_difference
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (J : ℕ) :
    Tendsto (fun V : ℝ ↦ cubicAFECompletedNonzeroModeMomentFinite W T X V J) atTop
      (nhds ((cubicMollifiedSecondMoment W T : ℂ) -
        cubicAFECompletedZeroModeMomentVertical W T X J - cubicAFEDiagonalMomentVertical W T X)) := by
  apply ((tendsto_cubicAFEDiagonal_completedNonzero_height W hT hX J).sub
    (tendsto_cubicAFEDiagonalMomentFinite_height W hT hX)).congr'
  exact Eventually.of_forall (fun V ↦ by
    change (cubicAFEDiagonalMomentFinite W T X V +
      cubicAFECompletedNonzeroModeMomentFinite W T X V J) -
      cubicAFEDiagonalMomentFinite W T X V = cubicAFECompletedNonzeroModeMomentFinite W T X V J
    ring)

/-- Limit of the literal full nonzero-mode moment, with its original order
of finite mollifier sums, all signed shifts, dyadic boxes and frequencies.
Existence for T != 0 and X > 1/2 is proved below; no asymptotic size is built
into this definition. -/
noncomputable def cubicAFECompletedNonzeroModeMomentVertical
    (W : CubicTestWeight) (T X : ℝ) (J : ℕ) : ℂ :=
  limUnder (atTop : Filter ℝ) (fun V ↦ cubicAFECompletedNonzeroModeMomentFinite W T X V J)

theorem cubicAFECompletedNonzeroModeMomentVertical_eq
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (J : ℕ) :
    cubicAFECompletedNonzeroModeMomentVertical W T X J =
      (cubicMollifiedSecondMoment W T : ℂ) - cubicAFECompletedZeroModeMomentVertical W T X J -
        cubicAFEDiagonalMomentVertical W T X :=
  (tendsto_nonzeroMode_to_difference W hT hX J).limUnder_eq

theorem tendsto_cubicAFECompletedNonzeroModeMomentFinite_height
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (J : ℕ) :
    Tendsto (fun V : ℝ ↦ cubicAFECompletedNonzeroModeMomentFinite W T X V J) atTop
      (nhds (cubicAFECompletedNonzeroModeMomentVertical W T X J)) := by
  rw [cubicAFECompletedNonzeroModeMomentVertical_eq W hT hX J]
  exact tendsto_nonzeroMode_to_difference W hT hX J

/-- Actual original integral, with the diagonal and completed modes after
height has been removed from the already summed expression. -/
theorem cubicMollifiedSecondMoment_eq_completed_modes
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (J : ℕ) :
    (cubicMollifiedSecondMoment W T : ℂ) =
      (cubicAFEDiagonalMomentVertical W T X + cubicAFECompletedZeroModeMomentVertical W T X J) +
        cubicAFECompletedNonzeroModeMomentVertical W T X J := by
  rw [cubicAFECompletedNonzeroModeMomentVertical_eq W hT hX J]
  ring

/-- Completion-dependent exact principal part, not an evaluated asymptotic
main term. The physical factor T is divided out only for the real identity. -/
noncomputable def cubicAFECompletedPrincipalPart (W : CubicTestWeight) (T X : ℝ) (J : ℕ) : ℝ :=
  (cubicAFEDiagonalMomentVertical W T X + cubicAFECompletedZeroModeMomentVertical W T X J).re / T

noncomputable def cubicAFECompletedRemainder (W : CubicTestWeight) (T X : ℝ) (J : ℕ) : ℝ :=
  (cubicAFECompletedNonzeroModeMomentVertical W T X J).re

/-- Fixed-depth exact decomposition of the literal moment. This theorem
does not close either hmain or hrem in MWKFCubicFinal. -/
theorem cubicMollifiedSecondMoment_eq_completed_principal_remainder
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (J : ℕ) :
    cubicMollifiedSecondMoment W T = T * cubicAFECompletedPrincipalPart W T X J +
      cubicAFECompletedRemainder W T X J := by
  have h := congrArg Complex.re (cubicMollifiedSecondMoment_eq_completed_modes W hT hX J)
  simp only [Complex.ofReal_re, Complex.add_re] at h
  unfold cubicAFECompletedPrincipalPart cubicAFECompletedRemainder
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hT]
  simpa only [Complex.add_re] using h

end PrimeNumberTheorem.MWKFCubic
