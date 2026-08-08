import HardyTheorem.SelbergSqrtZetaSignedModelShiftDecomposition

/-!
# Domination of the signed pseudo-correlation

After the two short shifts are integrated first, the pseudo-correlation is
the integral of `A(t)^2`, whereas the ordinary conjugate correlation is the
integral of `|A(t)|^2`.  The triangle inequality therefore bounds the former
by the latter without discarding the Fourier cancellation inside `A`.
-/

open Complex MeasureTheory Set

namespace HardyTheorem

/-- Fubini for the ordinary conjugate correlation on the compact
shift-height box. -/
theorem selbergSqrtZetaSignedOrdinaryShiftKernel_fubini
    (kappa T : ℝ) (X : ℕ) {H : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T) :
    (∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedComplexModel kappa T X (t + w))) =
      ∫ t in T..2 * T - H, ∫ v in 0..H, ∫ w in 0..H,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedComplexModel kappa T X (t + w)) := by
  have hlong : T ≤ 2 * T - H := by linarith
  let nuShift : Measure ℝ := volume.restrict (Ioc 0 H)
  let muHeight : Measure ℝ := volume.restrict (Ioc T (2 * T - H))
  let F : (ℝ × ℝ) × ℝ → ℂ :=
    selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X
  have hF : Integrable F ((nuShift.prod nuShift).prod muHeight) := by
    simpa only [nuShift, muHeight, F] using
      integrable_selbergSqrtZetaSignedOrdinaryShiftKernel
        kappa T X hT hroom
  have hswap :
      (∫ p, ∫ t, F (p, t) ∂muHeight ∂nuShift.prod nuShift) =
        ∫ t, ∫ p, F (p, t) ∂nuShift.prod nuShift ∂muHeight :=
    integral_integral_swap hF
  calc
    (∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedComplexModel kappa T X (t + w))) =
        ∫ p, ∫ t, F (p, t) ∂muHeight ∂nuShift.prod nuShift := by
      rw [integral_prod _ hF.integral_prod_left]
      simp only [nuShift, muHeight, F,
        intervalIntegral.integral_of_le hH,
        intervalIntegral.integral_of_le hlong,
        selbergSqrtZetaSignedOrdinaryShiftKernel]
    _ = ∫ t, ∫ p, F (p, t) ∂nuShift.prod nuShift ∂muHeight := hswap
    _ = ∫ t in T..2 * T - H, ∫ v in 0..H, ∫ w in 0..H,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedComplexModel kappa T X (t + w)) := by
      rw [intervalIntegral.integral_of_le hlong]
      apply integral_congr_ae
      filter_upwards [hF.prod_left_ae] with t ht
      rw [integral_prod _ ht]
      simp only [nuShift, F, intervalIntegral.integral_of_le hH,
        selbergSqrtZetaSignedOrdinaryShiftKernel]

private theorem norm_integral_mul_self_le_norm_integral_mul_conj_self
    (A : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    ‖∫ t in a..b, A t * A t‖ ≤
      ‖∫ t in a..b, A t * (starRingEnd ℂ) (A t)‖ := by
  have hnonneg :
      0 ≤ ∫ t in a..b, Complex.normSq (A t) :=
    intervalIntegral.integral_nonneg_of_forall hab fun t =>
      Complex.normSq_nonneg (A t)
  have hord :
      (∫ t in a..b, A t * (starRingEnd ℂ) (A t)) =
        ((∫ t in a..b, Complex.normSq (A t) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only
    rw [mul_comm, Complex.normSq_eq_conj_mul_self]
  calc
    ‖∫ t in a..b, A t * A t‖ ≤
        ∫ t in a..b, ‖A t * A t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ t in a..b, Complex.normSq (A t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only
      rw [norm_mul, Complex.normSq_eq_norm_sq]
      ring
    _ = ‖∫ t in a..b,
        A t * (starRingEnd ℂ) (A t)‖ := by
      rw [hord, Complex.norm_real, Real.norm_of_nonneg hnonneg]

/-- The pseudo-correlation is dominated by the ordinary conjugate
correlation.  In particular, no separate frequency-cardinality bound is
needed for the pseudo term. -/
theorem
    norm_integral_integral_integral_selbergSqrtZetaSignedComplexModel_mul_shift_le_conj_shift
    (kappa T : ℝ) (X : ℕ) {H : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T) :
    ‖∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          selbergSqrtZetaSignedComplexModel kappa T X (t + w)‖ ≤
      ‖∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedComplexModel kappa T X (t + w))‖ := by
  let C : ℝ → ℂ := selbergSqrtZetaSignedComplexModel kappa T X
  let A : ℝ → ℂ := fun t => ∫ v in 0..H, C (t + v)
  have hpseudo := selbergSqrtZetaSignedPseudoShiftKernel_fubini
    kappa T X hT hH hroom
  have hord := selbergSqrtZetaSignedOrdinaryShiftKernel_fubini
    kappa T X hT hH hroom
  have hinnerPseudo : ∀ t : ℝ,
      (∫ v in 0..H, ∫ w in 0..H, C (t + v) * C (t + w)) =
        A t * A t := by
    intro t
    calc
      (∫ v in 0..H, ∫ w in 0..H, C (t + v) * C (t + w)) =
          ∫ v in 0..H, C (t + v) * A t := by
            apply intervalIntegral.integral_congr
            intro v _hv
            change (∫ w in 0..H, C (t + v) * C (t + w)) =
              C (t + v) * (∫ w in 0..H, C (t + w))
            exact
              intervalIntegral.integral_const_mul
                (C (t + v)) (fun w => C (t + w))
      _ = A t * A t := by
        change (∫ v in 0..H, C (t + v) * A t) =
          (∫ v in 0..H, C (t + v)) * A t
        exact
          intervalIntegral.integral_mul_const
            (A t) (fun v => C (t + v))
  have hinnerOrdinary : ∀ t : ℝ,
      (∫ v in 0..H, ∫ w in 0..H,
          C (t + v) * (starRingEnd ℂ) (C (t + w))) =
        A t * (starRingEnd ℂ) (A t) := by
    intro t
    have hconj :
        (∫ w in 0..H, (starRingEnd ℂ) (C (t + w))) =
          (starRingEnd ℂ) (A t) := by
      simp only [A, intervalIntegral.integral_of_le hH]
      exact integral_conj
    calc
      (∫ v in 0..H, ∫ w in 0..H,
          C (t + v) * (starRingEnd ℂ) (C (t + w))) =
          ∫ v in 0..H,
            C (t + v) * (starRingEnd ℂ) (A t) := by
            apply intervalIntegral.integral_congr
            intro v _hv
            change
              (∫ w in 0..H,
                C (t + v) * (starRingEnd ℂ) (C (t + w))) =
              C (t + v) * (starRingEnd ℂ) (A t)
            calc
              _ = C (t + v) *
                  (∫ w in 0..H, (starRingEnd ℂ) (C (t + w))) :=
                intervalIntegral.integral_const_mul
                  (C (t + v))
                  (fun w => (starRingEnd ℂ) (C (t + w)))
              _ = C (t + v) * (starRingEnd ℂ) (A t) := by
                rw [hconj]
      _ = A t * (starRingEnd ℂ) (A t) := by
        change
          (∫ v in 0..H,
            C (t + v) * (starRingEnd ℂ) (A t)) =
          (∫ v in 0..H, C (t + v)) * (starRingEnd ℂ) (A t)
        exact
          intervalIntegral.integral_mul_const
            ((starRingEnd ℂ) (A t)) (fun v => C (t + v))
  rw [hpseudo, hord]
  simp only [C] at hinnerPseudo hinnerOrdinary
  simp_rw [hinnerPseudo, hinnerOrdinary]
  exact norm_integral_mul_self_le_norm_integral_mul_conj_self
    A (by linarith)

end HardyTheorem
