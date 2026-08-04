import HardyTheorem.HardyModelApproximation
import HardyTheorem.SelbergSqrtZetaAbsLower

open Complex Set
open scoped BigOperators

namespace HardyTheorem

/-!
# Pointwise signed approximation for the square-root-zeta mollifier

This module attaches the exact sign-preserving mollifier weight to the
uniform first Hardy approximation.  The resulting model is finite: it is the
real part of the `thetaModel`-rotated first zeta Dirichlet polynomial,
multiplied by the squared norm of the finite square-root-zeta mollifier.
-/

/-- The finite, real `thetaModel` approximation to the square-root-zeta
mollified Hardy function on the dyadic interval based at `T`. -/
noncomputable def selbergSqrtZetaSignedThetaModel
    (kappa T : ℝ) (X : ℕ) (t : ℝ) : ℝ :=
  (Complex.exp (I * kappa) * Complex.exp (I * thetaModel t) *
      (∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
      (Complex.normSq
        (selbergSqrtZetaMollifier X
          ((1 / 2 : ℂ) + I * t)) : ℂ)).re

/-- The genuine mollified Hardy function is the real part of the exactly
Gamma-rotated zeta value times the nonnegative mollifier weight. -/
theorem selbergSqrtZetaMollifiedHardyZ_eq_rotatedZeta_re_mul_normSq
    (X : ℕ) (t : ℝ) :
    selbergSqrtZetaMollifiedHardyZ X t =
      (Complex.exp (I * thetaPhase t) *
          riemannZeta ((1 / 2 : ℂ) + I * t) *
        (Complex.normSq
          (selbergSqrtZetaMollifier X
            ((1 / 2 : ℂ) + I * t)) : ℂ)).re := by
  rw [selbergSqrtZetaMollifiedHardyZ, selbergMollifiedHardyZ,
    hardyZ_eq_re_exp_I_thetaPhase_mul_zeta]
  unfold selbergSqrtZetaMollifier
  simp

/-- The strongest direct pointwise estimate: the first Hardy approximation
error is multiplied by the actual squared mollifier norm.  The constants are
uniform in `X` and in `t ∈ [T, 2T]`. -/
theorem
    exists_abs_selbergSqrtZetaMollifiedHardyZ_sub_signedThetaModel_le_normSq :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, ∀ T t : ℝ,
        T0 ≤ T → t ∈ Icc T (2 * T) →
          |selbergSqrtZetaMollifiedHardyZ X t -
              selbergSqrtZetaSignedThetaModel kappa T X t| ≤
            C / Real.sqrt T *
              Complex.normSq
                (selbergSqrtZetaMollifier X
                  ((1 / 2 : ℂ) + I * t)) := by
  obtain ⟨kappa, C, T0, hC, hT0, happ⟩ :=
    exists_norm_rotated_riemannZeta_sub_thetaModel_dirichletPolynomial_le_inv_sqrt
  refine ⟨kappa, C, T0, hC, hT0, ?_⟩
  intro X T t hT ht
  let A : ℂ :=
    Complex.exp (I * thetaPhase t) *
      riemannZeta ((1 / 2 : ℂ) + I * t)
  let B : ℂ :=
    Complex.exp (I * kappa) * Complex.exp (I * thetaModel t) *
      (∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))
  let r : ℝ :=
    Complex.normSq
      (selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t))
  have happrox : ‖A - B‖ ≤ C / Real.sqrt T := by
    simpa only [A, B] using happ T t hT ht
  have hr : 0 ≤ r := Complex.normSq_nonneg _
  rw [selbergSqrtZetaMollifiedHardyZ_eq_rotatedZeta_re_mul_normSq]
  change |(A * (r : ℂ)).re - (B * (r : ℂ)).re| ≤
    C / Real.sqrt T * r
  have hre :
      (A * (r : ℂ)).re - (B * (r : ℂ)).re =
        ((A - B) * (r : ℂ)).re := by
    simp [mul_re]
    ring
  rw [hre]
  calc
    |(((A - B) * (r : ℂ)).re)| ≤ ‖(A - B) * (r : ℂ)‖ :=
      Complex.abs_re_le_norm _
    _ = ‖A - B‖ * r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    _ ≤ (C / Real.sqrt T) * r :=
      mul_le_mul_of_nonneg_right happrox hr

/-- Replacing the actual mollifier norm by its explicit finite coefficient
majorant preserves uniformity in the dyadic height variable. -/
theorem
    exists_abs_selbergSqrtZetaMollifiedHardyZ_sub_signedThetaModel_le_majorant :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, ∀ T t : ℝ,
        T0 ≤ T → t ∈ Icc T (2 * T) →
          |selbergSqrtZetaMollifiedHardyZ X t -
              selbergSqrtZetaSignedThetaModel kappa T X t| ≤
            C / Real.sqrt T *
              selbergSqrtZetaMollifierMajorant X ^ 2 := by
  obtain ⟨kappa, C, T0, hC, hT0, happ⟩ :=
    exists_abs_selbergSqrtZetaMollifiedHardyZ_sub_signedThetaModel_le_normSq
  refine ⟨kappa, C, T0, hC, hT0, ?_⟩
  intro X T t hT ht
  have hpoint := happ X T t hT ht
  have hM :=
    norm_selbergSqrtZetaMollifier_criticalLine_le_majorant X t
  have hmajorant : 0 ≤ selbergSqrtZetaMollifierMajorant X := by
    unfold selbergSqrtZetaMollifierMajorant
    positivity
  have hfactor : 0 ≤ C / Real.sqrt T := by positivity
  have hsq :
      ‖selbergSqrtZetaMollifier X
          ((1 / 2 : ℂ) + I * t)‖ ^ 2 ≤
        selbergSqrtZetaMollifierMajorant X ^ 2 := by
    nlinarith [norm_nonneg
      (selbergSqrtZetaMollifier X
        ((1 / 2 : ℂ) + I * t))]
  calc
    |selbergSqrtZetaMollifiedHardyZ X t -
        selbergSqrtZetaSignedThetaModel kappa T X t| ≤
        C / Real.sqrt T *
          Complex.normSq
            (selbergSqrtZetaMollifier X
              ((1 / 2 : ℂ) + I * t)) := hpoint
    _ ≤ C / Real.sqrt T *
          selbergSqrtZetaMollifierMajorant X ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact mul_le_mul_of_nonneg_left hsq hfactor

/-- With `X ≥ 2`, the elementary coefficient estimate gives the fully
explicit dyadic-uniform error `4 * C * X / sqrt T`. -/
theorem
    exists_abs_selbergSqrtZetaMollifiedHardyZ_sub_signedThetaModel_le_four_mul :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T t : ℝ,
        T0 ≤ T → t ∈ Icc T (2 * T) →
          |selbergSqrtZetaMollifiedHardyZ X t -
              selbergSqrtZetaSignedThetaModel kappa T X t| ≤
            4 * C * X / Real.sqrt T := by
  obtain ⟨kappa, C, T0, hC, hT0, happ⟩ :=
    exists_abs_selbergSqrtZetaMollifiedHardyZ_sub_signedThetaModel_le_majorant
  refine ⟨kappa, C, T0, hC, hT0, ?_⟩
  intro X hX T t hT ht
  have hpoint := happ X T t hT ht
  have hmajorant :=
    selbergSqrtZetaMollifierMajorant_le_two_sqrt hX
  have hmajorant_nonneg : 0 ≤ selbergSqrtZetaMollifierMajorant X := by
    unfold selbergSqrtZetaMollifierMajorant
    positivity
  have hXnonneg : 0 ≤ (X : ℝ) := by positivity
  have hsqrt_sq : (Real.sqrt X) ^ 2 = X :=
    Real.sq_sqrt hXnonneg
  have hsq :
      selbergSqrtZetaMollifierMajorant X ^ 2 ≤ 4 * X := by
    nlinarith [Real.sqrt_nonneg (X : ℝ)]
  have hT1 : 1 ≤ T := hT0.trans hT
  have hfactor : 0 ≤ C / Real.sqrt T := by positivity
  calc
    |selbergSqrtZetaMollifiedHardyZ X t -
        selbergSqrtZetaSignedThetaModel kappa T X t| ≤
        C / Real.sqrt T *
          selbergSqrtZetaMollifierMajorant X ^ 2 := hpoint
    _ ≤ C / Real.sqrt T * (4 * X) :=
      mul_le_mul_of_nonneg_left hsq hfactor
    _ = 4 * C * X / Real.sqrt T := by ring

/-- The two-point consequence needed for autocorrelation estimates.  Both
heights may vary independently in the same dyadic interval, while the same
constants and the same explicit error budget apply to both. -/
theorem
    exists_abs_selbergSqrtZetaMollifiedAutocorrelation_sub_signedThetaModel_le :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T t u : ℝ,
        T0 ≤ T → t ∈ Icc T (2 * T) → u ∈ Icc T (2 * T) →
          |selbergSqrtZetaMollifiedHardyZ X t *
                selbergSqrtZetaMollifiedHardyZ X u -
              selbergSqrtZetaSignedThetaModel kappa T X t *
                selbergSqrtZetaSignedThetaModel kappa T X u| ≤
            (4 * C * X / Real.sqrt T) *
              (|selbergSqrtZetaSignedThetaModel kappa T X t| +
                |selbergSqrtZetaSignedThetaModel kappa T X u| +
                4 * C * X / Real.sqrt T) := by
  obtain ⟨kappa, C, T0, hC, hT0, happ⟩ :=
    exists_abs_selbergSqrtZetaMollifiedHardyZ_sub_signedThetaModel_le_four_mul
  refine ⟨kappa, C, T0, hC, hT0, ?_⟩
  intro X hX T t u hT ht hu
  let F : ℝ → ℝ := selbergSqrtZetaMollifiedHardyZ X
  let G : ℝ → ℝ := selbergSqrtZetaSignedThetaModel kappa T X
  let E : ℝ := 4 * C * X / Real.sqrt T
  have htErr : |F t - G t| ≤ E := happ X hX T t hT ht
  have huErr : |F u - G u| ≤ E := happ X hX T u hT hu
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hFu : |F u| ≤ |G u| + E := by
    calc
      |F u| = |(F u - G u) + G u| := by ring_nf
      _ ≤ |F u - G u| + |G u| := abs_add_le _ _
      _ ≤ E + |G u| := by
        simpa only [add_comm] using add_le_add_left huErr |G u|
      _ = |G u| + E := by ring
  have hdecomp :
      F t * F u - G t * G u =
        (F t - G t) * F u + G t * (F u - G u) := by
    ring
  change |F t * F u - G t * G u| ≤
    E * (|G t| + |G u| + E)
  rw [hdecomp]
  calc
    |(F t - G t) * F u + G t * (F u - G u)| ≤
        |(F t - G t) * F u| + |G t * (F u - G u)| :=
      abs_add_le _ _
    _ = |F t - G t| * |F u| + |G t| * |F u - G u| := by
      rw [abs_mul, abs_mul]
    _ ≤
        E * (|G u| + E) + |G t| * E := by
      exact add_le_add
        (mul_le_mul htErr hFu (abs_nonneg _) hE)
        (mul_le_mul_of_nonneg_left huErr (abs_nonneg _))
    _ = E * (|G t| + |G u| + E) := by ring

end HardyTheorem
