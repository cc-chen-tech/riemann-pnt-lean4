import HardyTheorem.SelbergMollifiedCoefficientEnergy
import MathlibAux.GaussianDirichletPolynomialSchur
import PrimeNumberTheorem.CarlsonDivisorSquare

/-!
# Gaussian mean square of the finite Selberg-mollified zeta polynomial

This file closes the finite-polynomial arithmetic required after a
square-root approximate functional equation.  The crude divisor-square
majorant costs four powers of a logarithm, but no power of the height.
-/

open Complex MeasureTheory
open scoped BigOperators ArithmeticFunction
open PrimeNumberTheorem.CarlsonZeroDensity

namespace HardyTheorem

private theorem fourfoldDivisor_inv_sum_le_two_mul_log_pow_four
    {U : ℕ} (hU : 1 ≤ U) :
    (∑ n ∈ Finset.Icc 1 U,
        (fourfoldDivisorCount n : ℝ) * (n : ℝ)⁻¹) ≤
      2 * (1 + Real.log U) ^ 4 := by
  have hAbel := fourfoldDivisorSum_mul_le_prefixSlope
    (f := fun n : ℕ => (n : ℝ)⁻¹) (L := 1) (U := U)
    (by norm_num) hU
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by
      intro m n hm hmn hn
      have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
      exact inv_anti₀ hmpos (by exact_mod_cast hmn))
  have hharmonic :
      (∑ n ∈ Finset.Icc 1 U, (n : ℝ)⁻¹) = (harmonic U : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
  have hlog0 : 0 ≤ Real.log U :=
    Real.log_nonneg (by exact_mod_cast hU)
  have hA0 : 0 ≤ 1 + Real.log U := by linarith
  have hharmonicLe : (harmonic U : ℝ) ≤ 1 + Real.log U :=
    harmonic_le_one_add_log U
  calc
    (∑ n ∈ Finset.Icc 1 U,
        (fourfoldDivisorCount n : ℝ) * (n : ℝ)⁻¹) =
        ∑ n ∈ Finset.Icc 1 U,
          (n : ℝ)⁻¹ * (fourfoldDivisorCount n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ (1 + Real.log U) ^ 3 *
        ((1 : ℝ) * (1 : ℝ)⁻¹ +
          ∑ n ∈ Finset.Icc 1 U, (n : ℝ)⁻¹) := by
      simpa using hAbel
    _ = (1 + Real.log U) ^ 3 * (1 + (harmonic U : ℝ)) := by
      rw [hharmonic]
      norm_num
    _ ≤ (1 + Real.log U) ^ 3 *
        (2 * (1 + Real.log U)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hA0 3)
      linarith
    _ = 2 * (1 + Real.log U) ^ 4 := by ring

private theorem normSq_selbergMollifiedCriticalLineCoeff_le_fourfold_inv
    {N X k : ℕ} (hX : 2 ≤ X) (hk : k ∈ Finset.Icc 1 (N * X)) :
    Complex.normSq (selbergMollifiedCriticalLineCoeff N X k) ≤
      (fourfoldDivisorCount k : ℝ) * (k : ℝ)⁻¹ := by
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1
  have habs := abs_selbergMollifiedDirichletCoeff_le_card_divisorsAntidiagonal
    (N := N) (X := X) (k := k) hX
  have hcardNat := card_divisorsAntidiagonal_sq_le_fourfoldDivisorCount hkpos.ne'
  have hcard :
      (k.divisorsAntidiagonal.card : ℝ) ^ 2 ≤
        (fourfoldDivisorCount k : ℝ) := by
    exact_mod_cast hcardNat
  have hhalf : ‖(k : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt k := by
    rw [Complex.norm_natCast_cpow_of_pos hkpos]
    simp [Real.sqrt_eq_rpow]
  have hsqrtPos : 0 < Real.sqrt k :=
    Real.sqrt_pos.2 (by exact_mod_cast hkpos)
  have hcoeffNorm :
      ‖(selbergMollifiedDirichletCoeff N X k : ℂ)‖ ≤
        (k.divisorsAntidiagonal.card : ℝ) := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using habs
  rw [Complex.normSq_eq_norm_sq, selbergMollifiedCriticalLineCoeff,
    norm_mul, norm_inv, hhalf]
  calc
    (‖(selbergMollifiedDirichletCoeff N X k : ℂ)‖ *
        (Real.sqrt k)⁻¹) ^ 2 ≤
      ((k.divisorsAntidiagonal.card : ℝ) *
        (Real.sqrt k)⁻¹) ^ 2 := by
      have hinv0 : 0 ≤ (Real.sqrt k)⁻¹ := inv_nonneg.mpr hsqrtPos.le
      have hmul := mul_le_mul_of_nonneg_right hcoeffNorm hinv0
      exact (sq_le_sq₀
        (mul_nonneg
          (norm_nonneg (selbergMollifiedDirichletCoeff N X k : ℂ)) hinv0)
        (mul_nonneg (Nat.cast_nonneg _) hinv0)).2 hmul
    _ = (k.divisorsAntidiagonal.card : ℝ) ^ 2 * (k : ℝ)⁻¹ := by
      rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
    _ ≤ (fourfoldDivisorCount k : ℝ) * (k : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr (Nat.cast_nonneg k))

/-- The full critical-line convolution coefficient energy is polylogarithmic.
This includes the incomplete range above `min N X`. -/
theorem sum_normSq_selbergMollifiedCriticalLineCoeff_full_le
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) :
    (∑ k ∈ Finset.Icc 1 (N * X),
        Complex.normSq (selbergMollifiedCriticalLineCoeff N X k)) ≤
      2 * (1 + Real.log (N * X)) ^ 4 := by
  have hNX : 1 ≤ N * X := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
    (Nat.ne_of_gt (Nat.zero_lt_of_lt hN)) (by omega))
  calc
    (∑ k ∈ Finset.Icc 1 (N * X),
        Complex.normSq (selbergMollifiedCriticalLineCoeff N X k)) ≤
      ∑ k ∈ Finset.Icc 1 (N * X),
        (fourfoldDivisorCount k : ℝ) * (k : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      exact normSq_selbergMollifiedCriticalLineCoeff_le_fourfold_inv hX hk
    _ ≤ 2 * (1 + Real.log (N * X)) ^ 4 :=
      by simpa only [Nat.cast_mul] using
        (fourfoldDivisor_inv_sum_le_two_mul_log_pow_four hNX)

/-- Exact logarithmic-frequency polynomial obtained by multiplying the first
zeta sum by the linearly tapered Selberg mollifier. -/
theorem criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_eq_exponentialPolynomial
    (N X : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) =
      MathlibAux.exponentialPolynomial (Finset.Icc 1 (N * X))
        (selbergMollifiedCriticalLineCoeff N X)
        (fun k => -Real.log k) t := by
  rw [criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_eq_convolutionSum]
  unfold MathlibAux.exponentialPolynomial
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : k ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hk).1
  rw [inv_nat_cpow_criticalLine_eq_exp hk0 t]
  dsimp only [selbergMollifiedCriticalLineCoeff]
  push_cast
  ring

/-- Gaussian second moment of the finite mollified zeta polynomial.  The
length hypothesis is exactly the sub-half-length condition needed after a
square-root zeta approximation. -/
theorem integral_gaussian_normSq_criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_le
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X)
    {Delta : ℝ} (hDelta : 2 * ((N * X : ℕ) : ℝ) ≤ Delta) (w : ℝ) :
    (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          ((∑ m ∈ Finset.Icc 1 N,
              1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
            selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) ≤
      Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        MathlibAux.gaussianBucketSchurConstant *
          (2 * (1 + Real.log (N * X)) ^ 4) := by
  have hNXpos : 0 < N * X := Nat.mul_pos
    (Nat.zero_lt_of_lt hN) (by omega)
  have hbase :=
    MathlibAux.integral_gaussian_mul_normSq_dirichletPolynomial_le
      hNXpos hDelta w (Finset.Icc 1 (N * X))
      (fun k hk => (Finset.mem_Icc.mp hk).1)
      (fun k hk => (Finset.mem_Icc.mp hk).2)
      (selbergMollifiedCriticalLineCoeff N X)
  rw [show (fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          ((∑ m ∈ Finset.Icc 1 N,
              1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
            selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) =
      fun t : ℝ =>
        Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            (MathlibAux.exponentialPolynomial (Finset.Icc 1 (N * X))
              (selbergMollifiedCriticalLineCoeff N X)
              (fun k => -Real.log k) t) by
    funext t
    rw [criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_eq_exponentialPolynomial]]
  refine hbase.trans ?_
  have henergy :=
    sum_normSq_selbergMollifiedCriticalLineCoeff_full_le hN hX
  have hfactor :
      0 ≤ Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        MathlibAux.gaussianBucketSchurConstant :=
    mul_nonneg (Real.sqrt_nonneg _)
      MathlibAux.gaussianBucketSchurConstant_pos.le
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Complex.normSq_eq_norm_sq] using henergy) hfactor

end HardyTheorem
