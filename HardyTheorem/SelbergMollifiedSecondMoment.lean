import HardyTheorem.SelbergMollifier

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-!
# A genuine second-moment bound for the sign-preserving Selberg mollification

The real function used in the zero-counting argument is

`hardyZ t * normSq (M_X (1 / 2 + I * t))`.

Its square is therefore `|zeta|^2 * |M_X|^4`, not the second moment of
`zeta * M_X`.  The bound below keeps both mollifier factors.  It combines the
elementary dyadic pointwise estimate for zeta, derived from the first zeta
approximation, with the finite-sum pointwise estimate `|M_X| <= 2 * sqrt X`.
The resulting `O(X^2 T^2)` estimate is deliberately coarse but unconditional.
-/

/-- The square of the sign-preserving mollified Hardy function contains two
copies of the mollifier energy. -/
theorem sq_selbergMoebiusMollifiedHardyZ_eq_normSq_zeta_mul_normSq_mollifier_sq
    (X : ℕ) (t : ℝ) :
    selbergMoebiusMollifiedHardyZ X t ^ 2 =
      Complex.normSq
          (riemannZeta ((1 / 2 : ℂ) + I * t)) *
        Complex.normSq
            (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) ^ 2 := by
  rw [selbergMoebiusMollifiedHardyZ, selbergMollifiedHardyZ]
  have hzeta : hardyZ t ^ 2 =
      Complex.normSq (riemannZeta ((1 / 2 : ℂ) + I * t)) := by
    rw [← sq_abs, abs_hardyZ_eq_norm_riemannZeta,
      Complex.normSq_eq_norm_sq]
  rw [mul_pow, hzeta]
  rfl

private theorem norm_selbergMoebiusMollifier_le_two_sqrt
    {X : ℕ} (hX : 2 ≤ X) (t : ℝ) :
    ‖selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)‖ ≤
      2 * Real.sqrt X := by
  unfold selbergMoebiusMollifier selbergMollifier
  calc
    ‖∑ n ∈ Finset.Icc 1 X,
        (selbergMoebiusCoeff X n : ℂ) *
          (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))‖ ≤
        ∑ n ∈ Finset.Icc 1 X,
          ‖(selbergMoebiusCoeff X n : ℂ) *
            (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
      have hnpos : 0 < n := by omega
      have hcoeff : ‖(selbergMoebiusCoeff X n : ℂ)‖ ≤ 1 := by
        simpa [Complex.norm_real, Real.norm_eq_abs] using
          abs_selbergMoebiusCoeff_le_one hX hn1 hnX
      have hpow :
          ‖(n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ = Real.sqrt n := by
        rw [Complex.norm_natCast_cpow_of_pos hnpos]
        simp [Real.sqrt_eq_rpow]
      rw [norm_mul, norm_div, norm_one, hpow, one_div]
      exact mul_le_of_le_one_left
        (inv_nonneg.mpr (Real.sqrt_nonneg n)) hcoeff
    _ ≤ 2 * Real.sqrt X := sum_inv_sqrt_Icc_one_le_two_sqrt X

/-- An unconditional dyadic `L2` bound for the actual sign-preserving
Selberg-mollified Hardy function.  In particular, this bounds
`|zeta|^2 * |M_X|^4`; no second-moment estimate is assumed as an input. -/
theorem exists_integral_sq_selbergMoebiusMollifiedHardyZ_le :
    ∃ C T0 : ℝ, 0 < C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T : ℝ, T0 ≤ T →
        (∫ t in T..2 * T,
            selbergMoebiusMollifiedHardyZ X t ^ 2) ≤
          C * (X : ℝ) ^ 2 * T ^ 2 := by
  obtain ⟨A, T0, hA, hT0, hzeta⟩ :=
    exists_norm_riemannZeta_critical_line_le_sqrt
  refine ⟨16 * A ^ 2, T0, by positivity, hT0, ?_⟩
  intro X hX T hT
  have hT1 : 1 ≤ T := hT0.trans hT
  have hT0' : 0 ≤ T := zero_le_one.trans hT1
  have hinterval : T ≤ 2 * T := by linarith
  let K : ℝ := 16 * A ^ 2 * (X : ℝ) ^ 2 * T
  have hpoint : ∀ t ∈ Icc T (2 * T),
      selbergMoebiusMollifiedHardyZ X t ^ 2 ≤ K := by
    intro t ht
    have hz := hzeta T t hT ht
    have hM := norm_selbergMoebiusMollifier_le_two_sqrt hX t
    have hzsq :
        Complex.normSq (riemannZeta ((1 / 2 : ℂ) + I * t)) ≤
          A ^ 2 * T := by
      rw [Complex.normSq_eq_norm_sq]
      have hsqrt : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hT0'
      nlinarith [norm_nonneg
        (riemannZeta ((1 / 2 : ℂ) + I * t)), Real.sqrt_nonneg T]
    have hMsq :
        Complex.normSq
            (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) ≤
          4 * (X : ℝ) := by
      rw [Complex.normSq_eq_norm_sq]
      have hsqrt : (Real.sqrt (X : ℝ)) ^ 2 = (X : ℝ) :=
        Real.sq_sqrt (by positivity)
      nlinarith [norm_nonneg
        (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)),
        Real.sqrt_nonneg (X : ℝ)]
    rw [sq_selbergMoebiusMollifiedHardyZ_eq_normSq_zeta_mul_normSq_mollifier_sq]
    dsimp only [K]
    calc
      Complex.normSq (riemannZeta ((1 / 2 : ℂ) + I * t)) *
          Complex.normSq
              (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) ^ 2 ≤
          (A ^ 2 * T) * (4 * (X : ℝ)) ^ 2 := by
        gcongr
        exact Complex.normSq_nonneg _
      _ = 16 * A ^ 2 * (X : ℝ) ^ 2 * T := by ring
  have hfunInt : IntervalIntegrable
      (fun t : ℝ => selbergMoebiusMollifiedHardyZ X t ^ 2)
      volume T (2 * T) :=
    ((continuous_selbergMoebiusMollifiedHardyZ X).pow 2).intervalIntegrable
      T (2 * T)
  have hconstInt : IntervalIntegrable (fun _t : ℝ => K)
      volume T (2 * T) := continuous_const.intervalIntegrable T (2 * T)
  calc
    (∫ t in T..2 * T, selbergMoebiusMollifiedHardyZ X t ^ 2) ≤
        ∫ _t in T..2 * T, K :=
      intervalIntegral.integral_mono_on hinterval hfunInt hconstInt hpoint
    _ = T * K := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring
    _ = (16 * A ^ 2) * (X : ℝ) ^ 2 * T ^ 2 := by
      dsimp only [K]
      ring

end HardyTheorem
