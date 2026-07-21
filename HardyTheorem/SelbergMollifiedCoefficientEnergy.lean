import HardyTheorem.SelbergMollifiedCoefficientArithmetic
import Mathlib.NumberTheory.Harmonic.Bounds

open Complex
open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# Energy of the complete-range Selberg-mollified coefficients

Below both truncation lengths the collected coefficient is `1` at the
constant term and `vonMangoldt k / log X` otherwise.  On the critical line
the additional square-root denominator therefore gives a pointwise energy
bound `1 / k`.  Summing retains this decay and costs only a harmonic factor.
-/

/-- The collected Selberg-mollified Dirichlet coefficient after restriction
to the critical line. -/
noncomputable def selbergMollifiedCriticalLineCoeff
    (N X k : ℕ) : ℂ :=
  (selbergMollifiedDirichletCoeff N X k : ℂ) *
    ((k : ℂ) ^ (1 / 2 : ℂ))⁻¹

/-- In the complete coefficient range, the critical-line coefficient energy
is at most `1 / k`.  For `k = 1` this uses the exact constant coefficient;
for `k > 1` it uses `vonMangoldt k ≤ log k ≤ log X`. -/
theorem normSq_selbergMollifiedCriticalLineCoeff_le_inv
    {N X k : ℕ} (hX : 2 ≤ X) (hk1 : 1 ≤ k)
    (hkN : k ≤ N) (hkX : k ≤ X) :
    Complex.normSq (selbergMollifiedCriticalLineCoeff N X k) ≤
      (k : ℝ)⁻¹ := by
  by_cases hk : k = 1
  · subst k
    simp [selbergMollifiedCriticalLineCoeff,
      selbergMollifiedDirichletCoeff_one hkN hkX]
  · have hkgt : 1 < k := lt_of_le_of_ne hk1 (Ne.symm hk)
    have hkpos : 0 < k := by omega
    have hlogX : 0 < Real.log X :=
      Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hlogk : 0 < Real.log k :=
      Real.log_pos (by exact_mod_cast hkgt)
    have hlogle : Real.log k ≤ Real.log X :=
      Real.log_le_log (by exact_mod_cast hkpos) (by exact_mod_cast hkX)
    have hvnonneg : 0 ≤ ArithmeticFunction.vonMangoldt k :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hvle : ArithmeticFunction.vonMangoldt k ≤ Real.log X :=
      ArithmeticFunction.vonMangoldt_le_log.trans hlogle
    have hratio_nonneg :
        0 ≤ ArithmeticFunction.vonMangoldt k / Real.log X :=
      div_nonneg hvnonneg hlogX.le
    have hratio_le :
        ArithmeticFunction.vonMangoldt k / Real.log X ≤ 1 := by
      exact (div_le_one hlogX).2 hvle
    have hcoeff :
        ‖((ArithmeticFunction.vonMangoldt k / Real.log X : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hratio_nonneg]
      exact hratio_le
    have hhalf : ‖(k : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt k := by
      rw [Complex.norm_natCast_cpow_of_pos hkpos]
      simp [Real.sqrt_eq_rpow]
    have hsqrt_pos : 0 < Real.sqrt k :=
      Real.sqrt_pos.2 (by exact_mod_cast hkpos)
    have hnorm :
        ‖selbergMollifiedCriticalLineCoeff N X k‖ ≤
          (Real.sqrt k)⁻¹ := by
      rw [selbergMollifiedCriticalLineCoeff,
        selbergMollifiedDirichletCoeff_eq_vonMangoldt_div_log
          hkgt hkN hkX,
        norm_mul, norm_inv, hhalf]
      simpa using mul_le_mul_of_nonneg_right hcoeff
        (inv_nonneg.mpr hsqrt_pos.le)
    rw [Complex.normSq_eq_norm_sq]
    have hsquare :
        ‖selbergMollifiedCriticalLineCoeff N X k‖ ^ 2 ≤
          ((Real.sqrt k)⁻¹) ^ 2 := by
      nlinarith [norm_nonneg (selbergMollifiedCriticalLineCoeff N X k),
        inv_nonneg.mpr hsqrt_pos.le]
    calc
      ‖selbergMollifiedCriticalLineCoeff N X k‖ ^ 2 ≤
          ((Real.sqrt k)⁻¹) ^ 2 := hsquare
      _ = (k : ℝ)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt (by positivity)]

/-- The complete-range coefficient energy is bounded by the corresponding
harmonic sum.  This is the finite-sum form that explicitly retains the
`1 / k` decay. -/
theorem sum_normSq_selbergMollifiedCriticalLineCoeff_le_harmonic
    {N X : ℕ} (_hN : 1 ≤ N) (hX : 2 ≤ X) :
    (∑ k ∈ Finset.Icc 1 (min N X),
        Complex.normSq (selbergMollifiedCriticalLineCoeff N X k)) ≤
      (harmonic (min N X) : ℝ) := by
  calc
    (∑ k ∈ Finset.Icc 1 (min N X),
        Complex.normSq (selbergMollifiedCriticalLineCoeff N X k)) ≤
        ∑ k ∈ Finset.Icc 1 (min N X), (k : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      exact normSq_selbergMollifiedCriticalLineCoeff_le_inv hX
        (Finset.mem_Icc.mp hk).1
        ((Finset.mem_Icc.mp hk).2.trans (min_le_left N X))
        ((Finset.mem_Icc.mp hk).2.trans (min_le_right N X))
    _ = (harmonic (min N X) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]

/-- The complete-range coefficient energy grows at most logarithmically in
the shorter of the two truncation lengths. -/
theorem sum_normSq_selbergMollifiedCriticalLineCoeff_le_one_add_log_min
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) :
    (∑ k ∈ Finset.Icc 1 (min N X),
        Complex.normSq (selbergMollifiedCriticalLineCoeff N X k)) ≤
      1 + Real.log ((min N X : ℕ) : ℝ) := by
  exact (sum_normSq_selbergMollifiedCriticalLineCoeff_le_harmonic hN hX).trans
    (by simpa only [Nat.cast_min] using
      harmonic_le_one_add_log (min N X))

/-- A convenient `O(1 + log X)` form of the complete-range coefficient
energy bound. -/
theorem sum_normSq_selbergMollifiedCriticalLineCoeff_le_one_add_log
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) :
    (∑ k ∈ Finset.Icc 1 (min N X),
        Complex.normSq (selbergMollifiedCriticalLineCoeff N X k)) ≤
      1 + Real.log X := by
  have hX1 : 1 ≤ X := by omega
  have hmin1 : 1 ≤ min N X := (Nat.le_min).2 ⟨hN, hX1⟩
  have hlog : Real.log ((min N X : ℕ) : ℝ) ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast (show 0 < min N X by omega))
      (by exact_mod_cast (min_le_right N X))
  exact (sum_normSq_selbergMollifiedCriticalLineCoeff_le_one_add_log_min hN hX).trans
    (by linarith)

end HardyTheorem
