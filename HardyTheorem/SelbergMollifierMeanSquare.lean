import HardyTheorem.SelbergMollifier
import MathlibAux.LogDirichletPolynomialMeanSquare
import Mathlib.NumberTheory.Harmonic.Bounds

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem

/-!
# Mean square of Selberg's finite mollifier

On the critical line, the finite Moebius mollifier is a logarithmic-frequency
exponential polynomial.  The global logarithmic Hilbert inequality therefore
gives an interval second-moment estimate with constants independent of the
interval endpoints.
-/

/-- The coefficient of the logarithmic exponential polynomial obtained by
restricting Selberg's Moebius mollifier to the critical line. -/
noncomputable def selbergMoebiusCriticalLineCoeff (X n : ℕ) : ℂ :=
  (selbergMoebiusCoeff X n : ℂ) *
    ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹

/-- Exact finite logarithmic-frequency representation of Selberg's Moebius
mollifier on the critical line.  The time is reflected because a Dirichlet
monomial has frequency `-log n`. -/
theorem selbergMoebiusMollifier_criticalLine_eq_logExponentialPolynomial
    (X : ℕ) (t : ℝ) :
    selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) =
      MathlibAux.exponentialPolynomial (Finset.Icc 1 X)
        (selbergMoebiusCriticalLineCoeff X) (fun n => Real.log n) (-t) := by
  unfold selbergMoebiusMollifier selbergMollifier
  unfold MathlibAux.exponentialPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    have hn1 := (Finset.mem_Icc.mp hn).1
    omega
  rw [inv_nat_cpow_criticalLine_eq_exp hn0 t]
  dsimp only [selbergMoebiusCriticalLineCoeff]
  change
    (selbergMoebiusCoeff X n : ℂ) *
        (((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
          Complex.exp ((-I * (Real.log n : ℂ)) * t)) =
      ((selbergMoebiusCoeff X n : ℂ) *
          ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹) *
        Complex.exp (I * ((Real.log n : ℂ) * ((-t : ℝ) : ℂ)))
  rw [show Complex.exp ((-I * (Real.log n : ℂ)) * t) =
      Complex.exp (I * ((Real.log n : ℂ) * ((-t : ℝ) : ℂ))) by
    congr 1
    push_cast
    ring]
  ring

/-- The coefficient energy of the critical-line Selberg mollifier is at most
the length `X` of its support. -/
theorem sum_normSq_selbergMoebiusCriticalLineCoeff_le
    {X : ℕ} (hX : 2 ≤ X) :
    (∑ n ∈ Finset.Icc 1 X,
        Complex.normSq (selbergMoebiusCriticalLineCoeff X n)) ≤ X := by
  calc
    (∑ n ∈ Finset.Icc 1 X,
        Complex.normSq (selbergMoebiusCriticalLineCoeff X n)) ≤
        ∑ _n ∈ Finset.Icc 1 X, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
      have hnpos : 0 < n := by omega
      have hcoeff : ‖(selbergMoebiusCoeff X n : ℂ)‖ ≤ 1 := by
        simpa [Complex.norm_real, Real.norm_eq_abs] using
          abs_selbergMoebiusCoeff_le_one hX hn1 hnX
      have hhalf : ‖(n : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt n := by
        rw [Complex.norm_natCast_cpow_of_pos hnpos]
        simp [Real.sqrt_eq_rpow]
      have hsqrt_pos : 0 < Real.sqrt n :=
        Real.sqrt_pos.2 (by exact_mod_cast hnpos)
      have hsqrt_one : 1 ≤ Real.sqrt n := by
        rw [Real.one_le_sqrt]
        exact_mod_cast hn1
      have hinv : ‖((n : ℂ) ^ (1 / 2 : ℂ))⁻¹‖ ≤ 1 := by
        rw [norm_inv, hhalf]
        exact (inv_le_one₀ hsqrt_pos).2 hsqrt_one
      have hnorm : ‖selbergMoebiusCriticalLineCoeff X n‖ ≤ 1 := by
        rw [selbergMoebiusCriticalLineCoeff, norm_mul]
        nlinarith [norm_nonneg (selbergMoebiusCoeff X n : ℂ),
          norm_nonneg (((n : ℂ) ^ (1 / 2 : ℂ))⁻¹)]
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (selbergMoebiusCriticalLineCoeff X n)]
    _ = X := by
      simp [Nat.card_Icc]

/-- Each critical-line mollifier coefficient has square norm at most `1/n`.
This retains the square-root decay which is lost in the coarser support-size
bound above. -/
theorem normSq_selbergMoebiusCriticalLineCoeff_le_inv
    {X n : ℕ} (hX : 2 ≤ X) (hn1 : 1 ≤ n) (hnX : n ≤ X) :
    Complex.normSq (selbergMoebiusCriticalLineCoeff X n) ≤ (n : ℝ)⁻¹ := by
  have hnpos : 0 < n := by omega
  have hcoeff : ‖(selbergMoebiusCoeff X n : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using
      abs_selbergMoebiusCoeff_le_one hX hn1 hnX
  have hhalf : ‖(n : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt n := by
    rw [Complex.norm_natCast_cpow_of_pos hnpos]
    simp [Real.sqrt_eq_rpow]
  have hsqrt_pos : 0 < Real.sqrt n :=
    Real.sqrt_pos.2 (by exact_mod_cast hnpos)
  have hnorm :
      ‖selbergMoebiusCriticalLineCoeff X n‖ ≤ (Real.sqrt n)⁻¹ := by
    rw [selbergMoebiusCriticalLineCoeff, norm_mul, norm_inv, hhalf]
    simpa using
      mul_le_mul_of_nonneg_right hcoeff (inv_nonneg.mpr hsqrt_pos.le)
  rw [Complex.normSq_eq_norm_sq]
  have hsquare :
      ‖selbergMoebiusCriticalLineCoeff X n‖ ^ 2 ≤
        ((Real.sqrt n)⁻¹) ^ 2 := by
    nlinarith [norm_nonneg (selbergMoebiusCriticalLineCoeff X n),
      inv_nonneg.mpr hsqrt_pos.le]
  calc
    ‖selbergMoebiusCriticalLineCoeff X n‖ ^ 2 ≤
        ((Real.sqrt n)⁻¹) ^ 2 := hsquare
    _ = (n : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (by positivity)]

/-- The exact square-root decay improves the coefficient energy from `O(X)`
to the harmonic bound `1 + log X`. -/
theorem sum_normSq_selbergMoebiusCriticalLineCoeff_le_one_add_log
    {X : ℕ} (hX : 2 ≤ X) :
    (∑ n ∈ Finset.Icc 1 X,
        Complex.normSq (selbergMoebiusCriticalLineCoeff X n)) ≤
      1 + Real.log X := by
  calc
    (∑ n ∈ Finset.Icc 1 X,
        Complex.normSq (selbergMoebiusCriticalLineCoeff X n)) ≤
        ∑ n ∈ Finset.Icc 1 X, ((n : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      exact normSq_selbergMoebiusCriticalLineCoeff_le_inv hX
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
    _ = (harmonic X : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]
    _ ≤ 1 + Real.log X := harmonic_le_one_add_log X

/-- A uniform interval second-moment bound for Selberg's finite Moebius
mollifier.  Both the interval length and endpoint cost are explicit. -/
theorem integral_normSq_selbergMoebiusMollifier_le
    {X : ℕ} (hX : 2 ≤ X) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b,
        Complex.normSq
          (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) ≤
      ((b - a) + 4 * (5 * Real.pi + 4) * X) * X := by
  let P : ℝ → ℂ := fun t =>
    MathlibAux.exponentialPolynomial (Finset.Icc 1 X)
      (selbergMoebiusCriticalLineCoeff X) (fun n => Real.log n) t
  have hrewrite :
      (∫ t in a..b,
          Complex.normSq
            (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) =
        ∫ t in a..b, Complex.normSq (P (-t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact congrArg Complex.normSq
      (selbergMoebiusMollifier_criticalLine_eq_logExponentialPolynomial X t)
  have hreflect :
      (∫ t in a..b, Complex.normSq (P (-t))) =
        ∫ t in -b..-a, Complex.normSq (P t) := by
    exact intervalIntegral.integral_comp_neg
      (f := fun t : ℝ => Complex.normSq (P t)) (a := a) (b := b)
  rw [hrewrite, hreflect]
  have hXpos : 0 < X := by omega
  have hpositive : ∀ n ∈ Finset.Icc 1 X, n ≠ 0 := by
    intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    omega
  have hupper : ∀ n ∈ Finset.Icc 1 X, n ≤ X := by
    intro n hn
    exact (Finset.mem_Icc.mp hn).2
  have hbase :=
    MathlibAux.integral_normSq_logExponentialPolynomial_le_of_upper
      hXpos (Finset.Icc 1 X) (selbergMoebiusCriticalLineCoeff X)
        hpositive hupper (a := -b) (b := -a)
  have hbase' :
      (∫ t in -b..-a, Complex.normSq (P t)) ≤
        ((b - a) + 4 * (5 * Real.pi + 4) * X) *
          ∑ n ∈ Finset.Icc 1 X,
            Complex.normSq (selbergMoebiusCriticalLineCoeff X n) := by
    dsimp only [P]
    convert hbase using 1
    ring
  have hfactor :
      0 ≤ (b - a) + 4 * (5 * Real.pi + 4) * (X : ℝ) := by
    have hlength : 0 ≤ b - a := sub_nonneg.mpr hab
    positivity
  calc
    (∫ t in -b..-a, Complex.normSq (P t)) ≤
        ((b - a) + 4 * (5 * Real.pi + 4) * X) *
          ∑ n ∈ Finset.Icc 1 X,
            Complex.normSq (selbergMoebiusCriticalLineCoeff X n) := hbase'
    _ ≤ ((b - a) + 4 * (5 * Real.pi + 4) * X) * X :=
      mul_le_mul_of_nonneg_left
        (sum_normSq_selbergMoebiusCriticalLineCoeff_le hX) hfactor

/-- The logarithmic-energy version of the interval second-moment bound. -/
theorem integral_normSq_selbergMoebiusMollifier_le_one_add_log
    {X : ℕ} (hX : 2 ≤ X) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b,
        Complex.normSq
          (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) ≤
      ((b - a) + 4 * (5 * Real.pi + 4) * X) *
        (1 + Real.log X) := by
  let P : ℝ → ℂ := fun t =>
    MathlibAux.exponentialPolynomial (Finset.Icc 1 X)
      (selbergMoebiusCriticalLineCoeff X) (fun n => Real.log n) t
  have hrewrite :
      (∫ t in a..b,
          Complex.normSq
            (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) =
        ∫ t in a..b, Complex.normSq (P (-t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact congrArg Complex.normSq
      (selbergMoebiusMollifier_criticalLine_eq_logExponentialPolynomial X t)
  have hreflect :
      (∫ t in a..b, Complex.normSq (P (-t))) =
        ∫ t in -b..-a, Complex.normSq (P t) := by
    exact intervalIntegral.integral_comp_neg
      (f := fun t : ℝ => Complex.normSq (P t)) (a := a) (b := b)
  rw [hrewrite, hreflect]
  have hXpos : 0 < X := by omega
  have hpositive : ∀ n ∈ Finset.Icc 1 X, n ≠ 0 := by
    intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    omega
  have hupper : ∀ n ∈ Finset.Icc 1 X, n ≤ X := by
    intro n hn
    exact (Finset.mem_Icc.mp hn).2
  have hbase :=
    MathlibAux.integral_normSq_logExponentialPolynomial_le_of_upper
      hXpos (Finset.Icc 1 X) (selbergMoebiusCriticalLineCoeff X)
        hpositive hupper (a := -b) (b := -a)
  have hbase' :
      (∫ t in -b..-a, Complex.normSq (P t)) ≤
        ((b - a) + 4 * (5 * Real.pi + 4) * X) *
          ∑ n ∈ Finset.Icc 1 X,
            Complex.normSq (selbergMoebiusCriticalLineCoeff X n) := by
    dsimp only [P]
    convert hbase using 1
    ring
  have hfactor :
      0 ≤ (b - a) + 4 * (5 * Real.pi + 4) * (X : ℝ) := by
    have hlength : 0 ≤ b - a := sub_nonneg.mpr hab
    positivity
  exact hbase'.trans <|
    mul_le_mul_of_nonneg_left
      (sum_normSq_selbergMoebiusCriticalLineCoeff_le_one_add_log hX)
      hfactor

end HardyTheorem
