import HardyTheorem.SelbergShortCollectedArithmetic

open Complex
open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# Low-range arithmetic of the collected Selberg short coefficient

When `1 < k <= min N X`, every divisor factorization occurring in the
outer short convolution is present.  The constant coefficient of the first
mollified polynomial contributes `b_X(k)`, while every nonconstant
coefficient contributes `vonMangoldt d / log X`.  This file records the
resulting exact divisor convolution and a conservative pointwise bound.
-/

/-- The ordinary divisor convolution of the von Mangoldt function with the
last Selberg Moebius coefficient. -/
noncomputable def selbergShortLowRangeVonMangoldtConvolution
    (X k : ℕ) : ℝ :=
  ∑ d ∈ k.divisors,
    ArithmeticFunction.vonMangoldt d * selbergMoebiusCoeff X (k / d)

/-- In the complete divisor range, the truncated outer convolution is the
last Moebius coefficient plus the von-Mangoldt--Moebius divisor convolution
divided by `log X`. -/
theorem selbergShortCollectedDirichletConvolution_eq_lowRange
    {N X k : ℕ} (hk : 1 < k) (hkN : k ≤ N) (hkX : k ≤ X) :
    selbergShortCollectedDirichletConvolution N X k =
      selbergMoebiusCoeff X k +
        selbergShortLowRangeVonMangoldtConvolution X k / Real.log X := by
  classical
  have hk0 : k ≠ 0 := by omega
  have hX1 : 1 ≤ X := by omega
  have hkNX : k ≤ N * X := by
    calc
      k ≤ N := hkN
      _ = N * 1 := by omega
      _ ≤ N * X := Nat.mul_le_mul_left N hX1
  have hpair :
      selbergMollifiedDirichletPairs (N * X) X k =
        k.divisorsAntidiagonal :=
    selbergMollifiedDirichletPairs_eq_divisorsAntidiagonal
      hk.le hkNX hkX
  have hone : 1 ∈ k.divisors := by simp [hk0]
  have hrest :
    (∑ d ∈ k.divisors.erase 1,
        selbergMollifiedDirichletCoeff N X d *
          selbergMoebiusCoeff X (k / d)) =
        selbergShortLowRangeVonMangoldtConvolution X k / Real.log X := by
    calc
      (∑ d ∈ k.divisors.erase 1,
          selbergMollifiedDirichletCoeff N X d *
            selbergMoebiusCoeff X (k / d)) =
          ∑ d ∈ k.divisors.erase 1,
          (ArithmeticFunction.vonMangoldt d / Real.log X) *
            selbergMoebiusCoeff X (k / d) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdDiv : d ∣ k := (Nat.mem_divisors.mp (Finset.mem_of_mem_erase hd)).1
        have hdle : d ≤ k := Nat.le_of_dvd (by omega) hdDiv
        have hd1 : 1 < d := by
          have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdDiv (by omega)
          have hdne : d ≠ 1 := Finset.ne_of_mem_erase hd
          omega
        rw [selbergMollifiedDirichletCoeff_eq_vonMangoldt_div_log
          hd1 (hdle.trans hkN) (hdle.trans hkX)]
      _ = (∑ d ∈ k.divisors.erase 1,
            ArithmeticFunction.vonMangoldt d *
              selbergMoebiusCoeff X (k / d)) / Real.log X := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro d _hd
        ring
      _ = selbergShortLowRangeVonMangoldtConvolution X k / Real.log X := by
        unfold selbergShortLowRangeVonMangoldtConvolution
        rw [← Finset.sum_erase_add _ _ hone]
        simp
  unfold selbergShortCollectedDirichletConvolution
  rw [hpair]
  have hsum := Nat.sum_divisorsAntidiagonal
    (f := fun d l =>
      selbergMollifiedDirichletCoeff N X d * selbergMoebiusCoeff X l)
    (n := k)
  rw [hsum, ← Finset.sum_erase_add _ _ hone,
    selbergMollifiedDirichletCoeff_one (by omega) hX1,
    Nat.div_one, one_mul, hrest, add_comm]

/-- The exact low-range arithmetic formula for the collected critical-line
coefficient, retaining the common factor `1 / sqrt k`. -/
theorem selbergShortDirichletCollectedCoeff_eq_lowRange
    {N X k : ℕ} (hk : 1 < k) (hkN : k ≤ N) (hkX : k ≤ X) :
    selbergShortDirichletCollectedCoeff N X k =
      ((selbergMoebiusCoeff X k +
          selbergShortLowRangeVonMangoldtConvolution X k / Real.log X : ℝ) : ℂ) *
        (Real.sqrt (k : ℝ) : ℂ)⁻¹ := by
  rw [selbergShortDirichletCollectedCoeff_eq_convolution,
    selbergShortCollectedDirichletConvolution_eq_lowRange hk hkN hkX]

private theorem abs_selbergShortLowRangeVonMangoldtConvolution_le_log
    {X k : ℕ} (hX : 2 ≤ X) (hk : 1 < k) (hkX : k ≤ X) :
    |selbergShortLowRangeVonMangoldtConvolution X k| ≤ Real.log k := by
  classical
  unfold selbergShortLowRangeVonMangoldtConvolution
  calc
    |∑ d ∈ k.divisors,
        ArithmeticFunction.vonMangoldt d * selbergMoebiusCoeff X (k / d)| ≤
        ∑ d ∈ k.divisors,
          |ArithmeticFunction.vonMangoldt d *
            selbergMoebiusCoeff X (k / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ k.divisors, ArithmeticFunction.vonMangoldt d := by
      apply Finset.sum_le_sum
      intro d hd
      have hdData := Nat.mem_divisors.mp hd
      have hdDiv : d ∣ k := hdData.1
      have hkd1 : 1 ≤ k / d := by
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdDiv (by omega)
        exact Nat.div_pos (Nat.le_of_dvd (by omega) hdDiv) hdpos
      have hkdX : k / d ≤ X :=
        (Nat.div_le_self k d).trans hkX
      have hb := abs_selbergMoebiusCoeff_le_one hX hkd1 hkdX
      have hvm : 0 ≤ ArithmeticFunction.vonMangoldt d :=
        ArithmeticFunction.vonMangoldt_nonneg
      rw [abs_mul, abs_of_nonneg hvm]
      exact (mul_le_mul_of_nonneg_left hb hvm).trans_eq (mul_one _)
    _ = Real.log k := ArithmeticFunction.vonMangoldt_sum

/-- A safe low-range pointwise bound.  It uses no square-energy estimate:
the Moebius term costs at most one and the von Mangoldt divisor convolution
costs at most `log k / log X <= 1`. -/
theorem norm_selbergShortDirichletCollectedCoeff_le_two_div_sqrt
    {N X k : ℕ} (hX : 2 ≤ X) (hk : 1 < k)
    (hkN : k ≤ N) (hkX : k ≤ X) :
    ‖selbergShortDirichletCollectedCoeff N X k‖ ≤
      2 / Real.sqrt (k : ℝ) := by
  have hlogX : 0 < Real.log (X : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogk : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hk.le)
  have hlogle : Real.log (k : ℝ) ≤ Real.log (X : ℝ) := by
    exact Real.log_le_log (by exact_mod_cast (show 0 < k by omega))
      (by exact_mod_cast hkX)
  have hb := abs_selbergMoebiusCoeff_le_one hX hk.le hkX
  have hconv := abs_selbergShortLowRangeVonMangoldtConvolution_le_log
    hX hk hkX
  have hraw :
      |selbergMoebiusCoeff X k +
          selbergShortLowRangeVonMangoldtConvolution X k / Real.log X| ≤ 2 := by
    calc
      |selbergMoebiusCoeff X k +
          selbergShortLowRangeVonMangoldtConvolution X k / Real.log X| ≤
          |selbergMoebiusCoeff X k| +
            |selbergShortLowRangeVonMangoldtConvolution X k / Real.log X| :=
        abs_add_le _ _
      _ = |selbergMoebiusCoeff X k| +
          |selbergShortLowRangeVonMangoldtConvolution X k| / Real.log X := by
        rw [abs_div, abs_of_pos hlogX]
      _ ≤ 1 + Real.log k / Real.log X :=
        add_le_add hb (div_le_div_of_nonneg_right hconv hlogX.le)
      _ ≤ 2 := by
        have : Real.log (k : ℝ) / Real.log (X : ℝ) ≤ 1 :=
          (div_le_one hlogX).2 hlogle
        linarith
  rw [selbergShortDirichletCollectedCoeff_eq_lowRange hk hkN hkX]
  simp only [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), norm_inv]
  change |selbergMoebiusCoeff X k +
      selbergShortLowRangeVonMangoldtConvolution X k / Real.log X| *
      (Real.sqrt (k : ℝ))⁻¹ ≤ 2 / Real.sqrt (k : ℝ)
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hraw (inv_nonneg.mpr (Real.sqrt_nonneg _))

end HardyTheorem
