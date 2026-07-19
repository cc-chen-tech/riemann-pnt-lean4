import PrimeNumberTheorem.DirichletPolynomialMeanSquare
import PrimeNumberTheorem.CarneiroLittmannKernelConstruction
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Complex
open scoped BigOperators ComplexConjugate Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The finite Möbius mollifier used in Carlson's zero-density argument. -/
noncomputable def mobiusMollifier (X : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,
    (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s

/-- Coefficients of the Möbius mollifier restricted to a vertical line. -/
noncomputable def mobiusMollifierCoefficient (sigma : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius n : ℂ) * ((n : ℂ) ^ (sigma : ℂ))⁻¹

/-- Möbius coefficients have modulus at most one, so the mollifier coefficient
on `Re s = sigma` is bounded by the expected real power. -/
theorem norm_mobiusMollifierCoefficient_le
    {n : ℕ} (hn : 0 < n) (sigma : ℝ) :
    ‖mobiusMollifierCoefficient sigma n‖ ≤ (n : ℝ) ^ (-sigma) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmuInt := ArithmeticFunction.abs_moebius_le_one (n := n)
  have hmuReal : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast hmuInt
  have hmuComplex : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_intCast] using hmuReal
  have hnCast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
  unfold mobiusMollifierCoefficient
  rw [norm_mul, norm_inv, hnCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
  simp only [Complex.ofReal_re]
  rw [Real.rpow_neg hnpos.le]
  have hinvnonneg : 0 ≤ ((n : ℝ) ^ sigma)⁻¹ :=
    inv_nonneg.mpr (Real.rpow_nonneg hnpos.le sigma)
  simpa using mul_le_mul_of_nonneg_right hmuComplex hinvnonneg

/-- For `1/2 < sigma < 1`, the weighted real power sum in the mollifier
mean-square estimate has the sharp endpoint exponent `2 - 2 * sigma`. -/
theorem weightedPowerSum_le_rpow_endpoint
    {X : ℕ} (hX : 1 ≤ X) {sigma : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1) :
    (∑ n ∈ Finset.Icc 1 X,
        ((n : ℝ) + 1) * ((n : ℝ) ^ (-sigma)) ^ 2) ≤
      2 * (1 +
        ((X : ℝ) ^ (2 - 2 * sigma) - 1) / (2 - 2 * sigma)) := by
  let p : ℝ := 1 - 2 * sigma
  have hp_nonpos : p ≤ 0 := by dsimp [p]; linarith
  have hp_gt_neg_one : -1 < p := by dsimp [p]; linarith
  have hanti :
      AntitoneOn (fun x : ℝ => x ^ p) (Set.Icc ((1 : ℕ) : ℝ) X) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hp_nonpos).mono
    intro x hx
    exact Set.mem_Ioi.mpr ((by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)).trans_le hx.1)
  have htail := AntitoneOn.sum_le_integral_Ico
    (f := fun x : ℝ => x ^ p) hX hanti
  have hshift :
      (∑ n ∈ Finset.Ioc 1 X, (n : ℝ) ^ p) =
        ∑ n ∈ Finset.Ico 1 X, ((n + 1 : ℕ) : ℝ) ^ p := by
    simpa only [Finset.Ico_add_one_add_one_eq_Ioc] using
      (Finset.sum_Ico_add' (fun n : ℕ => (n : ℝ) ^ p) 1 X 1).symm
  have hset : Finset.Icc 1 X = insert 1 (Finset.Ioc 1 X) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hintegral :
      (∫ x : ℝ in (1 : ℝ)..X, x ^ p) =
        ((X : ℝ) ^ (2 - 2 * sigma) - 1) / (2 - 2 * sigma) := by
    rw [integral_rpow (Or.inl hp_gt_neg_one)]
    have hpadd : p + 1 = 2 - 2 * sigma := by dsimp [p]; ring
    rw [hpadd]
    simp only [Real.one_rpow]
  have htailEndpoint :
      (∑ n ∈ Finset.Ico 1 X, ((n + 1 : ℕ) : ℝ) ^ p) ≤
        ((X : ℝ) ^ (2 - 2 * sigma) - 1) / (2 - 2 * sigma) := by
    calc
      (∑ n ∈ Finset.Ico 1 X, ((n + 1 : ℕ) : ℝ) ^ p) ≤
          ∫ x : ℝ in (1 : ℝ)..X, x ^ p := by
        simpa only [Nat.cast_one] using htail
      _ = ((X : ℝ) ^ (2 - 2 * sigma) - 1) / (2 - 2 * sigma) := hintegral
  have hpowerSum :
      (∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ p) ≤
        1 + ((X : ℝ) ^ (2 - 2 * sigma) - 1) / (2 - 2 * sigma) := by
    rw [hset, Finset.sum_insert (by simp)]
    simp only [Nat.cast_one, Real.one_rpow]
    rw [hshift]
    linarith
  have hterm {n : ℕ} (hn : n ∈ Finset.Icc 1 X) :
      ((n : ℝ) + 1) * ((n : ℝ) ^ (-sigma)) ^ 2 ≤
        2 * (n : ℝ) ^ p := by
    have hnNat : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hnNat)
    have hnlinear : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
      exact_mod_cast (show n + 1 ≤ 2 * n by omega)
    have hsquare :
        ((n : ℝ) ^ (-sigma)) ^ 2 = (n : ℝ) ^ (-2 * sigma) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hnpos)]
      congr 1
      ring
    calc
      ((n : ℝ) + 1) * ((n : ℝ) ^ (-sigma)) ^ 2 ≤
          (2 * (n : ℝ)) * ((n : ℝ) ^ (-sigma)) ^ 2 :=
        mul_le_mul_of_nonneg_right hnlinear (sq_nonneg _)
      _ = 2 * (n : ℝ) ^ p := by
        rw [hsquare]
        calc
          (2 * (n : ℝ)) * (n : ℝ) ^ (-2 * sigma) =
              2 * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-2 * sigma)) := by
            rw [Real.rpow_one]
            ring
          _ = 2 * (n : ℝ) ^ ((1 : ℝ) + (-2 * sigma)) := by
            rw [Real.rpow_add hnpos]
          _ = 2 * (n : ℝ) ^ p := by dsimp [p]; ring_nf
  calc
    (∑ n ∈ Finset.Icc 1 X,
        ((n : ℝ) + 1) * ((n : ℝ) ^ (-sigma)) ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 X, 2 * (n : ℝ) ^ p := by
        apply Finset.sum_le_sum
        intro n hn
        exact hterm hn
    _ = 2 * (∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ p) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (1 +
        ((X : ℝ) ^ (2 - 2 * sigma) - 1) / (2 - 2 * sigma)) := by
      gcongr

/-- Split a positive natural complex power on a vertical line into its real
decay coefficient and logarithmic oscillation. -/
theorem inv_nat_cpow_verticalLine_eq_exp
    {n : ℕ} (hn : n ≠ 0) (sigma t : ℝ) :
    1 / (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t) =
      ((n : ℂ) ^ (sigma : ℂ))⁻¹ *
        Complex.exp ((-Complex.I * (Real.log n : ℂ)) * t) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Complex.cpow_add _ _ hnC, one_div, mul_inv_rev]
  calc
    ((n : ℂ) ^ (Complex.I * t))⁻¹ *
        ((n : ℂ) ^ (sigma : ℂ))⁻¹ =
        ((n : ℂ) ^ (sigma : ℂ))⁻¹ *
          ((n : ℂ) ^ (Complex.I * t))⁻¹ := mul_comm _ _
    _ = ((n : ℂ) ^ (sigma : ℂ))⁻¹ *
        Complex.exp ((-Complex.I * (Real.log n : ℂ)) * t) := by
      congr 1
      rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_neg,
        ← Complex.natCast_log]
      congr 1
      ring

/-- On a vertical line, the Möbius mollifier is a finite Dirichlet
polynomial with frequencies `-log n`. -/
theorem mobiusMollifier_verticalLine_eq_finiteDirichletPolynomial
    (X : ℕ) (sigma t : ℝ) :
    mobiusMollifier X ((sigma : ℂ) + Complex.I * t) =
      DirichletPolynomial.finiteDirichletPolynomial (Finset.Icc 1 X)
        (mobiusMollifierCoefficient sigma) t := by
  unfold mobiusMollifier DirichletPolynomial.finiteDirichletPolynomial
    DirichletPolynomial.finiteExponentialSum
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := Nat.ne_of_gt hnpos
  have hinv := inv_nat_cpow_verticalLine_eq_exp hn0 sigma t
  rw [one_div] at hinv
  rw [div_eq_mul_inv, hinv]
  unfold mobiusMollifierCoefficient
  ring_nf
  congr 1
  push_cast
  ring_nf

/-- A finite Möbius mollifier is continuous along every vertical line. -/
theorem continuous_mobiusMollifier_verticalLine
    (X : ℕ) (sigma : ℝ) :
    Continuous (fun t : ℝ =>
      mobiusMollifier X ((sigma : ℂ) + Complex.I * t)) := by
  have hpoly : Continuous (fun t : ℝ =>
      DirichletPolynomial.finiteDirichletPolynomial (Finset.Icc 1 X)
        (mobiusMollifierCoefficient sigma) t) := by
    unfold DirichletPolynomial.finiteDirichletPolynomial
      DirichletPolynomial.finiteExponentialSum
    fun_prop
  exact hpoly.congr fun t =>
    (mobiusMollifier_verticalLine_eq_finiteDirichletPolynomial X sigma t).symm

/-- The finite-frequency mean-square estimate inherited by the Möbius
mollifier on every vertical line. -/
theorem mobiusMollifier_meanSquare_le
    {X : ℕ} {sigma : ℝ} {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
        ‖mobiusMollifierCoefficient sigma m‖ *
          ‖mobiusMollifierCoefficient sigma n‖ *
            if m = n then b - a
            else 2 / |Real.log n - Real.log m| := by
  simp_rw [mobiusMollifier_verticalLine_eq_finiteDirichletPolynomial]
  apply DirichletPolynomial.finiteDirichletPolynomial_meanSquare_le hab
  intro n hn
  exact (Finset.mem_Icc.mp hn).1

/-- The concrete Carneiro--Littmann Hilbert kernel gives a single weighted
diagonal bound for the Möbius mollifier mean square. -/
theorem mobiusMollifier_meanSquare_le_carneiroLittmann
    (X : ℕ) (sigma : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc 1 X,
          ((n : ℝ) + 1) * ‖mobiusMollifierCoefficient sigma n‖ ^ 2 := by
  let D : ℝ := ∑ n ∈ Finset.Icc 1 X,
    ((n : ℝ) + 1) * ‖mobiusMollifierCoefficient sigma n‖ ^ 2
  have hraw :
      ∫ t in a..b,
          ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
        (b - a) * ∑ n ∈ Finset.Icc 1 X,
            ‖mobiusMollifierCoefficient sigma n‖ ^ 2 +
          4 * Real.pi * D := by
    simp_rw [mobiusMollifier_verticalLine_eq_finiteDirichletPolynomial]
    unfold DirichletPolynomial.finiteDirichletPolynomial
    simpa only [D, mul_assoc, show 2 * (2 * Real.pi) = 4 * Real.pi by ring] using
      (DirichletPolynomial.finiteExponentialSum_meanSquare_le_of_hilbert
        (S := Finset.Icc 1 X)
        (c := mobiusMollifierCoefficient sigma)
        (omega := fun n : ℕ => -Real.log n)
        (weight := fun n : ℕ => (n : ℝ) + 1)
        (C := 2 * Real.pi) hab
        (by
          intro m hm n hn hmn
          have hmpos : 0 < (m : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp hm).1
          have hnpos : 0 < (n : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp hn).1
          have hlog : Real.log (m : ℝ) = Real.log (n : ℝ) := by linarith
          exact Nat.cast_injective (Real.log_injOn_pos hmpos hnpos hlog))
        (by intro n hn; positivity)
        (fun d =>
          DirichletPolynomial.norm_hilbertForm_Icc_neg_log_le_carneiroLittmann
            (show 0 < (1 : ℕ) by omega) d))
  calc
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.Icc 1 X,
          ‖mobiusMollifierCoefficient sigma n‖ ^ 2 +
        4 * Real.pi * D := hraw
    _ ≤ (b - a) * D + 4 * Real.pi * D := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
        apply Finset.sum_le_sum
        intro n hn
        have hnorm : 0 ≤ ‖mobiusMollifierCoefficient sigma n‖ ^ 2 := sq_nonneg _
        have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      · exact le_rfl
    _ = ((b - a) + 4 * Real.pi) * D := by ring

/-- Replacing the Möbius coefficient by its pointwise power majorant leaves a
purely real weighted power sum for the mollifier mean square. -/
theorem mobiusMollifier_meanSquare_le_weightedPowerSum
    (X : ℕ) (sigma : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc 1 X,
          ((n : ℝ) + 1) * ((n : ℝ) ^ (-sigma)) ^ 2 := by
  calc
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc 1 X,
          ((n : ℝ) + 1) * ‖mobiusMollifierCoefficient sigma n‖ ^ 2 :=
      mobiusMollifier_meanSquare_le_carneiroLittmann X sigma hab
    _ ≤ ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc 1 X,
          ((n : ℝ) + 1) * ((n : ℝ) ^ (-sigma)) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro n hn
        have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
        have hcoeff := norm_mobiusMollifierCoefficient_le hnpos sigma
        have hcoeff_nonneg : 0 ≤ ‖mobiusMollifierCoefficient sigma n‖ := norm_nonneg _
        have hpower_nonneg : 0 ≤ (n : ℝ) ^ (-sigma) := Real.rpow_nonneg (by positivity) _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      · exact add_nonneg (sub_nonneg.mpr hab)
          (mul_nonneg (by norm_num) Real.pi_nonneg)

/-- The Möbius mollifier mean square in the Carlson strip, with the coefficient
sum eliminated in favor of its sharp `X ^ (2 - 2 * sigma)` endpoint bound. -/
theorem mobiusMollifier_meanSquare_le_rpow_endpoint
    {X : ℕ} (hX : 1 ≤ X) {sigma a b : ℝ}
    (hab : a ≤ b) (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1) :
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        (2 * (1 +
          ((X : ℝ) ^ (2 - 2 * sigma) - 1) / (2 - 2 * sigma))) := by
  calc
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc 1 X,
          ((n : ℝ) + 1) * ((n : ℝ) ^ (-sigma)) ^ 2 :=
      mobiusMollifier_meanSquare_le_weightedPowerSum X sigma hab
    _ ≤ ((b - a) + 4 * Real.pi) *
        (2 * (1 +
          ((X : ℝ) ^ (2 - 2 * sigma) - 1) / (2 - 2 * sigma))) := by
      apply mul_le_mul_of_nonneg_left
      · exact weightedPowerSum_le_rpow_endpoint hX hsigma hsigma1
      · exact add_nonneg (sub_nonneg.mpr hab)
          (mul_nonneg (by norm_num) Real.pi_nonneg)

end CarlsonZeroDensity
end PrimeNumberTheorem
