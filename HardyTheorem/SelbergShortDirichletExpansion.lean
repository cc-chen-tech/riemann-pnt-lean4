import HardyTheorem.SelbergShortAbsLower
import MathlibAux.DirichletPolynomialMeanSquare

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem

/-!
# The all-negative-frequency Selberg short Dirichlet expansion

The short absolute-mass argument uses the first zeta Dirichlet polynomial
multiplied by `M_X ^ 2`.  All three factors have the same critical-line phase,
so a term indexed by `(m,n,l)` has frequency `-log (m*n*l)`.  This differs
from the signed `M_X * conj M_X` expansion, whose third frequency is positive.
-/

/-- The three finite index ranges for the zeta polynomial and the two copies
of the Selberg mollifier. -/
noncomputable def selbergShortDirichletTripleSupport
    (N X : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.Icc 1 N).product
    ((Finset.Icc 1 X).product (Finset.Icc 1 X))

/-- The exact coefficient of the `(m,n,l)` term after restricting all three
Dirichlet factors to the critical line. -/
noncomputable def selbergShortDirichletTripleCoeff
    (X : ℕ) (p : ℕ × (ℕ × ℕ)) : ℂ :=
  (selbergMoebiusCoeff X p.2.1 : ℂ) *
    (selbergMoebiusCoeff X p.2.2 : ℂ) *
    ((Real.sqrt ((p.1 * p.2.1 * p.2.2 : ℕ) : ℝ) : ℝ) : ℂ)⁻¹

/-- Every frequency in the `M_X ^ 2` expansion is the negative logarithm of
the corresponding triple product. -/
noncomputable def selbergShortDirichletTripleFrequency
    (p : ℕ × (ℕ × ℕ)) : ℝ :=
  -Real.log ((p.1 * p.2.1 * p.2.2 : ℕ) : ℝ)

/-- The finite exponential polynomial for
`P_N(1/2+it) * M_X(1/2+it)^2`. -/
noncomputable def selbergShortDirichletTriplePolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial
    (selbergShortDirichletTripleSupport N X)
    (selbergShortDirichletTripleCoeff X)
    selbergShortDirichletTripleFrequency t

/-- The frequency definition exposes the exact product `m*n*l`. -/
theorem selbergShortDirichletTripleFrequency_eq_neg_log_product
    (m n l : ℕ) :
    selbergShortDirichletTripleFrequency (m, n, l) =
      -Real.log ((m * n * l : ℕ) : ℝ) := rfl

/-- Multiplication of the three finite Dirichlet factors gives an exact
uncollected triple sum. -/
theorem criticalLineDirichletPolynomial_mul_mollifier_sq_eq_tripleSum
    (N X : ℕ) (t : ℝ) :
    ((∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 X,
        ∑ l ∈ Finset.Icc 1 X,
          (selbergMoebiusCoeff X n : ℂ) *
            (selbergMoebiusCoeff X l : ℂ) *
            (1 / ((m * n * l : ℕ) : ℂ) ^
              ((1 / 2 : ℂ) + I * t)) := by
  rw [criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_eq_doubleSum]
  unfold selbergMoebiusMollifier selbergMollifier
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [show (((m * n * l : ℕ) : ℂ)) =
      (((m * n : ℕ) : ℂ) * (l : ℂ)) by norm_num,
    Complex.natCast_mul_natCast_cpow (m * n) l,
    show (((m * n : ℕ) : ℂ)) = (m : ℂ) * (n : ℂ) by norm_num,
    Complex.natCast_mul_natCast_cpow m n]
  simp only [one_div, mul_inv_rev]
  ring

private theorem inv_nat_cpow_half_eq_inv_sqrt
    (n : ℕ) :
    ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ = ((Real.sqrt n : ℝ) : ℂ)⁻¹ := by
  congr 1
  calc
    (n : ℂ) ^ (1 / 2 : ℂ) =
        (((n : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
      exact (Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ n) (1 / 2)).symm
    _ = ((Real.sqrt n : ℝ) : ℂ) := by rw [Real.sqrt_eq_rpow]

private theorem shortTripleTerm_eq_exponentialTerm
    {X m n l : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hl : l ≠ 0)
    (t : ℝ) :
    (selbergMoebiusCoeff X n : ℂ) *
          (selbergMoebiusCoeff X l : ℂ) *
          (1 / ((m * n * l : ℕ) : ℂ) ^
            ((1 / 2 : ℂ) + I * t)) =
      selbergShortDirichletTripleCoeff X (m, n, l) *
        Complex.exp
          (I * (selbergShortDirichletTripleFrequency (m, n, l) * t)) := by
  have hprod : m * n * l ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero hm hn) hl
  rw [inv_nat_cpow_criticalLine_eq_exp hprod t,
    inv_nat_cpow_half_eq_inv_sqrt]
  unfold selbergShortDirichletTripleCoeff
  unfold selbergShortDirichletTripleFrequency
  rw [show
      (selbergMoebiusCoeff X n : ℂ) *
          (selbergMoebiusCoeff X l : ℂ) *
          (((Real.sqrt ((m * n * l : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ *
            Complex.exp
              ((-I * (Real.log ((m * n * l : ℕ) : ℝ) : ℂ)) * t)) =
        ((selbergMoebiusCoeff X n : ℂ) *
          (selbergMoebiusCoeff X l : ℂ) *
          ((Real.sqrt ((m * n * l : ℕ) : ℝ) : ℝ) : ℂ)⁻¹) *
        Complex.exp
          ((-I * (Real.log ((m * n * l : ℕ) : ℝ) : ℂ)) * t) by ring]
  congr 2
  push_cast
  ring

/-- The uncollected triple sum is exactly the finite exponential polynomial
with coefficient `b_X(n)b_X(l)/sqrt(m*n*l)` and frequency
`-log(m*n*l)`. -/
theorem criticalLineDirichletPolynomial_mul_mollifier_sq_eq_exponentialPolynomial
    (N X : ℕ) (t : ℝ) :
    ((∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) =
      selbergShortDirichletTriplePolynomial N X t := by
  rw [criticalLineDirichletPolynomial_mul_mollifier_sq_eq_tripleSum]
  unfold selbergShortDirichletTriplePolynomial MathlibAux.exponentialPolynomial
  unfold selbergShortDirichletTripleSupport
  let A := Finset.Icc 1 N
  let B := Finset.Icc 1 X
  let F : ℕ × (ℕ × ℕ) → ℂ := fun p =>
    selbergShortDirichletTripleCoeff X p *
      Complex.exp (I * (selbergShortDirichletTripleFrequency p * t))
  calc
    (∑ m ∈ A, ∑ n ∈ B, ∑ l ∈ B,
          (selbergMoebiusCoeff X n : ℂ) *
          (selbergMoebiusCoeff X l : ℂ) *
          (1 / ((m * n * l : ℕ) : ℂ) ^
            ((1 / 2 : ℂ) + I * t))) =
        ∑ m ∈ A, ∑ n ∈ B, ∑ l ∈ B, F (m, n, l) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro l hl
      have hm0 : m ≠ 0 := by
        apply Nat.ne_of_gt
        exact (Finset.mem_Icc.mp (by simpa [A] using hm)).1
      have hn0 : n ≠ 0 := by
        apply Nat.ne_of_gt
        exact (Finset.mem_Icc.mp (by simpa [B] using hn)).1
      have hl0 : l ≠ 0 := by
        apply Nat.ne_of_gt
        exact (Finset.mem_Icc.mp (by simpa [B] using hl)).1
      exact shortTripleTerm_eq_exponentialTerm hm0 hn0 hl0 t
    _ = ∑ m ∈ A, ∑ q ∈ B.product B, F (m, q) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact (Finset.sum_product B B (fun q => F (m, q))).symm
    _ = ∑ p ∈ A.product (B.product B), F p :=
      (Finset.sum_product A (B.product B) F).symm

/-- Subtracting the distinguished constant term preserves the exact finite
exponential-polynomial expansion of the short-integral integrand. -/
theorem selbergShortDirichletIntegrand_eq_exponentialPolynomial_sub_one
    (N X : ℕ) (t : ℝ) :
    (((∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
      selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) *
      selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) - 1) =
      selbergShortDirichletTriplePolynomial N X t - 1 := by
  rw [criticalLineDirichletPolynomial_mul_mollifier_sq_eq_exponentialPolynomial]

/-- Consequently the existing Selberg short Dirichlet polynomial is exactly
the interval integral of the all-negative-frequency expansion minus one. -/
theorem selbergMollifiedShortDirichletPolynomial_eq_integral_expansion
    (H : ℝ) (N X : ℕ) (t : ℝ) :
    selbergMollifiedShortDirichletPolynomial H N X t =
      ∫ u in t..t + H,
        (selbergShortDirichletTriplePolynomial N X u - 1) := by
  unfold selbergMollifiedShortDirichletPolynomial
  congr 1
  funext u
  exact selbergShortDirichletIntegrand_eq_exponentialPolynomial_sub_one N X u

end HardyTheorem
