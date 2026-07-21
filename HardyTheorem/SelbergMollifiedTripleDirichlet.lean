import HardyTheorem.SelbergMollifiedDirichlet
import MathlibAux.DirichletPolynomialMeanSquare

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# The three-frequency expansion of the mollified zeta polynomial

On the critical line, the sign-preserving Selberg weight is `M(s) * conj M(s)`.
The conjugate has positive logarithmic frequencies, so multiplying the first
zeta Dirichlet polynomial by this weight is a genuine three-index exponential
polynomial, not an ordinary one-variable Dirichlet convolution.
-/

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

private theorem conj_inv_nat_cpow_criticalLine_eq_exp
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (starRingEnd ℂ)
        (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
      ((Real.sqrt n : ℝ) : ℂ)⁻¹ *
        Complex.exp ((I * (Real.log n : ℂ)) * t) := by
  rw [inv_nat_cpow_criticalLine_eq_exp hn t, map_mul,
    inv_nat_cpow_half_eq_inv_sqrt, map_inv₀, Complex.conj_ofReal,
    ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_neg, conj_I, Complex.conj_ofReal]
  ring

/-- Conjugating the real-coefficient Selberg mollifier changes every
critical-line Dirichlet monomial from height `t` to height `-t`. -/
theorem conj_selbergMoebiusMollifier_criticalLine_eq_sum
    (X : ℕ) (t : ℝ) :
    (starRingEnd ℂ)
        (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) =
      ∑ l ∈ Finset.Icc 1 X,
        (selbergMoebiusCoeff X l : ℂ) *
          (1 / (l : ℂ) ^ ((1 / 2 : ℂ) - I * t)) := by
  unfold selbergMoebiusMollifier selbergMollifier
  simp only [map_sum, map_mul, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  have hl0 : l ≠ 0 := by
    have := (Finset.mem_Icc.mp hl).1
    omega
  have hneg := inv_nat_cpow_criticalLine_eq_exp hl0 (-t)
  rw [conj_inv_nat_cpow_criticalLine_eq_exp hl0 t]
  have hneg' :
      1 / (l : ℂ) ^ ((1 / 2 : ℂ) - I * t) =
        ((l : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
          Complex.exp ((-I * (Real.log l : ℂ)) * (-t)) := by
    convert hneg using 1
    all_goals norm_num
    all_goals congr 1
  rw [hneg', inv_nat_cpow_half_eq_inv_sqrt]
  congr 1
  congr 1
  ring

/-- Equivalently, conjugation reflects the concrete mollifier across the real
axis on the critical line. -/
theorem conj_selbergMoebiusMollifier_criticalLine_eq_neg
    (X : ℕ) (t : ℝ) :
    (starRingEnd ℂ)
        (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) =
      selbergMoebiusMollifier X ((1 / 2 : ℂ) - I * t) := by
  rw [conj_selbergMoebiusMollifier_criticalLine_eq_sum]
  rfl

/-- The three finite index ranges `(m,n,l)` for the first zeta polynomial,
the mollifier, and its conjugate. -/
noncomputable def selbergMollifiedTripleSupport
    (N X : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.Icc 1 N).product
    ((Finset.Icc 1 X).product (Finset.Icc 1 X))

/-- The real square-root coefficient of a three-index mollified term. -/
noncomputable def selbergMollifiedTripleCoeff
    (X : ℕ) (p : ℕ × (ℕ × ℕ)) : ℂ :=
  (selbergMoebiusCoeff X p.2.1 : ℂ) *
    (selbergMoebiusCoeff X p.2.2 : ℂ) *
    ((Real.sqrt p.1 : ℝ) : ℂ)⁻¹ *
    ((Real.sqrt p.2.1 : ℝ) : ℂ)⁻¹ *
    ((Real.sqrt p.2.2 : ℝ) : ℂ)⁻¹

/-- The conjugate mollifier contributes the positive frequency `log l`; the
other two Dirichlet factors contribute `-log m-log n`. -/
noncomputable def selbergMollifiedTripleFrequency
    (p : ℕ × (ℕ × ℕ)) : ℝ :=
  Real.log p.2.2 - Real.log p.1 - Real.log p.2.1

/-- The correctly signed finite exponential polynomial for
`P_N(1/2+it) M_X(1/2+it) conj(M_X(1/2+it))`. -/
noncomputable def selbergMollifiedTriplePolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial (selbergMollifiedTripleSupport N X)
    (selbergMollifiedTripleCoeff X)
    selbergMollifiedTripleFrequency t

/-- Expanding the three finite factors gives the exact uncollected triple
sum.  No one-variable convolution is used for the conjugate factor. -/
theorem criticalLineDirichletPolynomial_mul_mollifier_mul_conj_eq_tripleSum
    (N X : ℕ) (t : ℝ) :
    ((∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) *
        (starRingEnd ℂ)
          (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 X,
        ∑ l ∈ Finset.Icc 1 X,
          (selbergMoebiusCoeff X n : ℂ) *
            (selbergMoebiusCoeff X l : ℂ) *
            (1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
            (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          (1 / (l : ℂ) ^ ((1 / 2 : ℂ) - I * t)) := by
  rw [criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_eq_doubleSum,
    conj_selbergMoebiusMollifier_criticalLine_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Complex.natCast_mul_natCast_cpow]
  simp only [one_div, mul_inv_rev]
  ring

private theorem tripleTerm_eq_exponentialTerm
    {X m n l : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hl : l ≠ 0)
    (t : ℝ) :
    (selbergMoebiusCoeff X n : ℂ) *
          (selbergMoebiusCoeff X l : ℂ) *
          (1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          (1 / (l : ℂ) ^ ((1 / 2 : ℂ) - I * t)) =
      selbergMollifiedTripleCoeff X (m, n, l) *
        Complex.exp
          (I * (selbergMollifiedTripleFrequency (m, n, l) * t)) := by
  have hlneg := inv_nat_cpow_criticalLine_eq_exp hl (-t)
  have hlneg' :
      1 / (l : ℂ) ^ ((1 / 2 : ℂ) - I * t) =
        ((l : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
          Complex.exp ((-I * (Real.log l : ℂ)) * (-t)) := by
    convert hlneg using 1
    all_goals norm_num
    all_goals congr 1
  rw [inv_nat_cpow_criticalLine_eq_exp hm t,
    inv_nat_cpow_criticalLine_eq_exp hn t,
    hlneg',
    inv_nat_cpow_half_eq_inv_sqrt,
    inv_nat_cpow_half_eq_inv_sqrt,
    inv_nat_cpow_half_eq_inv_sqrt]
  unfold selbergMollifiedTripleCoeff selbergMollifiedTripleFrequency
  rw [show
      (selbergMoebiusCoeff X n : ℂ) *
            (selbergMoebiusCoeff X l : ℂ) *
            (((Real.sqrt m : ℝ) : ℂ)⁻¹ *
              Complex.exp ((-I * (Real.log m : ℂ)) * t)) *
            (((Real.sqrt n : ℝ) : ℂ)⁻¹ *
              Complex.exp ((-I * (Real.log n : ℂ)) * t)) *
            (((Real.sqrt l : ℝ) : ℂ)⁻¹ *
              Complex.exp ((-I * (Real.log l : ℂ)) * (-t))) =
          ((selbergMoebiusCoeff X n : ℂ) *
            (selbergMoebiusCoeff X l : ℂ) *
            ((Real.sqrt m : ℝ) : ℂ)⁻¹ *
            ((Real.sqrt n : ℝ) : ℂ)⁻¹ *
            ((Real.sqrt l : ℝ) : ℂ)⁻¹) *
          (Complex.exp ((-I * (Real.log m : ℂ)) * t) *
            Complex.exp ((-I * (Real.log n : ℂ)) * t) *
            Complex.exp ((-I * (Real.log l : ℂ)) * (-t))) by ring]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The exact triple sum is the finite exponential polynomial with coefficient
`b_X(n)b_X(l)/(sqrt m sqrt n sqrt l)` and frequency
`log l-log m-log n`, equivalently `log l-log(mn)` on this positive support. -/
theorem criticalLineDirichletPolynomial_mul_mollifier_mul_conj_eq_exponentialPolynomial
    (N X : ℕ) (t : ℝ) :
    ((∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) *
        (starRingEnd ℂ)
          (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) =
      selbergMollifiedTriplePolynomial N X t := by
  rw [criticalLineDirichletPolynomial_mul_mollifier_mul_conj_eq_tripleSum]
  unfold selbergMollifiedTriplePolynomial MathlibAux.exponentialPolynomial
  unfold selbergMollifiedTripleSupport
  let A := Finset.Icc 1 N
  let B := Finset.Icc 1 X
  let F : ℕ × (ℕ × ℕ) → ℂ := fun p =>
    selbergMollifiedTripleCoeff X p *
      Complex.exp (I * (selbergMollifiedTripleFrequency p * t))
  calc
    (∑ m ∈ A, ∑ n ∈ B, ∑ l ∈ B,
        (selbergMoebiusCoeff X n : ℂ) *
          (selbergMoebiusCoeff X l : ℂ) *
          (1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          (1 / (l : ℂ) ^ ((1 / 2 : ℂ) - I * t))) =
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
      exact tripleTerm_eq_exponentialTerm hm0 hn0 hl0 t
    _ = ∑ m ∈ A, ∑ q ∈ B.product B, F (m, q) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact (Finset.sum_product B B (fun q => F (m, q))).symm
    _ = ∑ p ∈ A.product (B.product B), F p :=
      (Finset.sum_product A (B.product B) F).symm

end HardyTheorem
