import HardyTheorem.SelbergMollifiedDirichlet
import MathlibAux.GaussianExponentialPolynomialMeanSquare

/-!
# The dual AFE sum times the linear Selberg mollifier

The dual square-root AFE sum has positive logarithmic frequency.  After
multiplication by the ordinary mollifier, a pair `(n,d)` has frequency
`log n - log d`, hence equal frequencies lie on rational rays `n/d`.
This file records the exact uncollected exponential polynomial and an
absolute coefficient majorant.  It does not assume or prove an AFE.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

private theorem inv_nat_cpow_half_eq_inv_sqrt_dual (n : ℕ) :
    ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ = ((Real.sqrt n : ℝ) : ℂ)⁻¹ := by
  congr 1
  calc
    (n : ℂ) ^ (1 / 2 : ℂ) =
        (((n : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
      exact (Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ n) (1 / 2)).symm
    _ = ((Real.sqrt n : ℝ) : ℂ) := by rw [Real.sqrt_eq_rpow]

/-- The raw pair support for the dual zeta sum of length `N` and mollifier
of length `X`. -/
noncomputable def selbergMollifiedDualSupport
    (N X : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 N).product (Finset.Icc 1 X)

/-- The signed coefficient `b_X(d)/(sqrt n sqrt d)` attached to `(n,d)`. -/
noncomputable def selbergMollifiedDualCoeff
    (X : ℕ) (p : ℕ × ℕ) : ℂ :=
  (selbergMoebiusCoeff X p.2 : ℂ) *
    ((Real.sqrt p.1 : ℝ) : ℂ)⁻¹ *
    ((Real.sqrt p.2 : ℝ) : ℂ)⁻¹

/-- The nonnegative absolute majorant of the signed dual coefficient. -/
noncomputable def selbergMollifiedDualMass
    (X : ℕ) (p : ℕ × ℕ) : ℝ :=
  |selbergMoebiusCoeff X p.2| *
    (Real.sqrt p.1)⁻¹ * (Real.sqrt p.2)⁻¹

/-- The dual/mollifier logarithmic frequency of `(n,d)`. -/
noncomputable def selbergMollifiedDualFrequency
    (p : ℕ × ℕ) : ℝ :=
  Real.log p.1 - Real.log p.2

/-- The finite dual AFE polynomial multiplied by the linear mollifier. -/
noncomputable def selbergMollifiedDualPolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial (selbergMollifiedDualSupport N X)
    (selbergMollifiedDualCoeff X) selbergMollifiedDualFrequency t

/-- The signed coefficient is bounded exactly by its nonnegative majorant. -/
theorem norm_selbergMollifiedDualCoeff_le_mass
    {X : ℕ} {p : ℕ × ℕ} :
    ‖selbergMollifiedDualCoeff X p‖ ≤ selbergMollifiedDualMass X p := by
  rw [selbergMollifiedDualCoeff, selbergMollifiedDualMass,
    norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_inv]
  rw [abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Real.sqrt_nonneg _)]

private theorem dualTerm_eq_exponentialTerm
    {X n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0) (t : ℝ) :
    (1 / (n : ℂ) ^ ((1 / 2 : ℂ) - I * t)) *
        ((selbergMoebiusCoeff X d : ℂ) *
          (1 / (d : ℂ) ^ ((1 / 2 : ℂ) + I * t))) =
      selbergMollifiedDualCoeff X (n, d) *
        Complex.exp
          (I * (selbergMollifiedDualFrequency (n, d) * t)) := by
  have hnneg := inv_nat_cpow_criticalLine_eq_exp hn (-t)
  have hnneg' :
      1 / (n : ℂ) ^ ((1 / 2 : ℂ) - I * t) =
        ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
          Complex.exp ((-I * (Real.log n : ℂ)) * (-t)) := by
    convert hnneg using 1
    all_goals norm_num
    all_goals congr 1
  rw [hnneg', inv_nat_cpow_criticalLine_eq_exp hd t,
    inv_nat_cpow_half_eq_inv_sqrt_dual,
    inv_nat_cpow_half_eq_inv_sqrt_dual]
  unfold selbergMollifiedDualCoeff selbergMollifiedDualFrequency
  rw [show
      (((Real.sqrt n : ℝ) : ℂ)⁻¹ *
            Complex.exp ((-I * (Real.log n : ℂ)) * (-t))) *
          ((selbergMoebiusCoeff X d : ℂ) *
            (((Real.sqrt d : ℝ) : ℂ)⁻¹ *
              Complex.exp ((-I * (Real.log d : ℂ)) * t))) =
        ((selbergMoebiusCoeff X d : ℂ) *
            ((Real.sqrt n : ℝ) : ℂ)⁻¹ *
            ((Real.sqrt d : ℝ) : ℂ)⁻¹) *
          (Complex.exp ((-I * (Real.log n : ℂ)) * (-t)) *
            Complex.exp ((-I * (Real.log d : ℂ)) * t)) by ring]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Exact finite exponential-polynomial identity for the dual square-root
zeta sum times the ordinary Selberg mollifier. -/
theorem
    dualCriticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_eq_exponentialPolynomial
    (N X : ℕ) (t : ℝ) :
    (∑ n ∈ Finset.Icc 1 N,
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) - I * t)) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) =
      selbergMollifiedDualPolynomial N X t := by
  unfold selbergMoebiusMollifier selbergMollifier
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  unfold selbergMollifiedDualPolynomial MathlibAux.exponentialPolynomial
    selbergMollifiedDualSupport
  let A := Finset.Icc 1 N
  let B := Finset.Icc 1 X
  let F : ℕ × ℕ → ℂ := fun p =>
    selbergMollifiedDualCoeff X p *
      Complex.exp (I * (selbergMollifiedDualFrequency p * t))
  calc
    (∑ n ∈ A, (∑ d ∈ B,
        (1 / (n : ℂ) ^ ((1 / 2 : ℂ) - I * t)) *
          ((selbergMoebiusCoeff X d : ℂ) *
            (1 / (d : ℂ) ^ ((1 / 2 : ℂ) + I * t))))) =
        ∑ n ∈ A, ∑ d ∈ B, F (n, d) := by
      apply Finset.sum_congr rfl
      intro n hnMem
      apply Finset.sum_congr rfl
      intro d hdMem
      apply dualTerm_eq_exponentialTerm
      · exact Nat.ne_of_gt (Finset.mem_Icc.mp (by simpa [A] using hnMem)).1
      · exact Nat.ne_of_gt (Finset.mem_Icc.mp (by simpa [B] using hdMem)).1
    _ = ∑ p ∈ A.product B, F p :=
      (Finset.sum_product A B F).symm

end HardyTheorem
