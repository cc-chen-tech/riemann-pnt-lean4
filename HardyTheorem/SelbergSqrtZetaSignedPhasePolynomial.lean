import HardyTheorem.SelbergSqrtZetaShortExpansion
import HardyTheorem.VerticalGammaAsymptotic

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Signed Hardy-phase polynomial for the square-root-zeta mollifier

This module expands the finite critical-line product

`P_N(1/2+it) M_X(1/2+it) conj(M_X(1/2+it))`

with the tapered square-root-zeta coefficients.  The conjugate mollifier has
positive logarithmic frequency, so the exact expansion is indexed by triples
`(m,d,l)` with frequency `log l - log m - log d`.  Multiplication by
`exp (I * thetaModel t)` then attaches the model Hardy phase termwise.
-/

/-- The finite `(m,d,l)` support for the zeta truncation, the square-root-zeta
mollifier, and its complex conjugate. -/
noncomputable def selbergSqrtZetaSignedPhaseSupport
    (N X : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.Icc 1 N).product
    ((Finset.Icc 1 X).product (Finset.Icc 1 X))

/-- The coefficient of a signed square-root-zeta triple.  Both mollifier
coefficients are real, while every critical-line factor contributes its
inverse square-root weight. -/
noncomputable def selbergSqrtZetaSignedPhaseCoeff
    (X : ℕ) (p : ℕ × (ℕ × ℕ)) : ℂ :=
  (selbergSqrtZetaTaperedCoeff X p.2.1 : ℂ) *
    (selbergSqrtZetaTaperedCoeff X p.2.2 : ℂ) *
    ((Real.sqrt p.1 : ℝ) : ℂ)⁻¹ *
    ((Real.sqrt p.2.1 : ℝ) : ℂ)⁻¹ *
    ((Real.sqrt p.2.2 : ℝ) : ℂ)⁻¹

/-- The conjugate mollifier contributes `+log l`; the zeta truncation and
the ordinary mollifier contribute `-log m-log d`. -/
noncomputable def selbergSqrtZetaSignedPhaseFrequency
    (p : ℕ × (ℕ × ℕ)) : ℝ :=
  Real.log p.2.2 - Real.log p.1 - Real.log p.2.1

/-- The exact finite exponential polynomial before attaching `thetaModel`. -/
noncomputable def selbergSqrtZetaSignedTriplePolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial
    (selbergSqrtZetaSignedPhaseSupport N X)
    (selbergSqrtZetaSignedPhaseCoeff X)
    selbergSqrtZetaSignedPhaseFrequency t

/-- The same finite polynomial with the model Hardy phase attached to every
term. -/
noncomputable def selbergSqrtZetaSignedPhasePolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ selbergSqrtZetaSignedPhaseSupport N X,
    selbergSqrtZetaSignedPhaseCoeff X p *
      Complex.exp
        (I * ((thetaModel t +
          selbergSqrtZetaSignedPhaseFrequency p * t : ℝ) : ℂ))

private theorem inv_nat_cpow_half_eq_inv_sqrt_signed
    (n : ℕ) :
    ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ =
      ((Real.sqrt n : ℝ) : ℂ)⁻¹ := by
  congr 1
  calc
    (n : ℂ) ^ (1 / 2 : ℂ) =
        (((n : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
      exact (Complex.ofReal_cpow
        (by positivity : (0 : ℝ) ≤ n) (1 / 2)).symm
    _ = ((Real.sqrt n : ℝ) : ℂ) := by
      rw [Real.sqrt_eq_rpow]

private theorem conj_inv_nat_cpow_criticalLine_eq_exp_signed
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (starRingEnd ℂ)
        (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
      ((Real.sqrt n : ℝ) : ℂ)⁻¹ *
        Complex.exp ((I * (Real.log n : ℂ)) * t) := by
  rw [inv_nat_cpow_criticalLine_eq_exp hn t, map_mul,
    inv_nat_cpow_half_eq_inv_sqrt_signed, map_inv₀,
    Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_neg, conj_I, Complex.conj_ofReal]
  ring

/-- Conjugating the real-coefficient square-root-zeta mollifier reverses the
height of every critical-line Dirichlet monomial. -/
theorem conj_selbergSqrtZetaMollifier_criticalLine_eq_sum
    (X : ℕ) (t : ℝ) :
    (starRingEnd ℂ)
        (selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) =
      ∑ l ∈ Finset.Icc 1 X,
        (selbergSqrtZetaTaperedCoeff X l : ℂ) *
          (1 / (l : ℂ) ^ ((1 / 2 : ℂ) - I * t)) := by
  unfold selbergSqrtZetaMollifier selbergMollifier
  simp only [map_sum, map_mul, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  have hl0 : l ≠ 0 := by
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hl).1
  have hneg := inv_nat_cpow_criticalLine_eq_exp hl0 (-t)
  rw [conj_inv_nat_cpow_criticalLine_eq_exp_signed hl0 t]
  have hneg' :
      1 / (l : ℂ) ^ ((1 / 2 : ℂ) - I * t) =
        ((l : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
          Complex.exp ((-I * (Real.log l : ℂ)) * (-t)) := by
    convert hneg using 1
    all_goals norm_num
    all_goals congr 1
  rw [hneg', inv_nat_cpow_half_eq_inv_sqrt_signed]
  congr 1
  congr 1
  ring

/-- Expanding the three finite factors gives the exact signed triple sum with
the tapered square-root-zeta coefficients. -/
theorem
    criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_mul_conj_eq_signedTripleSum
    (N X : ℕ) (t : ℝ) :
    ((∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) *
        (starRingEnd ℂ)
          (selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) =
      ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 X,
        ∑ l ∈ Finset.Icc 1 X,
          (selbergSqrtZetaTaperedCoeff X d : ℂ) *
            (selbergSqrtZetaTaperedCoeff X l : ℂ) *
            (1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
            (1 / (d : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
            (1 / (l : ℂ) ^ ((1 / 2 : ℂ) - I * t)) := by
  rw [conj_selbergSqrtZetaMollifier_criticalLine_eq_sum]
  unfold selbergSqrtZetaMollifier selbergMollifier
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

private theorem signedTripleTerm_eq_exponentialTerm
    {X m d l : ℕ} (hm : m ≠ 0) (hd : d ≠ 0) (hl : l ≠ 0)
    (t : ℝ) :
    (selbergSqrtZetaTaperedCoeff X d : ℂ) *
          (selbergSqrtZetaTaperedCoeff X l : ℂ) *
          (1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          (1 / (d : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          (1 / (l : ℂ) ^ ((1 / 2 : ℂ) - I * t)) =
      selbergSqrtZetaSignedPhaseCoeff X (m, d, l) *
        Complex.exp
          (I * (selbergSqrtZetaSignedPhaseFrequency
            (m, d, l) * t)) := by
  have hlneg := inv_nat_cpow_criticalLine_eq_exp hl (-t)
  have hlneg' :
      1 / (l : ℂ) ^ ((1 / 2 : ℂ) - I * t) =
        ((l : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
          Complex.exp ((-I * (Real.log l : ℂ)) * (-t)) := by
    convert hlneg using 1
    all_goals norm_num
    all_goals congr 1
  rw [inv_nat_cpow_criticalLine_eq_exp hm t,
    inv_nat_cpow_criticalLine_eq_exp hd t, hlneg',
    inv_nat_cpow_half_eq_inv_sqrt_signed,
    inv_nat_cpow_half_eq_inv_sqrt_signed,
    inv_nat_cpow_half_eq_inv_sqrt_signed]
  unfold selbergSqrtZetaSignedPhaseCoeff
  unfold selbergSqrtZetaSignedPhaseFrequency
  rw [show
      (selbergSqrtZetaTaperedCoeff X d : ℂ) *
            (selbergSqrtZetaTaperedCoeff X l : ℂ) *
            (((Real.sqrt m : ℝ) : ℂ)⁻¹ *
              Complex.exp ((-I * (Real.log m : ℂ)) * t)) *
            (((Real.sqrt d : ℝ) : ℂ)⁻¹ *
              Complex.exp ((-I * (Real.log d : ℂ)) * t)) *
            (((Real.sqrt l : ℝ) : ℂ)⁻¹ *
              Complex.exp ((-I * (Real.log l : ℂ)) * (-t))) =
          ((selbergSqrtZetaTaperedCoeff X d : ℂ) *
            (selbergSqrtZetaTaperedCoeff X l : ℂ) *
            ((Real.sqrt m : ℝ) : ℂ)⁻¹ *
            ((Real.sqrt d : ℝ) : ℂ)⁻¹ *
            ((Real.sqrt l : ℝ) : ℂ)⁻¹) *
          (Complex.exp ((-I * (Real.log m : ℂ)) * t) *
            Complex.exp ((-I * (Real.log d : ℂ)) * t) *
            Complex.exp ((-I * (Real.log l : ℂ)) * (-t))) by ring]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The signed finite product is exactly the uncollected exponential
polynomial with frequency `log l-log m-log d`. -/
theorem
    criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_mul_conj_eq_signedTriplePolynomial
    (N X : ℕ) (t : ℝ) :
    ((∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) *
        (starRingEnd ℂ)
          (selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) =
      selbergSqrtZetaSignedTriplePolynomial N X t := by
  rw [
    criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_mul_conj_eq_signedTripleSum]
  unfold selbergSqrtZetaSignedTriplePolynomial
  unfold MathlibAux.exponentialPolynomial
  unfold selbergSqrtZetaSignedPhaseSupport
  let A := Finset.Icc 1 N
  let B := Finset.Icc 1 X
  let F : ℕ × (ℕ × ℕ) → ℂ := fun p =>
    selbergSqrtZetaSignedPhaseCoeff X p *
      Complex.exp
        (I * (selbergSqrtZetaSignedPhaseFrequency p * t))
  calc
    (∑ m ∈ A, ∑ d ∈ B, ∑ l ∈ B,
        (selbergSqrtZetaTaperedCoeff X d : ℂ) *
          (selbergSqrtZetaTaperedCoeff X l : ℂ) *
          (1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          (1 / (d : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          (1 / (l : ℂ) ^ ((1 / 2 : ℂ) - I * t))) =
        ∑ m ∈ A, ∑ d ∈ B, ∑ l ∈ B, F (m, d, l) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro l hl
      exact signedTripleTerm_eq_exponentialTerm
        (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
        (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1)
        (Nat.ne_of_gt (Finset.mem_Icc.mp hl).1) t
    _ = ∑ m ∈ A, ∑ q ∈ B.product B, F (m, q) := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact (Finset.sum_product B B (fun q => F (m, q))).symm
    _ = ∑ p ∈ A.product (B.product B), F p :=
      (Finset.sum_product A (B.product B) F).symm

private theorem exp_I_thetaModel_add_signedFrequency
    (omega t : ℝ) :
    Complex.exp
        (I * ((thetaModel t + omega * t : ℝ) : ℂ)) =
      Complex.exp (I * (thetaModel t : ℂ)) *
        Complex.exp (I * ((omega * t : ℝ) : ℂ)) := by
  rw [show I * ((thetaModel t + omega * t : ℝ) : ℂ) =
      I * (thetaModel t : ℂ) + I * ((omega * t : ℝ) : ℂ) by
    push_cast
    ring]
  exact Complex.exp_add _ _

/-- Attaching `thetaModel` termwise is exactly multiplication of the signed
triple polynomial by the common Hardy phase. -/
theorem selbergSqrtZetaSignedPhasePolynomial_eq_exp_mul_signedTriplePolynomial
    (N X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedPhasePolynomial N X t =
      Complex.exp (I * (thetaModel t : ℂ)) *
        selbergSqrtZetaSignedTriplePolynomial N X t := by
  classical
  unfold selbergSqrtZetaSignedPhasePolynomial
  unfold selbergSqrtZetaSignedTriplePolynomial
  unfold MathlibAux.exponentialPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [exp_I_thetaModel_add_signedFrequency]
  have hcast :
      ((selbergSqrtZetaSignedPhaseFrequency p * t : ℝ) : ℂ) =
        (selbergSqrtZetaSignedPhaseFrequency p : ℂ) * (t : ℂ) := by
    exact Complex.ofReal_mul _ _
  rw [hcast]
  ring

/-- Exact signed square-root-zeta phase-polynomial representation:
`exp(I thetaModel(t))` times the first zeta truncation, the mollifier, and
its complex conjugate equals the finite phase polynomial term by term. -/
theorem
    exp_I_thetaModel_mul_criticalLinePolynomial_mul_sqrtZetaMollifier_mul_conj_eq_signedPhasePolynomial
    (N X : ℕ) (t : ℝ) :
    Complex.exp (I * (thetaModel t : ℂ)) *
        (((∑ m ∈ Finset.Icc 1 N,
            1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) *
          (starRingEnd ℂ)
            (selbergSqrtZetaMollifier X
              ((1 / 2 : ℂ) + I * t))) =
      selbergSqrtZetaSignedPhasePolynomial N X t := by
  rw [
    criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_mul_conj_eq_signedTriplePolynomial]
  exact
    (selbergSqrtZetaSignedPhasePolynomial_eq_exp_mul_signedTriplePolynomial
      N X t).symm

end HardyTheorem
