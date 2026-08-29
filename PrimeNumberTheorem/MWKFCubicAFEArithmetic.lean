import PrimeNumberTheorem.MWKFCubicAFETermwise
import PrimeNumberTheorem.MWKFCubicFiniteExpansion

open Complex
open scoped Interval ComplexConjugate

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# Arithmetic phase and product weight in the cubic AFE

The two positive Dirichlet indices are separated into their exact
critical-line coefficient and a Mellin weight depending only on their product.
-/

def cubicAFEPositiveIndexProduct (p : ℕ × ℕ) : ℕ :=
  (p.1 + 1) * (p.2 + 1)

/-- Exact separation of a shifted Dirichlet term into its critical-line value
and the product-variable Mellin monomial. -/
theorem cubicAFEDirichletTerm_eq_zero_mul_product
    (t : ℝ) (z : ℂ) (p : ℕ × ℕ) :
    cubicAFEDirichletTerm t z p =
      cubicAFEDirichletTerm t 0 p *
        (1 / (cubicAFEPositiveIndexProduct p : ℂ) ^ z) := by
  have ha : ((p.1 + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero p.1
  have hb : ((p.2 + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero p.2
  have hab : (cubicAFEPositiveIndexProduct p : ℂ) ≠ 0 := by
    unfold cubicAFEPositiveIndexProduct
    exact_mod_cast mul_ne_zero (Nat.succ_ne_zero p.1) (Nat.succ_ne_zero p.2)
  unfold cubicAFEDirichletTerm
  have hcast1 : (p.1 + 1 : ℂ) = ((p.1 + 1 : ℕ) : ℂ) := by push_cast; ring
  have hcast2 : (p.2 + 1 : ℂ) = ((p.2 + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast1, hcast2]
  rw [Complex.cpow_add _ _ ha, Complex.cpow_add _ _ hb]
  rw [show cubicAFEPositiveIndexProduct p =
      (p.1 + 1) * (p.2 + 1) by rfl,
    Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  simp only [add_zero]
  field_simp [ha, hb, hab]

private theorem inv_natCast_cpow_one_sub_critical_eq_conj
    (t : ℝ) (n : ℕ) :
    1 / (n + 1 : ℂ) ^ (1 - cubicCriticalPoint t) =
      conj (1 / (n + 1 : ℂ) ^ cubicCriticalPoint t) := by
  have hn : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hcast : (n + 1 : ℂ) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast]
  rw [one_sub_cubicCriticalPoint_eq_conj, map_div₀, map_one]
  congr 1
  rw [Complex.cpow_conj]
  · simp
  · rw [Complex.natCast_arg]
    exact Ne.symm Real.pi_ne_zero

/-- The exact `1/sqrt(mn)` amplitude and `(n/m)^{it}` phase of the AFE
coefficient. -/
theorem cubicAFEDirichletTerm_zero_eq_exp
    (t : ℝ) (p : ℕ × ℕ) :
    cubicAFEDirichletTerm t 0 p =
      (((Real.sqrt (cubicAFEPositiveIndexProduct p) : ℝ) : ℂ)⁻¹) *
        Complex.exp
          ((I * ((Real.log (p.2 + 1) - Real.log (p.1 + 1) : ℝ) : ℂ)) * t) := by
  have hpair := cubicCriticalPair_eq_exp
    (d := p.1 + 1) (e := p.2 + 1)
    (Nat.succ_ne_zero p.1) (Nat.succ_ne_zero p.2) t
  unfold cubicAFEDirichletTerm
  simp only [add_zero]
  rw [inv_natCast_cpow_one_sub_critical_eq_conj]
  simpa [cubicAFEPositiveIndexProduct, cubicCriticalPoint,
    Nat.cast_add, Nat.cast_one] using hpair

/-- The finite-height Mellin weight, depending on the two arithmetic indices
only through their positive product. -/
noncomputable def cubicAFEProductWeightFinite
    (t X V : ℝ) (k : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ y : ℝ in -V..V,
      cubicAFEScalar t (cubicAFEVerticalPoint X y) *
        (1 / (k : ℂ) ^ cubicAFEVerticalPoint X y)

theorem cubicAFEWeightFinite_eq_arithmetic_mul_productWeight
    (t X V : ℝ) (p : ℕ × ℕ) :
    cubicAFEWeightFinite t X V p =
      cubicAFEDirichletTerm t 0 p *
        cubicAFEProductWeightFinite t X V (cubicAFEPositiveIndexProduct p) := by
  unfold cubicAFEWeightFinite cubicAFEProductWeightFinite
  have hintegrand :
      (fun y : ℝ ↦
        cubicAFENormalizedDirichletTerm t (cubicAFEVerticalPoint X y) p) =
      fun y : ℝ ↦ cubicAFEDirichletTerm t 0 p *
        (cubicAFEScalar t (cubicAFEVerticalPoint X y) *
          (1 / (cubicAFEPositiveIndexProduct p : ℂ) ^
            cubicAFEVerticalPoint X y)) := by
    funext y
    rw [cubicAFENormalizedDirichletTerm_eq,
      cubicAFEDirichletTerm_eq_zero_mul_product]
    ring
  rw [hintegrand, intervalIntegral.integral_const_mul]
  ring

/-- Fully exposed finite-height AFE double sum: exact amplitude, phase, and a
weight depending only on `(m+1)(n+1)`. -/
theorem cubicAFEDoubleSumFinite_eq_arithmetic
    (t X V : ℝ) :
    cubicAFEDoubleSumFinite t X V =
      ∑' p : ℕ × ℕ,
        (((Real.sqrt (cubicAFEPositiveIndexProduct p) : ℝ) : ℂ)⁻¹) *
          Complex.exp
            ((I * ((Real.log (p.2 + 1) - Real.log (p.1 + 1) : ℝ) : ℂ)) * t) *
          cubicAFEProductWeightFinite t X V (cubicAFEPositiveIndexProduct p) := by
  unfold cubicAFEDoubleSumFinite
  apply tsum_congr
  intro p
  rw [cubicAFEWeightFinite_eq_arithmetic_mul_productWeight,
    cubicAFEDirichletTerm_zero_eq_exp]

end MWKFCubic
end PrimeNumberTheorem
