import HardyTheorem.ConreyCoprimeMobiusResidue
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries

open Complex Nat
open scoped BigOperators

namespace HardyTheorem

/-! The finite Euler inverse retains its full modulus-dependent positive
majorant. Only the square correction is replaced by an absolute constant. -/

noncomputable def conreyEulerCorrectionConstant : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))

noncomputable def conreyCoprimeEulerMajorant (m : ℕ) (δ : ℝ) : ℝ :=
  ∏ p ∈ m.primeFactors, (1 + (p : ℝ) ^ (-(1 - 2 * δ)))

theorem conreyCoprimeEulerMajorant_nonneg (m : ℕ) (δ : ℝ) :
    0 ≤ conreyCoprimeEulerMajorant m δ := by
  unfold conreyCoprimeEulerMajorant
  positivity

private theorem summable_conreyEulerCorrection :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(7 / 4 : ℝ))) :=
  Real.summable_nat_rpow.mpr (by norm_num)

theorem one_le_conreyEulerCorrectionConstant : 1 ≤ conreyEulerCorrectionConstant := by
  have h := summable_conreyEulerCorrection.sum_le_tsum ({1} : Finset ℕ)
    (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  simpa [conreyEulerCorrectionConstant] using h

private noncomputable def correctionHom : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-(7 / 4 : ℝ))
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

private theorem correctionHom_apply (n : ℕ) :
    correctionHom n = (n : ℝ) ^ (-(7 / 4 : ℝ)) := rfl

private theorem correctionEulerProduct_le (m : ℕ) :
    (∏ p ∈ m.primeFactors, (1 - (p : ℝ) ^ (-(7 / 4 : ℝ)))⁻¹) ≤
      conreyEulerCorrectionConstant := by
  have hp : ∀ {p : ℕ}, p.Prime → ‖correctionHom p‖ < 1 := by
    intro p hp
    change ‖(p : ℝ) ^ (-(7 / 4 : ℝ))‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by norm_num)
  have he := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := correctionHom) hp m.primeFactors).2
  have he' : HasSum (fun n : factoredNumbers m.primeFactors =>
      (n.1 : ℝ) ^ (-(7 / 4 : ℝ)))
      (∏ p ∈ m.primeFactors, (1 - (p : ℝ) ^ (-(7 / 4 : ℝ)))⁻¹) := by
    simpa only [correctionHom_apply, Finset.filter_eq_self.mpr
      (fun p hp => Nat.prime_of_mem_primeFactors hp)] using he
  rw [← he'.tsum_eq]
  exact Summable.tsum_subtype_le _ _
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) summable_conreyEulerCorrection

private theorem norm_prime_inverse_le (p : ℕ) (hp : p.Prime)
    {δ : ℝ} (hδ16 : δ ≤ 1 / 16) {z : ℂ} (hz : -2 * δ ≤ z.re) :
    ‖(1 - (p : ℂ) ^ (-(1 + z)))⁻¹‖ ≤
      (1 + (p : ℝ) ^ (-(1 - 2 * δ))) *
        (1 - (p : ℝ) ^ (-(7 / 4 : ℝ)))⁻¹ := by
  let r := (p : ℝ) ^ (-(1 - 2 * δ))
  let q := (p : ℝ) ^ (-(7 / 4 : ℝ))
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hr : 0 ≤ r := Real.rpow_nonneg hp0 _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
  have hrsq : r ^ 2 ≤ q := by
    calc
      r ^ 2 = (p : ℝ) ^ (-(1 - 2 * δ) * 2) := by
        rw [Real.rpow_mul hp0, Real.rpow_two]
      _ ≤ q := Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  have hpow : ‖(p : ℂ) ^ (-(1 + z))‖ ≤ r := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, neg_re, add_re, one_re]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  have hden : 1 - r ≤ ‖1 - (p : ℂ) ^ (-(1 + z))‖ := by
    calc
      1 - r ≤ ‖(1 : ℂ)‖ - ‖(p : ℂ) ^ (-(1 + z))‖ := by simpa using sub_le_sub_left hpow 1
      _ ≤ _ := norm_sub_norm_le _ _
  have hbase : 0 < 1 - r := sub_pos.mpr hr1
  have hqbase : 0 < 1 - q := sub_pos.mpr hq1
  calc
    _ = ‖1 - (p : ℂ) ^ (-(1 + z))‖⁻¹ := norm_inv _
    _ ≤ (1 - r)⁻¹ := (inv_le_inv₀ (hbase.trans_le hden) hbase).mpr hden
    _ ≤ (1 + r) * (1 - q)⁻¹ := by
      have hratio : 1 / (1 - r) ≤ (1 + r) / (1 - q) :=
        (div_le_div_iff₀ hbase hqbase).mpr (by nlinarith)
      simpa only [div_eq_mul_inv, one_mul] using hratio

/-- The actual finite inverse is bounded by `zeta(7/4)` times the retained
positive Euler majorant, uniformly in modulus, shift and `0 ≤ delta ≤ 1/16`. -/
theorem norm_conreyCoprimeEulerInverse_le (m : ℕ) {δ : ℝ}
    (_hδ : 0 ≤ δ) (hδ16 : δ ≤ 1 / 16) {z : ℂ} (hz : -2 * δ ≤ z.re) :
    ‖conreyCoprimeEulerInverse m z‖ ≤
      conreyEulerCorrectionConstant * conreyCoprimeEulerMajorant m δ := by
  unfold conreyCoprimeEulerInverse
  rw [← Finset.prod_inv_distrib]
  calc
    _ ≤ ∏ p ∈ m.primeFactors, ‖(1 - (p : ℂ) ^ (-(1 + z)))⁻¹‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ p ∈ m.primeFactors,
        ((1 + (p : ℝ) ^ (-(1 - 2 * δ))) * (1 - (p : ℝ) ^ (-(7 / 4 : ℝ)))⁻¹) := by
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun p hp => norm_prime_inverse_le p (Nat.prime_of_mem_primeFactors hp) hδ16 hz)
    _ = conreyCoprimeEulerMajorant m δ *
        ∏ p ∈ m.primeFactors, (1 - (p : ℝ) ^ (-(7 / 4 : ℝ)))⁻¹ := by
      rw [Finset.prod_mul_distrib]; rfl
    _ ≤ conreyCoprimeEulerMajorant m δ * conreyEulerCorrectionConstant :=
      mul_le_mul_of_nonneg_left (correctionEulerProduct_le m) (conreyCoprimeEulerMajorant_nonneg m δ)
    _ = _ := mul_comm _ _

end HardyTheorem
