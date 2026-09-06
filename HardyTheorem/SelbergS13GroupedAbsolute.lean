import HardyTheorem.SelbergS13BoundedSmoothBridge
import HardyTheorem.SelbergS13AbsoluteBound

open Nat Finset
open scoped BigOperators

namespace HardyTheorem

/-! # Absolute Euler-product bound for the finite grouped S13 mass -/

noncomputable def selbergS13AdmissibleMultiplier
    {rho B : ℕ} [NeZero rho]
    (D : {D : ℕ // D ∈ selbergS13AdmissibleProducts rho B}) :
    factoredNumbers rho.primeFactors := by
  classical
  have hD := Finset.mem_filter.mp
    (show D.1 ∈ (Finset.Icc 1 B).filter fun D =>
      rho ∣ D ∧ selbergS13SupportedBy rho D by
      simpa [selbergS13AdmissibleProducts] using D.2)
  have hDne : D.1 ≠ 0 := Nat.one_le_iff_ne_zero.mp
    (Finset.mem_Icc.mp hD.1).1
  have hDfact : D.1 ∈ factoredNumbers rho.primeFactors :=
    mem_factoredNumbers_of_primeFactors_subset hDne hD.2.2
  exact ⟨D.1 / rho,
    mem_factoredNumbers_of_dvd hDfact (Nat.div_dvd_of_dvd hD.2.1)⟩

@[simp] theorem selbergS13AdmissibleMultiplier_val
    {rho B : ℕ} [NeZero rho]
    (D : {D : ℕ // D ∈ selbergS13AdmissibleProducts rho B}) :
    (selbergS13AdmissibleMultiplier (rho := rho) (B := B) D).1 =
      D.1 / rho := by
  rfl

theorem selbergS13AdmissibleMultiplier_injective
    {rho B : ℕ} [NeZero rho] :
    Function.Injective
      (selbergS13AdmissibleMultiplier (rho := rho) (B := B)) := by
  classical
  intro D E h
  apply Subtype.ext
  have hquot : D.1 / rho = E.1 / rho := by
    simpa using congrArg Subtype.val h
  have hD := Finset.mem_filter.mp
    (show D.1 ∈ (Finset.Icc 1 B).filter fun D =>
      rho ∣ D ∧ selbergS13SupportedBy rho D by
      simpa [selbergS13AdmissibleProducts] using D.2)
  have hE := Finset.mem_filter.mp
    (show E.1 ∈ (Finset.Icc 1 B).filter fun D =>
      rho ∣ D ∧ selbergS13SupportedBy rho D by
      simpa [selbergS13AdmissibleProducts] using E.2)
  calc
    D.1 = rho * (D.1 / rho) := (Nat.mul_div_cancel' hD.2.1).symm
    _ = rho * (E.1 / rho) := by rw [hquot]
    _ = E.1 := Nat.mul_div_cancel' hE.2.1

noncomputable def selbergS13AdmissibleMultiplierSet
    (rho B : ℕ) [NeZero rho] :
    Finset (factoredNumbers rho.primeFactors) := by
  classical
  exact (selbergS13AdmissibleProducts rho B).attach.image
    (selbergS13AdmissibleMultiplier (rho := rho) (B := B))

private theorem selbergS13AdmissibleReciprocalSum_le_eulerProduct
    (rho B : ℕ) [NeZero rho] :
    (∑ D ∈ selbergS13AdmissibleProducts rho B, (D : ℝ)⁻¹) ≤
      (rho : ℝ)⁻¹ *
        ∏ p ∈ rho.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
  classical
  let S := selbergS13AdmissibleProducts rho B
  let M := selbergS13AdmissibleMultiplierSet rho B
  have hinj := selbergS13AdmissibleMultiplier_injective
    (rho := rho) (B := B)
  have hfactor (D : {D : ℕ // D ∈ S}) :
      (D.1 : ℝ)⁻¹ = (rho : ℝ)⁻¹ *
        ((selbergS13AdmissibleMultiplier (rho := rho) (B := B) D).1 : ℝ)⁻¹ := by
    have hD := Finset.mem_filter.mp
      (show D.1 ∈ (Finset.Icc 1 B).filter fun D =>
        rho ∣ D ∧ selbergS13SupportedBy rho D by
        simpa [S, selbergS13AdmissibleProducts] using D.2)
    have hprod : rho * (D.1 / rho) = D.1 := Nat.mul_div_cancel' hD.2.1
    simp only [selbergS13AdmissibleMultiplier_val]
    have hprodR : (rho : ℝ) * ((D.1 / rho : ℕ) : ℝ) = (D.1 : ℝ) := by
      exact_mod_cast hprod
    rw [← hprodR, mul_inv_rev]
    ring
  calc
    (∑ D ∈ selbergS13AdmissibleProducts rho B, (D : ℝ)⁻¹) =
        ∑ D ∈ S.attach, (D.1 : ℝ)⁻¹ := by
      simpa only [S] using
        (Finset.sum_attach S (fun D : ℕ => (D : ℝ)⁻¹)).symm
    _ = (rho : ℝ)⁻¹ *
        ∑ D ∈ S.attach,
          ((selbergS13AdmissibleMultiplier
            (rho := rho) (B := B) D).1 : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D _hD
      exact hfactor D
    _ = (rho : ℝ)⁻¹ * ∑ m ∈ M, (m.1 : ℝ)⁻¹ := by
      congr 1
      dsimp [M, selbergS13AdmissibleMultiplierSet]
      rw [Finset.sum_image]
      intro x _hx y _hy hxy
      exact hinj hxy
    _ ≤ (rho : ℝ)⁻¹ *
        ∏ p ∈ rho.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
      exact mul_le_mul_of_nonneg_left
        (selbergS13FiniteSupportedReciprocalSum_le_eulerProduct rho M)
        (by positivity)

theorem selbergS13FiniteGroupedMass_le_two_mul_plus
    (rho B : ℕ) [NeZero rho] :
    selbergS13FiniteGroupedMass rho B ≤
      2 * (rho : ℝ)⁻¹ *
        ∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹) := by
  calc
    selbergS13FiniteGroupedMass rho B ≤
        ∑ D ∈ selbergS13AdmissibleProducts rho B, (D : ℝ)⁻¹ :=
      selbergS13FiniteGroupedMass_le_reciprocalSum rho B
    _ ≤ (rho : ℝ)⁻¹ *
        ∏ p ∈ rho.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ :=
      selbergS13AdmissibleReciprocalSum_le_eulerProduct rho B
    _ ≤ (rho : ℝ)⁻¹ *
        (2 * ∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left
        (selbergS13MinusEulerProduct_le_two_mul_plus rho) (by positivity)
    _ = 2 * (rho : ℝ)⁻¹ *
        ∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹) := by ring

theorem selbergS13BoundedSmoothPairMass_le_two_mul_plus
    (rho X : ℕ) [NeZero rho] :
    selbergS13BoundedSmoothPairMass rho X ≤
      2 * (rho : ℝ)⁻¹ *
        ∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹) :=
  (selbergS13BoundedSmoothPairMass_le_grouped rho X).trans
    (selbergS13FiniteGroupedMass_le_two_mul_plus rho (X * X))

end HardyTheorem
