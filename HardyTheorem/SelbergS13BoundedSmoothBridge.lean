import HardyTheorem.SelbergSArithmeticFactorBound
import HardyTheorem.SelbergS13DivisorPair

open Nat Finset
open scoped BigOperators

namespace HardyTheorem

/-! # Bridge from the bounded smooth pair set to Selberg's S13 mass -/

noncomputable def selbergS13BoundedSmoothPairs
    (rho X : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 X).product (Finset.Icc 1 X)).filter fun p =>
    p.1 ∈ factoredNumbers rho.primeFactors ∧
      p.2 ∈ factoredNumbers rho.primeFactors ∧
      rho ∣ p.1 * p.2

noncomputable def selbergS13BoundedSmoothPairMass
    (rho X : ℕ) : ℝ :=
  ∑ p ∈ selbergS13BoundedSmoothPairs rho X,
    |selbergSqrtZetaCoeff p.1 * selbergSqrtZetaCoeff p.2| /
      ((p.1 * p.2 : ℕ) : ℝ)

theorem selbergS13BoundedSmoothPairMass_eq_outer_sum
    (rho X : ℕ) :
    selbergS13BoundedSmoothPairMass rho X =
      ∑ d : selbergSmoothOuterIndex rho X,
        ∑ e : selbergSmoothOuterIndex rho X,
          if rho ∣ d.1 * e.1 then
            |selbergSqrtZetaCoeff d.1 * selbergSqrtZetaCoeff e.1| /
              ((d.1 * e.1 : ℕ) : ℝ)
          else 0 := by
  classical
  let O : Finset ℕ := Finset.univ.image
    (fun d : selbergSmoothOuterIndex rho X => d.1)
  have hO (n : ℕ) : n ∈ O ↔
      n ∈ Finset.Icc 1 X ∧ n ∈ factoredNumbers rho.primeFactors := by
    constructor
    · intro hn
      rcases Finset.mem_image.mp hn with ⟨d, _hd, rfl⟩
      exact d.2
    · intro hn
      exact Finset.mem_image.mpr ⟨⟨n, hn⟩, Finset.mem_univ _, rfl⟩
  have hPairs : selbergS13BoundedSmoothPairs rho X =
      (O.product O).filter fun p => rho ∣ p.1 * p.2 := by
    ext p
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp
        (show p ∈ ((Finset.Icc 1 X).product (Finset.Icc 1 X)).filter fun p =>
          p.1 ∈ factoredNumbers rho.primeFactors ∧
            p.2 ∈ factoredNumbers rho.primeFactors ∧
            rho ∣ p.1 * p.2 by
          simpa [selbergS13BoundedSmoothPairs] using hp)
      have hIcc := Finset.mem_product.mp hp'.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(hO p.1).mpr ⟨hIcc.1, hp'.2.1⟩,
          (hO p.2).mpr ⟨hIcc.2, hp'.2.2.1⟩⟩, hp'.2.2.2⟩
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      have hOmem := Finset.mem_product.mp hp'.1
      have hd := (hO p.1).mp hOmem.1
      have he := (hO p.2).mp hOmem.2
      exact (show p ∈ selbergS13BoundedSmoothPairs rho X by
        unfold selbergS13BoundedSmoothPairs
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hd.1, he.1⟩,
            hd.2, he.2, hp'.2⟩)
  unfold selbergS13BoundedSmoothPairMass
  rw [hPairs, Finset.sum_filter]
  calc
    (∑ a ∈ O.product O,
        if rho ∣ a.1 * a.2 then
          |selbergSqrtZetaCoeff a.1 * selbergSqrtZetaCoeff a.2| /
            ((a.1 * a.2 : ℕ) : ℝ)
        else 0) =
      ∑ d ∈ O, ∑ e ∈ O,
        if rho ∣ d * e then
          |selbergSqrtZetaCoeff d * selbergSqrtZetaCoeff e| /
            ((d * e : ℕ) : ℝ)
        else 0 := Finset.sum_product O O _
    _ = _ := by
      dsimp [O]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro d _hd
        rw [Finset.sum_image]
        exact Subtype.val_injective.injOn
      · exact Subtype.val_injective.injOn

noncomputable def selbergS13RestrictedPairs
    (rho D : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact D.divisorsAntidiagonal.filter fun p =>
    selbergS13SupportedBy rho p.1 ∧ selbergS13SupportedBy rho p.2

private theorem selbergS13BoundedSmoothPair_product_admissible
    {rho X : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ selbergS13BoundedSmoothPairs rho X) :
    p.1 * p.2 ∈ selbergS13AdmissibleProducts rho (X * X) := by
  classical
  have hp' := Finset.mem_filter.mp
    (show p ∈ ((Finset.Icc 1 X).product (Finset.Icc 1 X)).filter fun p =>
      p.1 ∈ factoredNumbers rho.primeFactors ∧
        p.2 ∈ factoredNumbers rho.primeFactors ∧
        rho ∣ p.1 * p.2 by
      simpa [selbergS13BoundedSmoothPairs] using hp)
  have hIcc := Finset.mem_product.mp hp'.1
  have hpos : 1 ≤ p.1 * p.2 := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero
      (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hIcc.1).1)
      (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hIcc.2).1))
  have hupper : p.1 * p.2 ≤ X * X :=
    Nat.mul_le_mul (Finset.mem_Icc.mp hIcc.1).2
      (Finset.mem_Icc.mp hIcc.2).2
  have hsupp : p.1 * p.2 ∈ factoredNumbers rho.primeFactors :=
    mul_mem_factoredNumbers hp'.2.1 hp'.2.2.1
  unfold selbergS13AdmissibleProducts
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hpos, hupper⟩, hp'.2.2.2,
    primeFactors_subset_of_mem_factoredNumbers hsupp⟩

private theorem selbergS13BoundedSmoothPair_fiber_subset
    {rho X D : ℕ} :
    {p ∈ selbergS13BoundedSmoothPairs rho X | p.1 * p.2 = D} ⊆
      selbergS13RestrictedPairs rho D := by
  classical
  intro p hp
  have hpP := (Finset.mem_filter.mp hp).1
  have hpD := (Finset.mem_filter.mp hp).2
  have hp' := Finset.mem_filter.mp
    (show p ∈ ((Finset.Icc 1 X).product (Finset.Icc 1 X)).filter fun p =>
      p.1 ∈ factoredNumbers rho.primeFactors ∧
        p.2 ∈ factoredNumbers rho.primeFactors ∧
        rho ∣ p.1 * p.2 by
      simpa [selbergS13BoundedSmoothPairs] using hpP)
  have hIcc := Finset.mem_product.mp hp'.1
  have hDne : D ≠ 0 := by
    rw [← hpD]
    exact Nat.mul_ne_zero
      (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hIcc.1).1)
      (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hIcc.2).1)
  unfold selbergS13RestrictedPairs
  apply Finset.mem_filter.mpr
  exact ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨hpD, hDne⟩,
    primeFactors_subset_of_mem_factoredNumbers hp'.2.1,
    primeFactors_subset_of_mem_factoredNumbers hp'.2.2.1⟩

/-- The actual bounded smooth pair mass is a submass of the finite grouped
S13 quantity. -/
theorem selbergS13BoundedSmoothPairMass_le_grouped
    (rho X : ℕ) :
    selbergS13BoundedSmoothPairMass rho X ≤
      selbergS13FiniteGroupedMass rho (X * X) := by
  classical
  let P := selbergS13BoundedSmoothPairs rho X
  let A := selbergS13AdmissibleProducts rho (X * X)
  let f : ℕ × ℕ → ℝ := fun p =>
    |selbergSqrtZetaCoeff p.1 * selbergSqrtZetaCoeff p.2| /
      ((p.1 * p.2 : ℕ) : ℝ)
  have hmap : ∀ p ∈ P, p.1 * p.2 ∈ A := by
    intro p hp
    exact selbergS13BoundedSmoothPair_product_admissible hp
  have hfiber (D : ℕ) (hD : D ∈ A) :
      (∑ p ∈ P with p.1 * p.2 = D, f p) ≤
        selbergS13RestrictedDivisorPairMass rho D / (D : ℝ) := by
    have hsubset : {p ∈ P | p.1 * p.2 = D} ⊆
        selbergS13RestrictedPairs rho D := by
      simpa only [P] using
        (selbergS13BoundedSmoothPair_fiber_subset (rho := rho) (X := X) (D := D))
    calc
      (∑ p ∈ P with p.1 * p.2 = D, f p) =
          ∑ p ∈ {p ∈ P | p.1 * p.2 = D},
            |selbergSqrtZetaCoeff p.1 * selbergSqrtZetaCoeff p.2| /
              (D : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpEq := (Finset.mem_filter.mp hp).2
        dsimp [f]
        rw [hpEq]
      _ ≤ ∑ p ∈ selbergS13RestrictedPairs rho D,
          |selbergSqrtZetaCoeff p.1 * selbergSqrtZetaCoeff p.2| /
            (D : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro p _hp _hnot
        positivity
      _ = selbergS13RestrictedDivisorPairMass rho D / (D : ℝ) := by
        unfold selbergS13RestrictedDivisorPairMass selbergS13RestrictedPairs
        rw [Finset.sum_div]
  unfold selbergS13BoundedSmoothPairMass selbergS13FiniteGroupedMass
  change (∑ p ∈ P, f p) ≤
    ∑ D ∈ A, selbergS13RestrictedDivisorPairMass rho D / (D : ℝ)
  rw [← Finset.sum_fiberwise_of_maps_to hmap f]
  exact Finset.sum_le_sum fun D hD => hfiber D hD

end HardyTheorem
