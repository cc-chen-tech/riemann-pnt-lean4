import HardyTheorem.SelbergSArithmeticDivisorMajorant
import HardyTheorem.SelbergSArithmeticHarmonic

open scoped BigOperators

namespace HardyTheorem

/-!
# A finite nonnegative Dirichlet-convolution bound

Pairs in the divisor antidiagonal of some `r ∈ [1,Y]` inject into the
rectangle `[1,Y] × [1,Y]`.  This is the finite form of the nonnegative
Dirichlet-convolution estimate used in the Selberg arithmetic tail.
-/

theorem selberg_finite_dirichlet_sum_le_product
    (Y : ℕ) {b c : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (hc : ∀ n, 0 ≤ c n) :
    (∑ r ∈ Finset.Icc 1 Y,
      ∑ p ∈ r.divisorsAntidiagonal, b p.1 * c p.2) ≤
      (∑ d ∈ Finset.Icc 1 Y, b d) *
        ∑ m ∈ Finset.Icc 1 Y, c m := by
  classical
  let A : Finset ℕ := Finset.Icc 1 Y
  let S : Finset (Σ _ : ℕ, ℕ × ℕ) :=
    A.sigma fun r => r.divisorsAntidiagonal
  let P : Finset (ℕ × ℕ) :=
    (A.product A).filter fun p => p.1 * p.2 ∈ A
  calc
    (∑ r ∈ Finset.Icc 1 Y,
        ∑ p ∈ r.divisorsAntidiagonal, b p.1 * c p.2) =
        ∑ x ∈ S, b x.2.1 * c x.2.2 := by
      exact Finset.sum_sigma' A (fun r => r.divisorsAntidiagonal)
        (fun r p => b p.1 * c p.2)
    _ = ∑ p ∈ P, b p.1 * c p.2 := by
      apply Finset.sum_nbij (fun x => x.2)
      · intro x hx
        have hx := Finset.mem_sigma.mp hx
        rcases hx with ⟨hrA, hp⟩
        have hrange : 1 ≤ x.1 ∧ x.1 ≤ Y := by
          simpa only [A, Finset.mem_Icc] using hrA
        have hp₁mem := Nat.fst_mem_divisors_of_mem_antidiagonal hp
        have hp₂mem := Nat.snd_mem_divisors_of_mem_antidiagonal hp
        have hp₁range : 1 ≤ x.2.1 ∧ x.2.1 ≤ Y := by
          constructor
          · exact Nat.one_le_iff_ne_zero.mpr
              (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp)
          · exact (Nat.divisor_le hp₁mem).trans hrange.2
        have hp₂range : 1 ≤ x.2.2 ∧ x.2.2 ≤ Y := by
          constructor
          · exact Nat.one_le_iff_ne_zero.mpr
              (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp)
          · exact (Nat.divisor_le hp₂mem).trans hrange.2
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_product.mpr
          simpa only [A, Finset.mem_Icc] using ⟨hp₁range, hp₂range⟩
        · simpa only [A, Finset.mem_Icc,
            (Nat.mem_divisorsAntidiagonal.mp hp).1] using hrange
      · intro x₁ hx₁ x₂ hx₂ h
        have hx₁ := Finset.mem_sigma.mp hx₁
        have hx₂ := Finset.mem_sigma.mp hx₂
        rcases x₁ with ⟨r, p⟩
        rcases x₂ with ⟨s, q⟩
        simp only at h
        have hr := (Nat.mem_divisorsAntidiagonal.mp hx₁.2).1
        have hs := (Nat.mem_divisorsAntidiagonal.mp hx₂.2).1
        subst q
        have hrs : r = s := hr.symm.trans hs
        subst s
        rfl
      · intro p hp
        have hp := Finset.mem_filter.mp hp
        have hpA := Finset.mem_product.mp hp.1
        refine ⟨⟨p.1 * p.2, p⟩, ?_, rfl⟩
        apply Finset.mem_sigma.mpr
        refine ⟨hp.2, ?_⟩
        have hp₁ : p.1 ≠ 0 := by
          have : p.1 ∈ A := hpA.1
          have hrange : 1 ≤ p.1 ∧ p.1 ≤ Y := by
            simpa only [A, Finset.mem_Icc] using this
          exact Nat.one_le_iff_ne_zero.mp hrange.1
        have hp₂ : p.2 ≠ 0 := by
          have : p.2 ∈ A := hpA.2
          have hrange : 1 ≤ p.2 ∧ p.2 ≤ Y := by
            simpa only [A, Finset.mem_Icc] using this
          exact Nat.one_le_iff_ne_zero.mp hrange.1
        exact Nat.mem_divisorsAntidiagonal.mpr
          ⟨rfl, Nat.mul_ne_zero hp₁ hp₂⟩
      · intro x _
        rfl
    _ ≤ ∑ p ∈ A.product A, b p.1 * c p.2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) ?_
      intro p _ _
      exact mul_nonneg (hb p.1) (hc p.2)
    _ = (∑ d ∈ Finset.Icc 1 Y, b d) *
          ∑ m ∈ Finset.Icc 1 Y, c m := by
      change (∑ p ∈ A ×ˢ A, b p.1 * c p.2) = _
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

end HardyTheorem
