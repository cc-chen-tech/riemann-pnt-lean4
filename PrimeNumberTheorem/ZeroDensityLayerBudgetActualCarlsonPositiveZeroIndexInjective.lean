import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonPositiveZeroTail

/-!
# Uniqueness of actual Carlson positive-zero indices

The base interval has ordinate at most one, while dyadic shell `n` has
ordinate in `(2^n, 2^(n+1)]`.  These intervals are pairwise disjoint, so the
combined actual Carlson index represents each positive zero at most once.
-/

namespace PrimeNumberTheorem

/-- A complex zero cannot belong to two different actual Carlson dyadic
shells. -/
theorem actualCarlsonDyadicZeroShell_index_unique
    {sigma : ℝ} {n m : ℕ} {rho : ℂ}
    (hn : rho ∈ actualCarlsonDyadicZeroShell sigma n)
    (hm : rho ∈ actualCarlsonDyadicZeroShell sigma m) :
    n = m := by
  have hnUpper :
      rho.im ≤ (2 : ℝ) ^ (n + 1) :=
    (ZeroDensity.mem_zeroDensityZerosFinset.mp
      (Finset.mem_sdiff.mp hn).1).2.2.1
  have hmUpper :
      rho.im ≤ (2 : ℝ) ^ (m + 1) :=
    (ZeroDensity.mem_zeroDensityZerosFinset.mp
      (Finset.mem_sdiff.mp hm).1).2.2.1
  have hnLower :
      (2 : ℝ) ^ n < rho.im :=
    actualCarlsonDyadicZeroShell_im_gt hn
  have hmLower :
      (2 : ℝ) ^ m < rho.im :=
    actualCarlsonDyadicZeroShell_im_gt hm
  by_contra hne
  rcases lt_or_gt_of_ne hne with hnm | hmn
  · have hnm' : n + 1 ≤ m := by omega
    have hpow :
        (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ m :=
      pow_le_pow_right₀ (by norm_num) hnm'
    linarith
  · have hmn' : m + 1 ≤ n := by omega
    have hpow :
        (2 : ℝ) ^ (m + 1) ≤ (2 : ℝ) ^ n :=
      pow_le_pow_right₀ (by norm_num) hmn'
    linarith

/-- The combined base-plus-dyadic Carlson indexing has no duplicate complex
zeros. -/
theorem actualCarlsonPositiveZero_injective
    {sigma : ℝ} :
    Function.Injective
      (@actualCarlsonPositiveZero sigma) := by
  intro index₁ index₂ hzero
  cases index₁ with
  | inl rho =>
      cases index₂ with
      | inl eta =>
          have hrho : rho = eta := by
            apply Subtype.ext
            simpa [actualCarlsonPositiveZero] using hzero
          subst eta
          rfl
      | inr index =>
          exfalso
          have hbase :
              (rho : ℂ).im ≤ 1 :=
            (ZeroDensity.mem_zeroDensityZerosFinset.mp rho.property).2.2.1
          have hshell :
              (2 : ℝ) ^ index.1 < index.2.1.im :=
            actualCarlsonDyadicZeroShell_im_gt index.2.property
          have honePow : (1 : ℝ) ≤ (2 : ℝ) ^ index.1 := by
            exact
              pow_le_pow_right₀ (by norm_num) (Nat.zero_le index.1)
          have hsame :
              (rho : ℂ) = index.2.1 := by
            simpa [actualCarlsonPositiveZero] using hzero
          rw [← hsame] at hshell
          linarith
  | inr index =>
      cases index₂ with
      | inl rho =>
          exfalso
          have hbase :
              (rho : ℂ).im ≤ 1 :=
            (ZeroDensity.mem_zeroDensityZerosFinset.mp rho.property).2.2.1
          have hshell :
              (2 : ℝ) ^ index.1 < index.2.1.im :=
            actualCarlsonDyadicZeroShell_im_gt index.2.property
          have honePow : (1 : ℝ) ≤ (2 : ℝ) ^ index.1 := by
            exact
              pow_le_pow_right₀ (by norm_num) (Nat.zero_le index.1)
          have hsame :
              index.2.1 = (rho : ℂ) := by
            simpa [actualCarlsonPositiveZero] using hzero
          rw [hsame] at hshell
          linarith
      | inr other =>
          rcases index with ⟨n, rho⟩
          rcases other with ⟨m, eta⟩
          have hsame :
              (rho : ℂ) = (eta : ℂ) := by
            simpa [actualCarlsonPositiveZero] using hzero
          have heta :
              (rho : ℂ) ∈ actualCarlsonDyadicZeroShell sigma m := by
            simpa [hsame] using eta.property
          have hnm :
              n = m :=
            actualCarlsonDyadicZeroShell_index_unique rho.property heta
          subst m
          have hrho : rho = eta := Subtype.ext hsame
          subst eta
          rfl

/-- The indexed Carlson weight is exactly the analytic-multiplicity
coefficient of the represented complex zero. -/
theorem actualCarlsonPositiveZeroWeight_eq_coefficient
    {sigma : ℝ} (index : ActualCarlsonPositiveZeroIndex sigma) :
    actualCarlsonPositiveZeroWeight index =
      (analyticOrderNatAt riemannZeta
        (actualCarlsonPositiveZero index) : ℝ) /
        ‖actualCarlsonPositiveZero index‖ := by
  cases index <;>
    rfl

end PrimeNumberTheorem
