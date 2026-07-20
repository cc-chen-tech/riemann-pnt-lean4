import HardyTheorem.SelbergShortCollectedEnergy

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Weighted square energy for collected Selberg coefficients

The finite Cauchy--Schwarz inequality below keeps the two square energies
separate.  Unlike the constant-function specialization, it introduces no
factor equal to the cardinality of the summation fiber.
-/

/-- Finite complex Cauchy--Schwarz for a sum of products, expressed using
`Complex.normSq`.  In particular, the bound has no cardinality factor. -/
theorem normSq_finset_sum_mul_le_sum_normSq_mul_sum_normSq
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, f i * g i) ≤
      (∑ i ∈ s, Complex.normSq (f i)) *
        ∑ i ∈ s, Complex.normSq (g i) := by
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖∑ i ∈ s, f i * g i‖ ^ 2 ≤
        (∑ i ∈ s, ‖f i * g i‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ = (∑ i ∈ s, ‖f i‖ * ‖g i‖) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      rw [norm_mul]
    _ ≤ (∑ i ∈ s, ‖f i‖ ^ 2) *
        ∑ i ∈ s, ‖g i‖ ^ 2 :=
      sum_mul_sq_le_sq_mul_sq s (fun i => ‖f i‖) (fun i => ‖g i‖)
    _ = (∑ i ∈ s, Complex.normSq (f i)) *
        ∑ i ∈ s, Complex.normSq (g i) := by
      simp only [Complex.normSq_eq_norm_sq]

/-- Weighted Cauchy--Schwarz on one collected Selberg product fiber.  The
normalization `1 / sqrt k` is split as `1 / sqrt d` times `1 / sqrt l`
for every factorization `d * l = k`.  No fiber-cardinality factor occurs. -/
theorem normSq_selbergShortDirichletCollectedCoeff_le_weightedPairEnergy
    (N X k : ℕ) :
    Complex.normSq (selbergShortDirichletCollectedCoeff N X k) ≤
      (∑ p ∈ selbergMollifiedDirichletPairs (N * X) X k,
          Complex.normSq
            ((selbergMollifiedDirichletCoeff N X p.1 : ℂ) *
              (Real.sqrt (p.1 : ℝ) : ℂ)⁻¹)) *
        ∑ p ∈ selbergMollifiedDirichletPairs (N * X) X k,
          Complex.normSq
            ((selbergMoebiusCoeff X p.2 : ℂ) *
              (Real.sqrt (p.2 : ℝ) : ℂ)⁻¹) := by
  classical
  let S := selbergMollifiedDirichletPairs (N * X) X k
  let f : ℕ × ℕ → ℂ := fun p =>
    (selbergMollifiedDirichletCoeff N X p.1 : ℂ) *
      (Real.sqrt (p.1 : ℝ) : ℂ)⁻¹
  let g : ℕ × ℕ → ℂ := fun p =>
    (selbergMoebiusCoeff X p.2 : ℂ) *
      (Real.sqrt (p.2 : ℝ) : ℂ)⁻¹
  have hterm : ∀ p ∈ S,
      selbergShortCollectedPairTerm N X k p = f p * g p := by
    intro p hp
    have hprod : p.1 * p.2 = k := (Finset.mem_filter.mp hp).2
    have hsqrt :
        Real.sqrt (k : ℝ) =
          Real.sqrt (p.1 : ℝ) * Real.sqrt (p.2 : ℝ) := by
      rw [← hprod, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p.1)]
    dsimp only [selbergShortCollectedPairTerm, f, g]
    rw [hsqrt]
    push_cast
    rw [mul_inv_rev]
    ring
  rw [selbergShortDirichletCollectedCoeff_eq_pairSum]
  change Complex.normSq (∑ p ∈ S, selbergShortCollectedPairTerm N X k p) ≤ _
  calc
    Complex.normSq (∑ p ∈ S, selbergShortCollectedPairTerm N X k p) =
        Complex.normSq (∑ p ∈ S, f p * g p) := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      exact hterm p hp
    _ ≤ (∑ p ∈ S, Complex.normSq (f p)) *
        ∑ p ∈ S, Complex.normSq (g p) :=
      normSq_finset_sum_mul_le_sum_normSq_mul_sum_normSq S f g
    _ = _ := by rfl

end HardyTheorem
