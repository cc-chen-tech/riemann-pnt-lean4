import MathlibAux.FiniteZeroComponents

open Set

-- Every complementary point must occur in exactly one genuine open gap;
-- a selected subfamily of convenient zero-free intervals is insufficient.
example {K : Finset ℝ} {U T : ℝ} (hUT : U < T)
    (hK : ∀ t ∈ K, t ∈ Ioo U T) :
    ∃ b : ↥(insert U K) → ℝ,
      (∀ i : ↥(insert U K), U ≤ (i : ℝ) ∧ (i : ℝ) < b i ∧ b i ≤ T) ∧
      (∀ i, b i ∈ insert T K) ∧
      (∀ i : ↥(insert U K), ∀ t ∈ Ioo (i : ℝ) (b i), t ∉ K) ∧
      Pairwise (fun (i j : ↥(insert U K)) =>
        Disjoint (Ioo (i : ℝ) (b i)) (Ioo (j : ℝ) (b j))) ∧
      ∀ t ∈ Ioo U T, t ∉ K ↔ ∃ i : ↥(insert U K), t ∈ Ioo (i : ℝ) (b i) := by
  exact MathlibAux.exists_finite_zero_complement_components hUT hK

#print axioms MathlibAux.exists_finite_zero_complement_components
