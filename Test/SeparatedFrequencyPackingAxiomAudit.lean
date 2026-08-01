import MathlibAux.SeparatedFrequencyPacking

#check MathlibAux.card_sub_one_mul_separation_le_two_mul_radius

example (S : Finset ℝ) (Δ ξ r : ℝ)
    (hΔ : 0 < Δ) (hr : 0 ≤ r)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Δ ≤ |x - y|)
    (hball : ∀ x ∈ S, |x - ξ| ≤ r) :
    (((S.card - 1 : ℕ) : ℝ) * Δ) ≤ 2 * r := by
  exact MathlibAux.card_sub_one_mul_separation_le_two_mul_radius
    S Δ ξ r hΔ hr hsep hball

#print axioms MathlibAux.card_sub_one_mul_separation_le_two_mul_radius
