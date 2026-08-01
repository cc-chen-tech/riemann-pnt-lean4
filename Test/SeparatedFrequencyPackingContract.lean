import MathlibAux.SeparatedFrequencyPacking

namespace MathlibAux

#check (card_sub_one_mul_separation_le_two_mul_radius :
  ∀ (S : Finset ℝ) (Δ ξ r : ℝ),
    0 < Δ → 0 ≤ r →
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → Δ ≤ |x - y|) →
    (∀ x ∈ S, |x - ξ| ≤ r) →
    (((S.card - 1 : ℕ) : ℝ) * Δ) ≤ 2 * r)

end MathlibAux
