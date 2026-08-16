import PrimeNumberTheorem.VKEdgeDynamicZeroPacketIteration

open Complex
open scoped BigOperators

open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo

#check
  (dynamicZeroPacketExpansionState :
    Finset ℂ → (ℕ → ℝ) → (ℕ → ℕ) → ℕ → Finset ℂ)

#check
  (dynamicZeroPacketAtStep :
    Finset ℂ → (ℕ → ℝ) → (ℕ → ℕ) → ℕ → Finset ℂ)

#check
  (dynamicZeroPacketAtStep_disjoint_state :
    ∀ (S0 : Finset ℂ) (height : ℕ → ℝ) (bucket : ℕ → ℕ) (k : ℕ),
      Disjoint
        (dynamicZeroPacketExpansionState S0 height bucket k)
        (dynamicZeroPacketAtStep S0 height bucket k))

#check
  (dynamicZeroPacketAtStep_subset_height :
    ∀ (S0 : Finset ℂ) (height : ℕ → ℝ) (bucket : ℕ → ℕ) (k : ℕ),
      dynamicZeroPacketAtStep S0 height bucket k ⊆
        nontrivialZerosFinset (height (k + 1)))

#check
  (dynamicZeroPacketExpansionState_subset_height :
    ∀ {S0 : Finset ℂ} {height : ℕ → ℝ} {bucket : ℕ → ℕ},
      Monotone height →
      S0 ⊆ nontrivialZerosFinset (height 0) →
      ∀ k,
        dynamicZeroPacketExpansionState S0 height bucket k ⊆
          nontrivialZerosFinset (height k))

#check
  (dynamicZeroPacketExpansionState_mono :
    ∀ (S0 : Finset ℂ) (height : ℕ → ℝ) (bucket : ℕ → ℕ),
      Monotone (dynamicZeroPacketExpansionState S0 height bucket))

#check
  (dynamicZeroPacketAtStep_pairwise_disjoint :
    ∀ (S0 : Finset ℂ) (height : ℕ → ℝ) (bucket : ℕ → ℕ)
      {i j : ℕ},
      i < j →
      Disjoint
        (dynamicZeroPacketAtStep S0 height bucket i)
        (dynamicZeroPacketAtStep S0 height bucket j))

#check
  (card_dynamicZeroPacketExpansionState :
    ∀ (S0 : Finset ℂ) (height : ℕ → ℝ) (bucket : ℕ → ℕ) (k : ℕ),
      (dynamicZeroPacketExpansionState S0 height bucket k).card =
        S0.card +
          ∑ i ∈ Finset.range k,
            (dynamicZeroPacketAtStep S0 height bucket i).card)

#check
  (card_add_steps_le_dynamicZeroPacketExpansionState_of_nonempty :
    ∀ {S0 : Finset ℂ} {height : ℕ → ℝ} {bucket : ℕ → ℕ} {k : ℕ},
      (∀ i < k,
        (dynamicZeroPacketAtStep S0 height bucket i).Nonempty) →
      S0.card + k ≤
        (dynamicZeroPacketExpansionState S0 height bucket k).card)

#check
  (card_add_steps_le_nontrivialZerosFinset_of_nonempty :
    ∀ {S0 : Finset ℂ} {height : ℕ → ℝ} {bucket : ℕ → ℕ} {k : ℕ},
      Monotone height →
      S0 ⊆ nontrivialZerosFinset (height 0) →
      (∀ i < k,
        (dynamicZeroPacketAtStep S0 height bucket i).Nonempty) →
      S0.card + k ≤ (nontrivialZerosFinset (height k)).card)
