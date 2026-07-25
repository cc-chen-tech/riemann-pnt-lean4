import ZeroFreeRegion.VinogradovKorobov.FordNearInteger

open ZeroFreeRegion.VinogradovKorobov

#check fordNearIntegerSet
#check mem_fordNearIntegerSet
#check card_fordNearIntegerSet_le
#check card_fordNearIntegerSet_le_scaled

example (K : ℕ) (γ δ : ℝ) (hγ : 0 < γ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) :
    ((fordNearIntegerSet K γ δ).card : ℝ) ≤
      4 * (K : ℝ) * δ + 2 * (K : ℝ) * γ + 4 * δ / γ + 2 :=
  card_fordNearIntegerSet_le K γ δ hγ hδ0 hδ

example (K A B : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hA : 1 ≤ A) (hK : K ≤ B) :
    ((fordNearIntegerSet K γ (1 / (2 * (A : ℝ)))).card : ℝ) ≤
      2 * (B : ℝ) / A + 2 * (B : ℝ) * γ +
        2 / ((A : ℝ) * γ) + 2 :=
  card_fordNearIntegerSet_le_scaled K A B γ hγ hA hK
