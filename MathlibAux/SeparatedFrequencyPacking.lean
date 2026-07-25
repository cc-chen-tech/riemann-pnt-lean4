import Mathlib

namespace MathlibAux

/-- A finite `Δ`-separated subset of a radius-`r` interval has at most
`1 + 2r / Δ` points, in multiplication form. -/
theorem card_sub_one_mul_separation_le_two_mul_radius
    (S : Finset ℝ) (Δ ξ r : ℝ)
    (_hΔ : 0 < Δ) (hr : 0 ≤ r)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Δ ≤ |x - y|)
    (hball : ∀ x ∈ S, |x - ξ| ≤ r) :
    (((S.card - 1 : ℕ) : ℝ) * Δ) ≤ 2 * r := by
  classical
  by_cases hc : S.card ≤ 1
  · have hsub : S.card - 1 = 0 := Nat.sub_eq_zero_of_le hc
    simp [hsub, hr]
  let L := S.sort (· ≤ ·)
  let f : ℕ → ℝ := fun k ↦ L.getD k 0
  have hlength : L.length = S.card := Finset.length_sort (· ≤ ·)
  have hpair : L.Pairwise (· ≤ ·) := Finset.pairwise_sort S (· ≤ ·)
  have hnodup : L.Nodup := Finset.sort_nodup S (· ≤ ·)
  have hmem (k : ℕ) (hk : k < L.length) : L.get ⟨k, hk⟩ ∈ S := by
    rw [← Finset.mem_sort (· ≤ ·)]
    exact List.get_mem L ⟨k, hk⟩
  have hf (k : ℕ) (hk : k < L.length) :
      f k = L.get ⟨k, hk⟩ := by
    exact List.getD_eq_get L 0 ⟨k, hk⟩
  have hgap (k : ℕ) (hk : k ∈ Finset.range (S.card - 1)) :
      Δ ≤ f (k + 1) - f k := by
    have hklt : k < S.card - 1 := Finset.mem_range.mp hk
    have hkL : k < L.length := by
      rw [hlength]
      omega
    have hsuccL : k + 1 < L.length := by
      rw [hlength]
      omega
    have hle :
        L.get ⟨k, hkL⟩ ≤ L.get ⟨k + 1, hsuccL⟩ :=
      hpair.rel_get_of_le
        (show (⟨k, hkL⟩ : Fin L.length) ≤ ⟨k + 1, hsuccL⟩ by
          exact Nat.le_succ k)
    have hne : L.get ⟨k, hkL⟩ ≠ L.get ⟨k + 1, hsuccL⟩ := by
      intro heq
      have hindex :
          (⟨k, hkL⟩ : Fin L.length) = ⟨k + 1, hsuccL⟩ :=
        hnodup.injective_get heq
      have : k = k + 1 := Fin.ext_iff.mp hindex
      omega
    have hsep' :=
      hsep (L.get ⟨k, hkL⟩) (hmem k hkL)
        (L.get ⟨k + 1, hsuccL⟩) (hmem (k + 1) hsuccL) hne
    rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hsep'
    rw [hf k hkL, hf (k + 1) hsuccL]
    linarith
  have hsum :
      (((S.card - 1 : ℕ) : ℝ) * Δ) ≤
        ∑ k ∈ Finset.range (S.card - 1), (f (k + 1) - f k) := by
    calc
      (((S.card - 1 : ℕ) : ℝ) * Δ) =
          ∑ _k ∈ Finset.range (S.card - 1), Δ := by simp
      _ ≤ ∑ k ∈ Finset.range (S.card - 1), (f (k + 1) - f k) :=
        Finset.sum_le_sum fun k hk ↦ hgap k hk
  have htel :
      (∑ k ∈ Finset.range (S.card - 1), (f (k + 1) - f k)) =
        f (S.card - 1) - f 0 :=
    Finset.sum_range_sub f (S.card - 1)
  have hcard : 1 < S.card := Nat.lt_of_not_ge hc
  have hzeroL : 0 < L.length := by
    rw [hlength]
    omega
  have hlastL : S.card - 1 < L.length := by
    rw [hlength]
    omega
  have hboxZero : |f 0 - ξ| ≤ r := by
    rw [hf 0 hzeroL]
    exact hball (L.get ⟨0, hzeroL⟩) (hmem 0 hzeroL)
  have hboxLast : |f (S.card - 1) - ξ| ≤ r := by
    rw [hf (S.card - 1) hlastL]
    exact hball (L.get ⟨S.card - 1, hlastL⟩)
      (hmem (S.card - 1) hlastL)
  rw [htel] at hsum
  have hzeroBounds := abs_le.mp hboxZero
  have hlastBounds := abs_le.mp hboxLast
  linarith

end MathlibAux
