import MathlibAux.MinReciprocalSquareSum

open scoped BigOperators

namespace MathlibAux

/-- Reindexing by distance to a right endpoint preserves the uniform
truncated reciprocal-square bound. -/
theorem sum_sq_min_div_nat_sub_left_le
    (s : Finset ℕ) (base : ℕ) {delta B : ℝ}
    (hdelta : 0 < delta) (hB : 0 ≤ B)
    (hleft : ∀ n ∈ s, n < base) :
    (∑ n ∈ s, (min delta (B / (base - n : ℕ))) ^ 2) ≤
      3 * B * delta := by
  let f : ℕ → ℝ := fun j => (min delta (B / (j : ℝ))) ^ 2
  have hinj : ∀ a ∈ s, ∀ b ∈ s, base - a = base - b → a = b := by
    intro a ha b hb hab
    have hal := hleft a ha
    have hbl := hleft b hb
    omega
  have himage : s.image (fun n => base - n) ⊆ Finset.Icc 1 base := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨n, hn, rfl⟩ := hj
    have hnl := hleft n hn
    simp only [Finset.mem_Icc]
    omega
  have hsum :
      (∑ n ∈ s, f (base - n)) =
        ∑ j ∈ s.image (fun n => base - n), f j := by
    exact (Finset.sum_image hinj).symm
  change (∑ n ∈ s, f (base - n)) ≤ 3 * B * delta
  rw [hsum]
  calc
    (∑ j ∈ s.image (fun n => base - n), f j) ≤
        ∑ j ∈ Finset.Icc 1 base, f j :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro j _hj _himage
        dsimp only [f]
        positivity)
    _ ≤ 3 * B * delta := sum_sq_min_div_le base hdelta hB

/-- Reindexing by distance from a left endpoint preserves the uniform
truncated reciprocal-square bound. -/
theorem sum_sq_min_div_nat_sub_right_le
    (s : Finset ℕ) (base N : ℕ) {delta B : ℝ}
    (hdelta : 0 < delta) (hB : 0 ≤ B)
    (hright : ∀ n ∈ s, base < n)
    (hupper : ∀ n ∈ s, n ≤ N) :
    (∑ n ∈ s, (min delta (B / (n - base : ℕ))) ^ 2) ≤
      3 * B * delta := by
  let f : ℕ → ℝ := fun j => (min delta (B / (j : ℝ))) ^ 2
  have hinj : ∀ a ∈ s, ∀ b ∈ s, a - base = b - base → a = b := by
    intro a ha b hb hab
    have har := hright a ha
    have hbr := hright b hb
    omega
  have himage : s.image (fun n => n - base) ⊆ Finset.Icc 1 N := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨n, hn, rfl⟩ := hj
    have hnr := hright n hn
    have hnN := hupper n hn
    simp only [Finset.mem_Icc]
    omega
  have hsum :
      (∑ n ∈ s, f (n - base)) =
        ∑ j ∈ s.image (fun n => n - base), f j := by
    exact (Finset.sum_image hinj).symm
  change (∑ n ∈ s, f (n - base)) ≤ 3 * B * delta
  rw [hsum]
  calc
    (∑ j ∈ s.image (fun n => n - base), f j) ≤
        ∑ j ∈ Finset.Icc 1 N, f j :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro j _hj _himage
        dsimp only [f]
        positivity)
    _ ≤ 3 * B * delta := sum_sq_min_div_le N hdelta hB

end MathlibAux
