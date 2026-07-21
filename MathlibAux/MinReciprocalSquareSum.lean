import MathlibAux.DyadicHarmonic

open scoped BigOperators

namespace MathlibAux

/-- A uniform reciprocal-square bound for a truncated minimum.  Splitting at
`floor (B / delta)` removes any dependence on the outer cutoff `K`. -/
theorem sum_sq_min_div_le (K : ℕ) {delta B : ℝ}
    (hdelta : 0 < delta) (hB : 0 ≤ B) :
    (∑ j ∈ Finset.Icc 1 K, (min delta (B / j)) ^ 2) ≤
      3 * B * delta := by
  by_cases hsmall : B < delta
  · have hpoint : ∀ j ∈ Finset.Icc 1 K,
        (min delta (B / j)) ^ 2 ≤
          B ^ 2 * (((j : ℝ) ^ 2)⁻¹) := by
      intro j hj
      have hj_one : (1 : ℝ) ≤ j := by
        exact_mod_cast (Finset.mem_Icc.mp hj).1
      have hj_pos : 0 < (j : ℝ) := zero_lt_one.trans_le hj_one
      have hdiv_le : B / (j : ℝ) ≤ delta :=
        (div_le_self hB hj_one).trans hsmall.le
      rw [min_eq_right hdiv_le, div_pow, div_eq_mul_inv]
    calc
      (∑ j ∈ Finset.Icc 1 K, (min delta (B / j)) ^ 2) ≤
          ∑ j ∈ Finset.Icc 1 K,
            B ^ 2 * (((j : ℝ) ^ 2)⁻¹) :=
        Finset.sum_le_sum hpoint
      _ = B ^ 2 *
          ∑ j ∈ Finset.Icc 1 K, (((j : ℝ) ^ 2)⁻¹) := by
        rw [Finset.mul_sum]
      _ ≤ B ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left
          (sum_inv_sq_Icc_one_le_two K) (sq_nonneg B)
      _ ≤ 3 * B * delta := by
        nlinarith [mul_nonneg hB hdelta.le]
  · have hlarge : delta ≤ B := le_of_not_gt hsmall
    let L := Nat.floor (B / delta)
    have hratio_nonneg : 0 ≤ B / delta := div_nonneg hB hdelta.le
    have hL : 1 ≤ L := by
      apply Nat.le_floor
      exact (le_div_iff₀ hdelta).2 (by simpa using hlarge)
    have hfloor : (L : ℝ) ≤ B / delta := by
      simpa only [L] using Nat.floor_le hratio_nonneg
    have hratio_lt : B / delta < (L : ℝ) + 1 := by
      simpa only [L, Nat.cast_add, Nat.cast_one] using
        Nat.lt_floor_add_one (B / delta)
    have hsplit :
        Finset.Icc 1 K =
          Finset.Icc 1 (min K L) ∪ Finset.Ioo L (K + 1) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioo,
        Nat.le_min, Nat.lt_add_one_iff]
      omega
    have hdisjoint :
        Disjoint (Finset.Icc 1 (min K L)) (Finset.Ioo L (K + 1)) := by
      refine Finset.disjoint_left.2 ?_
      intro j hjhead hjtail
      simp only [Finset.mem_Icc, Nat.le_min] at hjhead
      simp only [Finset.mem_Ioo] at hjtail
      omega
    have hhead_point : ∀ j ∈ Finset.Icc 1 (min K L),
        (min delta (B / j)) ^ 2 ≤ delta ^ 2 := by
      intro j hj
      have hj_one : (1 : ℝ) ≤ j := by
        exact_mod_cast (Finset.mem_Icc.mp hj).1
      have hdiv_nonneg : 0 ≤ B / (j : ℝ) :=
        div_nonneg hB (zero_le_one.trans hj_one)
      exact (sq_le_sq₀ (le_min hdelta.le hdiv_nonneg) hdelta.le).2
        (min_le_left _ _)
    have hhead :
        (∑ j ∈ Finset.Icc 1 (min K L),
          (min delta (B / j)) ^ 2) ≤ B * delta := by
      have hLdelta : (L : ℝ) * delta ≤ B :=
        (le_div_iff₀ hdelta).1 hfloor
      calc
        (∑ j ∈ Finset.Icc 1 (min K L),
            (min delta (B / j)) ^ 2) ≤
            ∑ _j ∈ Finset.Icc 1 (min K L), delta ^ 2 :=
          Finset.sum_le_sum hhead_point
        _ = (min K L : ℕ) * delta ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          simp
        _ ≤ (L : ℝ) * delta ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast min_le_right K L) (sq_nonneg delta)
        _ ≤ B * delta := by
          nlinarith [mul_nonneg hdelta.le hdelta.le]
    have htail_point : ∀ j ∈ Finset.Ioo L (K + 1),
        (min delta (B / j)) ^ 2 ≤
          B ^ 2 * (((j : ℝ) ^ 2)⁻¹) := by
      intro j hj
      have hj_pos : 0 < (j : ℝ) := by
        have hj_pos_nat : 0 < j :=
          Nat.zero_lt_of_lt (hL.trans_lt (Finset.mem_Ioo.mp hj).1)
        exact_mod_cast hj_pos_nat
      have hdiv_nonneg : 0 ≤ B / (j : ℝ) := div_nonneg hB hj_pos.le
      calc
        (min delta (B / j)) ^ 2 ≤ (B / j) ^ 2 :=
          (sq_le_sq₀ (le_min hdelta.le hdiv_nonneg) hdiv_nonneg).2
            (min_le_right _ _)
        _ = B ^ 2 * (((j : ℝ) ^ 2)⁻¹) := by
          rw [div_pow, div_eq_mul_inv]
    have hinv_tail :
        (∑ j ∈ Finset.Ioo L (K + 1), (((j : ℝ) ^ 2)⁻¹)) ≤
          2 / ((L : ℝ) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (sum_Ioo_inv_sq_le (α := ℝ) L (K + 1))
    have hden_pos : 0 < (L : ℝ) + 1 := by positivity
    have hB_div_le : B / ((L : ℝ) + 1) ≤ delta := by
      apply (div_le_iff₀ hden_pos).2
      have hB_lt : B < ((L : ℝ) + 1) * delta :=
        (div_lt_iff₀ hdelta).1 hratio_lt
      simpa only [mul_comm] using hB_lt.le
    have htail :
        (∑ j ∈ Finset.Ioo L (K + 1),
          (min delta (B / j)) ^ 2) ≤ 2 * B * delta := by
      calc
        (∑ j ∈ Finset.Ioo L (K + 1),
            (min delta (B / j)) ^ 2) ≤
            ∑ j ∈ Finset.Ioo L (K + 1),
              B ^ 2 * (((j : ℝ) ^ 2)⁻¹) :=
          Finset.sum_le_sum htail_point
        _ = B ^ 2 *
            ∑ j ∈ Finset.Ioo L (K + 1), (((j : ℝ) ^ 2)⁻¹) := by
          rw [Finset.mul_sum]
        _ ≤ B ^ 2 * (2 / ((L : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hinv_tail (sq_nonneg B)
        _ = 2 * B * (B / ((L : ℝ) + 1)) := by
          field_simp
        _ ≤ 2 * B * delta :=
          mul_le_mul_of_nonneg_left hB_div_le (mul_nonneg (by norm_num) hB)
    rw [hsplit, Finset.sum_union hdisjoint]
    calc
      (∑ j ∈ Finset.Icc 1 (min K L), (min delta (B / j)) ^ 2) +
          ∑ j ∈ Finset.Ioo L (K + 1), (min delta (B / j)) ^ 2 ≤
          B * delta + 2 * B * delta := add_le_add hhead htail
      _ = 3 * B * delta := by ring

end MathlibAux
