import HardyTheorem.SelbergOffDiagonalArithmetic

namespace HardyTheorem

/-! # Exact residue-class reindexing in Selberg's off-diagonal sum. -/

def selbergPositiveGapCount (K d : ℕ) : ℕ := (K - 1) / d

def selbergPositiveGapResidue (K d : ℕ) : ℕ :=
  K - selbergPositiveGapCount K d * d

noncomputable def selbergPositiveGapReciprocalSum (K d : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (selbergPositiveGapCount K d),
    ((K - n * d : ℕ) : ℝ)⁻¹

noncomputable def selbergPositiveGapResidueSum (K d : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (selbergPositiveGapCount K d),
    ((selbergPositiveGapResidue K d + j * d : ℕ) : ℝ)⁻¹

theorem selberg_positive_gap_admissible_iff
    {K d n : ℕ} (hd : 1 ≤ d) :
    1 ≤ n ∧ n * d < K ↔ n ∈ Finset.Icc 1 (selbergPositiveGapCount K d) := by
  constructor
  · rintro ⟨hn, hgap⟩
    apply Finset.mem_Icc.mpr
    refine ⟨hn, ?_⟩
    unfold selbergPositiveGapCount
    exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  · intro hmem
    obtain ⟨hn, hnN⟩ := Finset.mem_Icc.mp hmem
    refine ⟨hn, ?_⟩
    unfold selbergPositiveGapCount at hnN
    have hmul := (Nat.le_div_iff_mul_le (by omega)).1 hnN
    have hmul' : n * d ≤ K - 1 := by simpa [mul_comm] using hmul
    have hprod0 : 0 < n * d := Nat.mul_pos (by omega) (by omega)
    have hK0 : 0 < K :=
      lt_of_lt_of_le hprod0 (hmul'.trans (Nat.sub_le K 1))
    exact hmul'.trans_lt (Nat.sub_lt hK0 (by omega))

theorem selberg_positive_gap_residue_bounds
    {K d : ℕ} (hK : 1 ≤ K) (hd : 1 ≤ d) :
    1 ≤ selbergPositiveGapResidue K d ∧
      selbergPositiveGapResidue K d ≤ d := by
  unfold selbergPositiveGapResidue selbergPositiveGapCount
  have hmul := Nat.div_mul_le_self (K - 1) d
  have hmod := Nat.mod_lt (K - 1) (by omega : 0 < d)
  have hdecomp := Nat.mod_add_div (K - 1) d
  have hsum : (K - 1) / d * d + ((K - 1) % d + 1) = K := by
    calc
      (K - 1) / d * d + ((K - 1) % d + 1) =
          (K - 1) % d + d * ((K - 1) / d) + 1 := by ring
      _ = (K - 1) + 1 := by rw [hdecomp]
      _ = K := Nat.sub_add_cancel hK
  omega

theorem selberg_positive_gap_reindex_identity
    {K d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hgap : n * d < K) :
    K - n * d = selbergPositiveGapResidue K d +
      (selbergPositiveGapCount K d - n) * d := by
  have hnN : n ≤ selbergPositiveGapCount K d :=
    Finset.mem_Icc.mp
      ((selberg_positive_gap_admissible_iff hd).mp ⟨hn, hgap⟩) |>.2
  have hNd : selbergPositiveGapCount K d * d ≤ K := by
    unfold selbergPositiveGapCount
    exact (Nat.div_mul_le_self (K - 1) d).trans (Nat.sub_le K 1)
  have hnd : n * d ≤ selbergPositiveGapCount K d * d :=
    Nat.mul_le_mul_right d hnN
  unfold selbergPositiveGapResidue
  rw [Nat.sub_mul]
  exact (tsub_add_tsub_cancel hNd hnd).symm

theorem selberg_positive_gap_sum_reindex
    {K d : ℕ} (hd : 1 ≤ d) :
    selbergPositiveGapReciprocalSum K d =
      selbergPositiveGapResidueSum K d := by
  classical
  let N := selbergPositiveGapCount K d
  unfold selbergPositiveGapReciprocalSum selbergPositiveGapResidueSum
  change (∑ n ∈ Finset.Icc 1 N, ((K - n * d : ℕ) : ℝ)⁻¹) =
    ∑ j ∈ Finset.range N,
      ((selbergPositiveGapResidue K d + j * d : ℕ) : ℝ)⁻¹
  refine Finset.sum_bij (fun n _hn => N - n) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_range]
    have hn' := Finset.mem_Icc.mp hn
    omega
  · intro n₁ hn₁ n₂ hn₂ heq
    have hn₁' := Finset.mem_Icc.mp hn₁
    have hn₂' := Finset.mem_Icc.mp hn₂
    omega
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    refine ⟨N - j, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr (by omega)
    · omega
  · intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hgap : n * d < K :=
      (selberg_positive_gap_admissible_iff hd).mpr hn |>.2
    rw [selberg_positive_gap_reindex_identity hd hn1 hgap]

theorem selberg_positive_gap_reciprocal_sum_le
    {K d : ℕ} (hK : 1 ≤ K) (hd : 1 ≤ d) :
    selbergPositiveGapReciprocalSum K d ≤
      1 + (d : ℝ)⁻¹ *
        (1 + Real.log (selbergPositiveGapCount K d : ℝ)) := by
  rw [selberg_positive_gap_sum_reindex hd]
  let N := selbergPositiveGapCount K d
  let r := selbergPositiveGapResidue K d
  change (∑ j ∈ Finset.range N, (((r + j * d : ℕ) : ℝ))⁻¹) ≤
    1 + (d : ℝ)⁻¹ * (1 + Real.log (N : ℝ))
  have hr := selberg_positive_gap_residue_bounds hK hd
  have hfirst : ((r : ℝ))⁻¹ ≤ 1 := by
    have hrReal : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.1
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hrReal
    norm_num at h
    exact h
  by_cases hN0 : N = 0
  · simp [hN0]
    positivity
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  by_cases hNone : N = 1
  · have hrhs : (1 : ℝ) ≤ 1 + (d : ℝ)⁻¹ :=
      le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg d))
    simpa [hNone] using hfirst.trans hrhs
  have hN2 : 2 ≤ N := by omega
  have hrange : Finset.range N =
      insert 0 (Finset.Icc 1 (N - 1)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have htail : (∑ j ∈ Finset.Icc 1 (N - 1),
      ((r : ℝ) + (j : ℝ) * (d : ℝ))⁻¹) ≤
      (d : ℝ)⁻¹ * (1 + Real.log ((N - 1 : ℕ) : ℝ)) := by
    simpa only [r, Nat.cast_add, Nat.cast_mul] using
      (selberg_arithmetic_progression_reciprocal_tail_le hr.1 hd (N - 1))
  have hlog : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (by omega : 0 < N - 1)
    · exact_mod_cast Nat.sub_le N 1
  have htailBound : (d : ℝ)⁻¹ *
      (1 + Real.log ((N - 1 : ℕ) : ℝ)) ≤
      (d : ℝ)⁻¹ * (1 + Real.log (N : ℝ)) :=
    mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hlog)
      (inv_nonneg.mpr (Nat.cast_nonneg d))
  rw [hrange, Finset.sum_insert (by simp)]
  simp only [zero_mul, add_zero, Nat.cast_add, Nat.cast_mul]
  exact (add_le_add hfirst htail).trans (add_le_add (le_refl 1) htailBound)

theorem selberg_positive_gap_count_le_mul_sq
    {m kappa lambda mu nu X : ℕ}
    (_hlambda : 1 ≤ lambda) (_hmu : 1 ≤ mu)
    (hkappaX : kappa ≤ X) (hnuX : nu ≤ X) :
    selbergPositiveGapCount (m * kappa * nu) (lambda * mu) ≤ m * X ^ 2 := by
  have hknu : kappa * nu ≤ X * X := Nat.mul_le_mul hkappaX hnuX
  calc
    selbergPositiveGapCount (m * kappa * nu) (lambda * mu) ≤
        m * kappa * nu - 1 := by
      unfold selbergPositiveGapCount
      exact Nat.div_le_self _ _
    _ ≤ m * kappa * nu := Nat.sub_le _ _
    _ ≤ m * (X * X) := by
      simpa [mul_assoc] using Nat.mul_le_mul_left m hknu
    _ = m * X ^ 2 := by ring

theorem selberg_log_positive_gap_count_le_two_log_mul
    {m kappa lambda mu nu X : ℕ}
    (hm : 1 ≤ m) (hlambda : 1 ≤ lambda) (hmu : 1 ≤ mu)
    (hkappaX : kappa ≤ X) (hnuX : nu ≤ X) (hX : 1 ≤ X) :
    Real.log (selbergPositiveGapCount (m * kappa * nu) (lambda * mu) : ℝ) ≤
      2 * Real.log ((m : ℝ) * (X : ℝ)) := by
  let N := selbergPositiveGapCount (m * kappa * nu) (lambda * mu)
  change Real.log (N : ℝ) ≤ 2 * Real.log ((m : ℝ) * (X : ℝ))
  have hNle : N ≤ m * X ^ 2 := by
    dsimp [N]
    exact selberg_positive_gap_count_le_mul_sq
      hlambda hmu hkappaX hnuX
  by_cases hN0 : N = 0
  · rw [hN0]
    simp only [Nat.cast_zero, Real.log_zero]
    have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hXReal : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith))
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hcast : (N : ℝ) ≤ (m : ℝ) * (X : ℝ) ^ 2 := by
    exact_mod_cast hNle
  calc
    Real.log (N : ℝ) ≤ Real.log ((m : ℝ) * (X : ℝ) ^ 2) :=
      Real.log_le_log hNpos hcast
    _ ≤ 2 * Real.log ((m : ℝ) * (X : ℝ)) := by
      have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hXReal : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      have hm0 : (0 : ℝ) < (m : ℝ) := zero_lt_one.trans_le hmReal
      have hX0 : (0 : ℝ) < (X : ℝ) := zero_lt_one.trans_le hXReal
      rw [Real.log_mul hm0.ne' (sq_pos_of_pos hX0).ne', Real.log_pow,
        Real.log_mul hm0.ne' hX0.ne']
      have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmReal
      norm_num at ⊢
      linarith

theorem selberg_log_mul_sq_le_two_log_mul
    {m X : ℝ} (hm : 1 ≤ m) (hX : 1 ≤ X) :
    Real.log (m * X ^ 2) ≤ 2 * Real.log (m * X) := by
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  rw [Real.log_mul hm0.ne' (sq_pos_of_pos hX0).ne', Real.log_pow,
    Real.log_mul hm0.ne' hX0.ne']
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  norm_num at ⊢
  linarith

end HardyTheorem
