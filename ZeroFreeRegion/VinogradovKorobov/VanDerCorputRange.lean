import ZeroFreeRegion.VinogradovKorobov.VanDerCorput

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- Reindex `[1, N]` by the zero-based range of length `N`. -/
lemma sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n =
      ∑ k ∈ Finset.range N, f (k + 1) := by
  rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega]
  simpa [Nat.add_comm] using Finset.sum_Ico_eq_sum_range f 1 (N + 1)

/-- Zero-based, unit-step form of van der Corput's fundamental inequality. -/
theorem vanDerCorputRangeInequality (u : ℕ → ℂ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N) :
    (L : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, u n‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + ((L : ℝ) - 1)) *
          ∑ n ∈ Finset.range N, ‖u n‖ ^ 2
      + 2 * ((N : ℝ) + ((L : ℝ) - 1)) *
        ∑ ell ∈ Finset.Icc 1 (L - 1), ((L : ℝ) - (ell : ℝ)) *
          (∑ n ∈ Finset.range (N - ell),
            u n * (starRingEnd ℂ) (u (n + ell))).re := by
  let v : ℕ → ℂ := fun n ↦ u (n - 1)
  have h := vanDerCorputFundamentalInequality 1 N (by omega) v L
    (by simpa using hL) (by simpa using hLN)
  have hsum : ∑ n ∈ Finset.Icc 1 N, v n =
      ∑ n ∈ Finset.range N, u n := by
    rw [sum_Icc_one_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [v, Nat.add_sub_cancel]
  have hdiag : ∑ n ∈ Finset.Icc 1 N, ‖v n‖ ^ 2 =
      ∑ n ∈ Finset.range N, ‖u n‖ ^ 2 := by
    rw [sum_Icc_one_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [v, Nat.add_sub_cancel]
  have hcorr : ∀ ell : ℕ,
      (∑ n ∈ Finset.Icc 1 (N - ell),
          v n * (starRingEnd ℂ) (v (n + ell))) =
        ∑ n ∈ Finset.range (N - ell),
          u n * (starRingEnd ℂ) (u (n + ell)) := by
    intro ell
    rw [sum_Icc_one_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [v, Nat.add_sub_cancel]
    congr 3
    omega
  have houter :
      (∑ ell ∈ Finset.Icc 1 (L - 1), ((L : ℝ) - (ell : ℝ)) *
          (∑ n ∈ Finset.Icc 1 (N - ell),
            v n * (starRingEnd ℂ) (v (n + ell))).re) =
        ∑ ell ∈ Finset.Icc 1 (L - 1), ((L : ℝ) - (ell : ℝ)) *
          (∑ n ∈ Finset.range (N - ell),
            u n * (starRingEnd ℂ) (u (n + ell))).re := by
    apply Finset.sum_congr rfl
    intro ell hell
    rw [hcorr ell]
  rw [hsum, hdiag] at h
  simp only [Nat.cast_one, one_mul] at h
  rw [houter] at h
  exact h

/-- Van der Corput with abstract quantitative bounds for every autocorrelation
sum. -/
theorem vanDerCorputRangeOfCorrelationBounds
    (u : ℕ → ℂ) (B : ℕ → ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hcor : ∀ ell ∈ Finset.Icc 1 (L - 1),
      ‖∑ n ∈ Finset.range (N - ell),
        u n * (starRingEnd ℂ) (u (n + ell))‖ ≤ B ell) :
    (L : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, u n‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + ((L : ℝ) - 1)) *
          ∑ n ∈ Finset.range N, ‖u n‖ ^ 2
      + 2 * ((N : ℝ) + ((L : ℝ) - 1)) *
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * B ell := by
  have h := vanDerCorputRangeInequality u N L hL hLN
  refine h.trans ?_
  have hsum :
      (∑ ell ∈ Finset.Icc 1 (L - 1), ((L : ℝ) - (ell : ℝ)) *
          (∑ n ∈ Finset.range (N - ell),
            u n * (starRingEnd ℂ) (u (n + ell))).re) ≤
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * B ell := by
    apply Finset.sum_le_sum
    intro ell hell
    rw [Finset.mem_Icc] at hell
    apply mul_le_mul_of_nonneg_left _
    · have hellL : ell ≤ L := hell.2.trans (Nat.sub_le L 1)
      have hellLr : (ell : ℝ) ≤ (L : ℝ) := by exact_mod_cast hellL
      linarith
    · exact (Complex.re_le_norm _).trans (hcor ell (by simpa using hell))
  have hfactor : 0 ≤ 2 * ((N : ℝ) + ((L : ℝ) - 1)) := by
    apply mul_nonneg (by norm_num)
    exact add_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr (by exact_mod_cast hL))
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left hsum hfactor

end ZeroFreeRegion.VinogradovKorobov
