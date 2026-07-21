import HardyTheorem.SelbergShortCompleteRangeEnergy

open scoped BigOperators

namespace HardyTheorem

/-!
# Sign-safe decomposition of the varying Selberg harmonic kernel

The varying factor `H_(N / lcm(r,s)) / lcm(r,s)` cannot be bounded
termwise when the coefficients have signs.  The identity below instead
diagonalizes the entire quadratic form into divisor sums of squares.
-/

/-- The finite lcm-harmonic quadratic form is exactly the weighted sum of
the squared divisor sums of its coefficients.  In particular, this
rewriting preserves all cancellation among signed coefficients. -/
theorem sum_lcmHarmonic_quadratic_eq_divisorSquares
    (a : ℕ → ℝ) (M N : ℕ) :
    (∑ r ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 M,
        a r * a s *
          ((Nat.lcm r s : ℝ)⁻¹ *
            (harmonic (N / Nat.lcm r s) : ℝ))) =
      ∑ k ∈ Finset.Icc 1 N,
        (∑ r ∈ (Finset.Icc 1 M).filter (fun r => r ∣ k), a r) ^ 2 *
          (k : ℝ)⁻¹ := by
  classical
  let I := Finset.Icc 1 M
  let K := Finset.Icc 1 N
  have hkernel : ∀ r ∈ I, ∀ s ∈ I,
      (Nat.lcm r s : ℝ)⁻¹ *
          (harmonic (N / Nat.lcm r s) : ℝ) =
        ∑ k ∈ K.filter (fun k => Nat.lcm r s ∣ k), (k : ℝ)⁻¹ := by
    intro r hr s hs
    have hrPos : 0 < r := (Finset.mem_Icc.mp hr).1
    have hsPos : 0 < s := (Finset.mem_Icc.mp hs).1
    have hlcmPos : 0 < Nat.lcm r s := Nat.lcm_pos hrPos hsPos
    simpa only [I, K, selbergShortLcmHarmonicKernel] using
      (selbergShortLcmHarmonicKernel_one_eq_inv_mul_harmonic
        (N := N) hlcmPos).symm
  have hinner : ∀ k ∈ K,
      (∑ r ∈ I, ∑ s ∈ I,
          if Nat.lcm r s ∣ k then a r * a s else 0) =
        (∑ r ∈ I.filter (fun r => r ∣ k), a r) ^ 2 := by
    intro k _hk
    calc
      (∑ r ∈ I, ∑ s ∈ I,
          if Nat.lcm r s ∣ k then a r * a s else 0) =
          ∑ r ∈ I, ∑ s ∈ I,
            if r ∣ k ∧ s ∣ k then a r * a s else 0 := by
        apply Finset.sum_congr rfl
        intro r _hr
        apply Finset.sum_congr rfl
        intro s _hs
        simp only [Nat.lcm_dvd_iff]
      _ = ∑ r ∈ I.filter (fun r => r ∣ k),
            ∑ s ∈ I.filter (fun s => s ∣ k), a r * a s := by
        simp_rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro r _hr
        by_cases hrk : r ∣ k
        · simp [hrk]
        · simp [hrk]
      _ = (∑ r ∈ I.filter (fun r => r ∣ k), a r) *
            (∑ s ∈ I.filter (fun s => s ∣ k), a s) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r _hr
        rw [Finset.mul_sum]
      _ = (∑ r ∈ I.filter (fun r => r ∣ k), a r) ^ 2 := by
        rw [pow_two]
  change (∑ r ∈ I, ∑ s ∈ I,
      a r * a s *
        ((Nat.lcm r s : ℝ)⁻¹ *
          (harmonic (N / Nat.lcm r s) : ℝ))) = _
  calc
    (∑ r ∈ I, ∑ s ∈ I,
        a r * a s *
          ((Nat.lcm r s : ℝ)⁻¹ *
            (harmonic (N / Nat.lcm r s) : ℝ))) =
        ∑ r ∈ I, ∑ s ∈ I,
          a r * a s *
            ∑ k ∈ K.filter (fun k => Nat.lcm r s ∣ k),
              (k : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      rw [hkernel r hr s hs]
    _ = ∑ r ∈ I, ∑ s ∈ I, ∑ k ∈ K,
          if Nat.lcm r s ∣ k then a r * a s * (k : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro r _hr
      apply Finset.sum_congr rfl
      intro s _hs
      rw [Finset.mul_sum, Finset.sum_filter]
    _ = ∑ k ∈ K, ∑ r ∈ I, ∑ s ∈ I,
          if Nat.lcm r s ∣ k then a r * a s * (k : ℝ)⁻¹ else 0 := by
      calc
        (∑ r ∈ I, ∑ s ∈ I, ∑ k ∈ K,
            if Nat.lcm r s ∣ k then a r * a s * (k : ℝ)⁻¹ else 0) =
            ∑ r ∈ I, ∑ k ∈ K, ∑ s ∈ I,
              if Nat.lcm r s ∣ k then a r * a s * (k : ℝ)⁻¹ else 0 := by
          apply Finset.sum_congr rfl
          intro r _hr
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = ∑ k ∈ K,
          (∑ r ∈ I, ∑ s ∈ I,
            if Nat.lcm r s ∣ k then a r * a s else 0) *
              (k : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _hs
      split_ifs <;> ring
    _ = ∑ k ∈ K,
          (∑ r ∈ I.filter (fun r => r ∣ k), a r) ^ 2 *
            (k : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hinner k hk]
    _ = _ := by
      rfl

/-- The varying lcm-harmonic kernel is positive semidefinite on every finite
positive box. -/
theorem sum_lcmHarmonic_quadratic_nonneg
    (a : ℕ → ℝ) (M N : ℕ) :
    0 ≤ ∑ r ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 M,
      a r * a s *
        ((Nat.lcm r s : ℝ)⁻¹ *
          (harmonic (N / Nat.lcm r s) : ℝ)) := by
  rw [sum_lcmHarmonic_quadratic_eq_divisorSquares]
  apply Finset.sum_nonneg
  intro k _hk
  exact mul_nonneg (sq_nonneg _) (by positivity)

/-- For the actual Selberg coefficients, the complete energy is the weighted
square of their divisor sums.  This is the sign-safe form in which the sharp
Möbius cancellation estimate must be proved. -/
theorem sum_normSq_selbergShortDirichletCollectedCoeff_completeRange_eq_divisorSquares
    {N X : ℕ} (hX : 2 ≤ X) :
    (∑ k ∈ Finset.Icc 1 N,
        Complex.normSq (selbergShortDirichletCollectedCoeff N X k)) =
      ∑ k ∈ Finset.Icc 1 N,
        (∑ r ∈ (Finset.Icc 1 ((X - 1) * (X - 1))).filter
            (fun r => r ∣ k),
          selbergShortDoubleMoebiusCoeff X r) ^ 2 * (k : ℝ)⁻¹ := by
  rw [sum_normSq_selbergShortDirichletCollectedCoeff_completeRange_eq_effectiveDoubleLcmHarmonic
    hX]
  exact sum_lcmHarmonic_quadratic_eq_divisorSquares
    (selbergShortDoubleMoebiusCoeff X) ((X - 1) * (X - 1)) N

end HardyTheorem
