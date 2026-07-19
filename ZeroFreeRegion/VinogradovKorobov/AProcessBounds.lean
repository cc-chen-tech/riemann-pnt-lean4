import ZeroFreeRegion.VinogradovKorobov.IteratedDifference
import ZeroFreeRegion.VinogradovKorobov.Harmonic
import ZeroFreeRegion.VinogradovKorobov.PowerSum

namespace ZeroFreeRegion.VinogradovKorobov

/-- A uniform bound on A-process correlations controls their weighted sum. -/
lemma sum_aProcess_weights_le_sq_mul
    (B : ℕ → ℝ) (C : ℝ) (L : ℕ)
    (hC : 0 ≤ C)
    (hB : ∀ ell ∈ Finset.Icc 1 (L - 1), B ell ≤ C) :
    ∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * B ell ≤ (L : ℝ) ^ 2 * C := by
  have hsubset : Finset.Icc 1 (L - 1) ⊆ Finset.range L := by
    intro ell hell
    rcases Finset.mem_Icc.mp hell with ⟨hl, hu⟩
    exact Finset.mem_range.mpr (by omega)
  have hcard : (Finset.Icc 1 (L - 1)).card ≤ L := by
    simpa only [Finset.card_range] using Finset.card_le_card hsubset
  calc
    ∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * B ell ≤
        ∑ ell ∈ Finset.Icc 1 (L - 1), (L : ℝ) * C := by
      apply Finset.sum_le_sum
      intro ell hell
      have hu : ell ≤ L := by
        have h := (Finset.mem_Icc.mp hell).2
        omega
      have hweight : 0 ≤ (L : ℝ) - (ell : ℝ) := by
        exact sub_nonneg.mpr (by exact_mod_cast hu)
      calc
        ((L : ℝ) - (ell : ℝ)) * B ell ≤
            ((L : ℝ) - (ell : ℝ)) * C :=
          mul_le_mul_of_nonneg_left (hB ell hell) hweight
        _ ≤ (L : ℝ) * C := by
          exact mul_le_mul_of_nonneg_right
            (sub_le_self (L : ℝ) (Nat.cast_nonneg ell)) hC
    _ = ((Finset.Icc 1 (L - 1)).card : ℝ) * ((L : ℝ) * C) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (L : ℝ) * ((L : ℝ) * C) := by
      gcongr
    _ = (L : ℝ) ^ 2 * C := by ring

/-- Coarse normalized A-process estimate after replacing all correlations by
a single nonnegative bound `C`. -/
theorem aProcessSquaredBound_le
    (B : ℕ → ℝ) (C : ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N) (hC : 0 ≤ C)
    (hB0 : ∀ ell ∈ Finset.Icc 1 (L - 1), 0 ≤ B ell)
    (hB : ∀ ell ∈ Finset.Icc 1 (L - 1), B ell ≤ C) :
    aProcessSquaredBound B N L ≤
      2 * (N : ℝ) ^ 2 / L + 4 * (N : ℝ) * C := by
  have hLpos : 0 < (L : ℝ) := Nat.cast_pos.mpr (by omega)
  have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hspan :
      (N : ℝ) + ((L : ℝ) - 1) ≤ 2 * (N : ℝ) := by
    have hLNR : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast hLN
    linarith
  have hsum0 :
      0 ≤ ∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * B ell := by
    apply Finset.sum_nonneg
    intro ell hell
    have hu : ell ≤ L := by
      have h := (Finset.mem_Icc.mp hell).2
      omega
    exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hu)) (hB0 ell hell)
  have hsum := sum_aProcess_weights_le_sq_mul B C L hC hB
  unfold aProcessSquaredBound
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ hLpos.le
    calc
      ((N : ℝ) + ((L : ℝ) - 1)) * N ≤
          (2 * (N : ℝ)) * N :=
        mul_le_mul_of_nonneg_right hspan hNnonneg
      _ = 2 * (N : ℝ) ^ 2 := by ring
  · calc
      (2 * ((N : ℝ) + ((L : ℝ) - 1)) *
          ∑ ell ∈ Finset.Icc 1 (L - 1),
            ((L : ℝ) - (ell : ℝ)) * B ell) / (L : ℝ) ^ 2 ≤
          (2 * (2 * (N : ℝ)) * ((L : ℝ) ^ 2 * C)) /
            (L : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg (L : ℝ))
        gcongr
      _ = 4 * (N : ℝ) * C := by
        field_simp
        ring

/-- The one-step numerical A-process envelope is monotone in both the block
length and its nonnegative child bounds. -/
theorem aProcessSquaredBound_mono
    (B C : ℕ → ℝ) (N M L : ℕ)
    (hL : 1 ≤ L) (hNM : N ≤ M)
    (hB0 : ∀ ell ∈ Finset.Icc 1 (L - 1), 0 ≤ B ell)
    (hC0 : ∀ ell ∈ Finset.Icc 1 (L - 1), 0 ≤ C ell)
    (hBC : ∀ ell ∈ Finset.Icc 1 (L - 1), B ell ≤ C ell) :
    aProcessSquaredBound B N L ≤ aProcessSquaredBound C M L := by
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hNMreal : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hspanN : 0 ≤ (N : ℝ) + ((L : ℝ) - 1) := by
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hspanM : 0 ≤ (M : ℝ) + ((L : ℝ) - 1) := by
    have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hspan :
      (N : ℝ) + ((L : ℝ) - 1) ≤
        (M : ℝ) + ((L : ℝ) - 1) := by linarith
  have hsumB : 0 ≤ ∑ ell ∈ Finset.Icc 1 (L - 1),
      ((L : ℝ) - (ell : ℝ)) * B ell := by
    apply Finset.sum_nonneg
    intro ell hell
    have hellL : ell ≤ L := by
      have := (Finset.mem_Icc.mp hell).2
      omega
    exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hellL))
      (hB0 ell hell)
  have hsumC : 0 ≤ ∑ ell ∈ Finset.Icc 1 (L - 1),
      ((L : ℝ) - (ell : ℝ)) * C ell := by
    apply Finset.sum_nonneg
    intro ell hell
    have hellL : ell ≤ L := by
      have := (Finset.mem_Icc.mp hell).2
      omega
    exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hellL))
      (hC0 ell hell)
  have hsum :
      (∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * B ell) ≤
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * C ell := by
    apply Finset.sum_le_sum
    intro ell hell
    have hellL : ell ≤ L := by
      have := (Finset.mem_Icc.mp hell).2
      omega
    exact mul_le_mul_of_nonneg_left (hBC ell hell)
      (sub_nonneg.mpr (by exact_mod_cast hellL))
  unfold aProcessSquaredBound
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
    exact mul_le_mul hspan hNMreal (Nat.cast_nonneg N) hspanM
  · apply div_le_div_of_nonneg_right _ (sq_nonneg (L : ℝ))
    gcongr

/-- Weighted A-process sum when the correlations decay like `C / ell`. -/
lemma sum_aProcess_weights_reciprocal_le
    (B : ℕ → ℝ) (C : ℝ) (L : ℕ) (hC : 0 ≤ C)
    (hB : ∀ ell ∈ Finset.Icc 1 (L - 1),
      B ell ≤ C * (ell : ℝ)⁻¹) :
    ∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * B ell ≤
      C * ((L : ℝ) * (1 + Real.log L)) := by
  calc
    ∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * B ell ≤
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * (C * (ell : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro ell hell
      have hu : ell ≤ L := by
        have h := (Finset.mem_Icc.mp hell).2
        omega
      exact mul_le_mul_of_nonneg_left (hB ell hell)
        (sub_nonneg.mpr (by exact_mod_cast hu))
    _ = C * (∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * (ell : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell hell
      ring
    _ ≤ C * ((L : ℝ) * (1 + Real.log L)) :=
      mul_le_mul_of_nonneg_left (weighted_reciprocal_sum_le L) hC

/-- Refined normalized A-process estimate for reciprocal correlation decay. -/
theorem aProcessSquaredBound_le_reciprocal
    (B : ℕ → ℝ) (C : ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N) (hC : 0 ≤ C)
    (hB0 : ∀ ell ∈ Finset.Icc 1 (L - 1), 0 ≤ B ell)
    (hB : ∀ ell ∈ Finset.Icc 1 (L - 1),
      B ell ≤ C * (ell : ℝ)⁻¹) :
    aProcessSquaredBound B N L ≤
      2 * (N : ℝ) ^ 2 / L +
        4 * (N : ℝ) * C * (1 + Real.log L) / L := by
  have hLpos : 0 < (L : ℝ) := Nat.cast_pos.mpr (by omega)
  have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hspan :
      (N : ℝ) + ((L : ℝ) - 1) ≤ 2 * (N : ℝ) := by
    have hLNR : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast hLN
    linarith
  have hsum0 :
      0 ≤ ∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * B ell := by
    apply Finset.sum_nonneg
    intro ell hell
    have hu : ell ≤ L := by
      have h := (Finset.mem_Icc.mp hell).2
      omega
    exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hu)) (hB0 ell hell)
  have hsum := sum_aProcess_weights_reciprocal_le B C L hC hB
  unfold aProcessSquaredBound
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ hLpos.le
    calc
      ((N : ℝ) + ((L : ℝ) - 1)) * N ≤
          (2 * (N : ℝ)) * N :=
        mul_le_mul_of_nonneg_right hspan hNnonneg
      _ = 2 * (N : ℝ) ^ 2 := by ring
  · calc
      (2 * ((N : ℝ) + ((L : ℝ) - 1)) *
          ∑ ell ∈ Finset.Icc 1 (L - 1),
            ((L : ℝ) - (ell : ℝ)) * B ell) / (L : ℝ) ^ 2 ≤
          (2 * (2 * (N : ℝ)) *
            (C * ((L : ℝ) * (1 + Real.log L)))) /
            (L : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg (L : ℝ))
        gcongr
      _ = 4 * (N : ℝ) * C * (1 + Real.log L) / L := by
        field_simp
        ring

/-- One A-process step propagates a constant plus negative real-power child
bound, halving the accumulated-product decay exponent through the square
root. -/
theorem aProcessSquaredBound_le_sqrt_add_rpow
    (Q : ℕ → ℝ) (A D α : ℝ) (N L : ℕ)
    (hL : 2 ≤ L) (hLN : L ≤ N)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hα0 : 0 ≤ α) (hα2 : α < 2)
    (hQ : ∀ ell ∈ Finset.Icc 1 (L - 1),
      Q ell ≤ A + D * (ell : ℝ) ^ (-α)) :
    aProcessSquaredBound (fun ell ↦ Real.sqrt (Q ell)) N L ≤
      2 * (N : ℝ) ^ 2 / L +
        4 * (N : ℝ) *
          (Real.sqrt A * (L : ℝ) ^ 2 +
            Real.sqrt D * (L : ℝ) * finiteRpowSumEnvelope L (α / 2)) /
          (L : ℝ) ^ 2 := by
  have hαhalf0 : 0 ≤ α / 2 := by linarith
  have hαhalf1 : α / 2 < 1 := by linarith
  have hsqrtAdd : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
    intro x y hx hy
    apply (Real.sqrt_le_iff).2
    refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
    rw [add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
    nlinarith [mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  have hpoint : ∀ ell ∈ Finset.Icc 1 (L - 1),
      Real.sqrt (Q ell) ≤
        Real.sqrt A + Real.sqrt D * (ell : ℝ) ^ (-(α / 2)) := by
    intro ell hell
    have hell0 : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
    have hpow0 : 0 ≤ (ell : ℝ) ^ (-α) := Real.rpow_nonneg hell0 _
    calc
      Real.sqrt (Q ell) ≤ Real.sqrt (A + D * (ell : ℝ) ^ (-α)) :=
        Real.sqrt_le_sqrt (hQ ell hell)
      _ ≤ Real.sqrt A + Real.sqrt (D * (ell : ℝ) ^ (-α)) :=
        hsqrtAdd A (D * (ell : ℝ) ^ (-α)) hA (mul_nonneg hD hpow0)
      _ = Real.sqrt A + Real.sqrt D * (ell : ℝ) ^ (-(α / 2)) := by
        have hsqrtPow : Real.sqrt ((ell : ℝ) ^ (-α)) =
            (ell : ℝ) ^ (-(α / 2)) := by
          rw [Real.sqrt_eq_rpow,
            ← Real.rpow_mul hell0 (-α) (1 / 2 : ℝ)]
          congr 1
          ring
        rw [Real.sqrt_mul hD, hsqrtPow]
  have hweight :
      (∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ))) ≤ (L : ℝ) ^ 2 := by
    simpa only [mul_one, one_mul] using
      sum_aProcess_weights_le_sq_mul (fun _ ↦ 1) 1 L (by norm_num)
        (fun _ _ ↦ le_rfl)
  have hpower := weighted_rpow_neg_sum_le_envelope
    L (α / 2) hL hαhalf0 hαhalf1
  have hsum :
      (∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * Real.sqrt (Q ell)) ≤
        Real.sqrt A * (L : ℝ) ^ 2 +
          Real.sqrt D * (L : ℝ) * finiteRpowSumEnvelope L (α / 2) := by
    calc
      (∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * Real.sqrt (Q ell)) ≤
          ∑ ell ∈ Finset.Icc 1 (L - 1),
            ((L : ℝ) - (ell : ℝ)) *
              (Real.sqrt A + Real.sqrt D * (ell : ℝ) ^ (-(α / 2))) := by
        apply Finset.sum_le_sum
        intro ell hell
        have hellL : ell ≤ L := by
          have := (Finset.mem_Icc.mp hell).2
          omega
        exact mul_le_mul_of_nonneg_left (hpoint ell hell)
          (sub_nonneg.mpr (by exact_mod_cast hellL))
      _ = Real.sqrt A *
            (∑ ell ∈ Finset.Icc 1 (L - 1),
              ((L : ℝ) - (ell : ℝ))) +
          Real.sqrt D *
            (∑ ell ∈ Finset.Icc 1 (L - 1),
              ((L : ℝ) - (ell : ℝ)) *
                (ell : ℝ) ^ (-(α / 2))) := by
        calc
          (∑ ell ∈ Finset.Icc 1 (L - 1),
              ((L : ℝ) - (ell : ℝ)) *
                (Real.sqrt A +
                  Real.sqrt D * (ell : ℝ) ^ (-(α / 2)))) =
              ∑ ell ∈ Finset.Icc 1 (L - 1),
                (Real.sqrt A * ((L : ℝ) - (ell : ℝ)) +
                  Real.sqrt D * (((L : ℝ) - (ell : ℝ)) *
                    (ell : ℝ) ^ (-(α / 2)))) := by
            apply Finset.sum_congr rfl
            intro ell hell
            ring
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ Real.sqrt A * (L : ℝ) ^ 2 +
          Real.sqrt D *
            ((L : ℝ) * finiteRpowSumEnvelope L (α / 2)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hweight (Real.sqrt_nonneg _))
          (mul_le_mul_of_nonneg_left hpower (Real.sqrt_nonneg _))
      _ = Real.sqrt A * (L : ℝ) ^ 2 +
          Real.sqrt D * (L : ℝ) * finiteRpowSumEnvelope L (α / 2) := by
        ring
  have hLpos : 0 < (L : ℝ) := Nat.cast_pos.mpr (by omega)
  have hspan :
      (N : ℝ) + ((L : ℝ) - 1) ≤ 2 * (N : ℝ) := by
    have hLNR : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast hLN
    linarith
  have hsumNonneg : 0 ≤
      Real.sqrt A * (L : ℝ) ^ 2 +
        Real.sqrt D * (L : ℝ) * finiteRpowSumEnvelope L (α / 2) := by
    have henv := finiteRpowSumEnvelope_nonneg
      L (α / 2) hL hαhalf0 hαhalf1
    positivity
  have hsumActualNonneg : 0 ≤
      ∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * Real.sqrt (Q ell) := by
    apply Finset.sum_nonneg
    intro ell hell
    have hellL : ell ≤ L := by
      have := (Finset.mem_Icc.mp hell).2
      omega
    exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hellL))
      (Real.sqrt_nonneg _)
  unfold aProcessSquaredBound
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ hLpos.le
    calc
      ((N : ℝ) + ((L : ℝ) - 1)) * N ≤
          (2 * (N : ℝ)) * N :=
        mul_le_mul_of_nonneg_right hspan (Nat.cast_nonneg N)
      _ = 2 * (N : ℝ) ^ 2 := by ring
  · calc
      (2 * ((N : ℝ) + ((L : ℝ) - 1)) *
          ∑ ell ∈ Finset.Icc 1 (L - 1),
            ((L : ℝ) - (ell : ℝ)) * Real.sqrt (Q ell)) /
          (L : ℝ) ^ 2 ≤
        (2 * (2 * (N : ℝ)) *
          (Real.sqrt A * (L : ℝ) ^ 2 +
            Real.sqrt D * (L : ℝ) * finiteRpowSumEnvelope L (α / 2))) /
          (L : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg (L : ℝ))
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hspan (by norm_num)) hsum
          hsumActualNonneg (by positivity)
      _ = 4 * (N : ℝ) *
          (Real.sqrt A * (L : ℝ) ^ 2 +
            Real.sqrt D * (L : ℝ) * finiteRpowSumEnvelope L (α / 2)) /
          (L : ℝ) ^ 2 := by ring

/-- The reciprocal sum on the A-process shift range is bounded by the usual
harmonic majorant. -/
lemma reciprocal_sum_Icc_le_one_add_log (L : ℕ) :
    (∑ ell ∈ Finset.Icc 1 (L - 1), (ell : ℝ)⁻¹) ≤
      1 + Real.log L := by
  have hsubset : Finset.Icc 1 (L - 1) ⊆ Finset.Icc 1 L := by
    intro ell hell
    rcases Finset.mem_Icc.mp hell with ⟨hl, hu⟩
    exact Finset.mem_Icc.mpr ⟨hl, hu.trans (Nat.sub_le L 1)⟩
  have hextend :
      (∑ ell ∈ Finset.Icc 1 (L - 1), (ell : ℝ)⁻¹) ≤
        ∑ ell ∈ Finset.Icc 1 L, (ell : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro ell hell hnot
    positivity
  have hharmonic :
      (∑ ell ∈ Finset.Icc 1 L, (ell : ℝ)⁻¹) = (harmonic L : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  calc
    (∑ ell ∈ Finset.Icc 1 (L - 1), (ell : ℝ)⁻¹) ≤
        ∑ ell ∈ Finset.Icc 1 L, (ell : ℝ)⁻¹ := hextend
    _ = (harmonic L : ℝ) := hharmonic
    _ ≤ 1 + Real.log L := harmonic_le_one_add_log L

/-- Cauchy--Schwarz bound for the inverse-square-root weights produced by
the outer A-process. -/
theorem weighted_inv_sqrt_sum_le (L : ℕ) :
    (∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * (Real.sqrt ell)⁻¹) ≤
      Real.sqrt ((L : ℝ) ^ 3 * (1 + Real.log L)) := by
  let s := Finset.Icc 1 (L - 1)
  have hcard : s.card ≤ L := by
    have hsubset : s ⊆ Finset.range L := by
      intro ell hell
      rcases Finset.mem_Icc.mp hell with ⟨hl, hu⟩
      exact Finset.mem_range.mpr (by omega)
    simpa only [Finset.card_range] using Finset.card_le_card hsubset
  have hweightSq :
      (∑ ell ∈ s, ((L : ℝ) - (ell : ℝ)) ^ 2) ≤ (L : ℝ) ^ 3 := by
    calc
      (∑ ell ∈ s, ((L : ℝ) - (ell : ℝ)) ^ 2) ≤
          ∑ ell ∈ s, (L : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro ell hell
        have hu : ell ≤ L := by
          have h := (Finset.mem_Icc.mp hell).2
          omega
        have hw0 : 0 ≤ (L : ℝ) - (ell : ℝ) :=
          sub_nonneg.mpr (by exact_mod_cast hu)
        have hwL : (L : ℝ) - (ell : ℝ) ≤ L :=
          sub_le_self (L : ℝ) (Nat.cast_nonneg ell)
        nlinarith
      _ = (s.card : ℝ) * (L : ℝ) ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (L : ℝ) * (L : ℝ) ^ 2 := by
        gcongr
      _ = (L : ℝ) ^ 3 := by ring
  have hinvSqEq :
      (∑ ell ∈ s, ((Real.sqrt ell)⁻¹) ^ 2) =
        ∑ ell ∈ s, (ell : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro ell hell
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg ell)]
  have hinvSq :
      (∑ ell ∈ s, ((Real.sqrt ell)⁻¹) ^ 2) ≤
        1 + Real.log L := by
    rw [hinvSqEq]
    exact reciprocal_sum_Icc_le_one_add_log L
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun ell ↦ (L : ℝ) - (ell : ℝ))
    (fun ell ↦ (Real.sqrt ell)⁻¹)
  have hsq :
      (∑ ell ∈ s,
          ((L : ℝ) - (ell : ℝ)) * (Real.sqrt ell)⁻¹) ^ 2 ≤
        (L : ℝ) ^ 3 * (1 + Real.log L) := by
    exact hcs.trans (mul_le_mul hweightSq hinvSq
      (by positivity) (by positivity))
  exact Real.le_sqrt_of_sq_le hsq

private lemma sqrt_add_mul_inv_le
    {A D : ℝ} (ell : ℕ) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    Real.sqrt (A + D * (ell : ℝ)⁻¹) ≤
      Real.sqrt A + Real.sqrt D * (Real.sqrt ell)⁻¹ := by
  have hell0 : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hinv0 : 0 ≤ ((ell : ℝ)⁻¹) := inv_nonneg.mpr hell0
  have hB : 0 ≤ D * (ell : ℝ)⁻¹ := mul_nonneg hD hinv0
  have hsqrtMul :
      Real.sqrt (D * (ell : ℝ)⁻¹) =
        Real.sqrt D * (Real.sqrt ell)⁻¹ := by
    rw [Real.sqrt_mul hD, Real.sqrt_inv]
  rw [← hsqrtMul]
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB,
      mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg (D * (ell : ℝ)⁻¹))]

/-- Closed A-process estimate when the correlations are bounded by
`sqrt (A + D / ell)`. -/
theorem aProcessSquaredBound_le_sqrt_reciprocal
    (B : ℕ → ℝ) (A D : ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hB0 : ∀ ell ∈ Finset.Icc 1 (L - 1), 0 ≤ B ell)
    (hB : ∀ ell ∈ Finset.Icc 1 (L - 1),
      B ell ≤ Real.sqrt (A + D * (ell : ℝ)⁻¹)) :
    aProcessSquaredBound B N L ≤
      2 * (N : ℝ) ^ 2 / L +
        4 * (N : ℝ) *
          (Real.sqrt A * (L : ℝ) ^ 2 +
            Real.sqrt D *
              Real.sqrt ((L : ℝ) ^ 3 * (1 + Real.log L))) /
          (L : ℝ) ^ 2 := by
  have hLpos : 0 < (L : ℝ) := Nat.cast_pos.mpr (by omega)
  have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hspan :
      (N : ℝ) + ((L : ℝ) - 1) ≤ 2 * (N : ℝ) := by
    have hLNR : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast hLN
    linarith
  have hsum0 :
      0 ≤ ∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * B ell := by
    apply Finset.sum_nonneg
    intro ell hell
    have hu : ell ≤ L := by
      have h := (Finset.mem_Icc.mp hell).2
      omega
    exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hu)) (hB0 ell hell)
  have hweight :
      (∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ))) ≤ (L : ℝ) ^ 2 := by
    simpa only [mul_one] using
      sum_aProcess_weights_le_sq_mul (fun _ ↦ 1) 1 L (by norm_num)
        (by intro ell hell; exact le_rfl)
  have hsqrtWeight := weighted_inv_sqrt_sum_le L
  have hsum :
      (∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * B ell) ≤
        Real.sqrt A * (L : ℝ) ^ 2 +
          Real.sqrt D *
            Real.sqrt ((L : ℝ) ^ 3 * (1 + Real.log L)) := by
    calc
      (∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * B ell) ≤
          ∑ ell ∈ Finset.Icc 1 (L - 1),
            ((L : ℝ) - (ell : ℝ)) *
              (Real.sqrt A + Real.sqrt D * (Real.sqrt ell)⁻¹) := by
        apply Finset.sum_le_sum
        intro ell hell
        have hu : ell ≤ L := by
          have h := (Finset.mem_Icc.mp hell).2
          omega
        apply mul_le_mul_of_nonneg_left _
          (sub_nonneg.mpr (by exact_mod_cast hu))
        exact (hB ell hell).trans (sqrt_add_mul_inv_le ell hA hD)
      _ = Real.sqrt A *
            (∑ ell ∈ Finset.Icc 1 (L - 1),
              ((L : ℝ) - (ell : ℝ))) +
          Real.sqrt D *
            (∑ ell ∈ Finset.Icc 1 (L - 1),
              ((L : ℝ) - (ell : ℝ)) * (Real.sqrt ell)⁻¹) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.sum_mul]
          ring
        · calc
            (∑ ell ∈ Finset.Icc 1 (L - 1),
                ((L : ℝ) - (ell : ℝ)) *
                  (Real.sqrt D * (Real.sqrt ell)⁻¹)) =
                ∑ ell ∈ Finset.Icc 1 (L - 1),
                  (((L : ℝ) - (ell : ℝ)) * (Real.sqrt ell)⁻¹) *
                    Real.sqrt D := by
              apply Finset.sum_congr rfl
              intro ell hell
              ring
            _ = (∑ ell ∈ Finset.Icc 1 (L - 1),
                  ((L : ℝ) - (ell : ℝ)) * (Real.sqrt ell)⁻¹) *
                    Real.sqrt D := by rw [Finset.sum_mul]
            _ = Real.sqrt D *
                (∑ ell ∈ Finset.Icc 1 (L - 1),
                  ((L : ℝ) - (ell : ℝ)) * (Real.sqrt ell)⁻¹) := by ring
      _ ≤ Real.sqrt A * (L : ℝ) ^ 2 +
          Real.sqrt D *
            Real.sqrt ((L : ℝ) ^ 3 * (1 + Real.log L)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hweight (Real.sqrt_nonneg A))
          (mul_le_mul_of_nonneg_left hsqrtWeight (Real.sqrt_nonneg D))
  unfold aProcessSquaredBound
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ hLpos.le
    calc
      ((N : ℝ) + ((L : ℝ) - 1)) * N ≤
          (2 * (N : ℝ)) * N :=
        mul_le_mul_of_nonneg_right hspan hNnonneg
      _ = 2 * (N : ℝ) ^ 2 := by ring
  · calc
      (2 * ((N : ℝ) + ((L : ℝ) - 1)) *
          ∑ ell ∈ Finset.Icc 1 (L - 1),
            ((L : ℝ) - (ell : ℝ)) * B ell) / (L : ℝ) ^ 2 ≤
          (2 * (2 * (N : ℝ)) *
            (Real.sqrt A * (L : ℝ) ^ 2 +
              Real.sqrt D *
                Real.sqrt ((L : ℝ) ^ 3 * (1 + Real.log L)))) /
            (L : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg (L : ℝ))
        gcongr
      _ = 4 * (N : ℝ) *
          (Real.sqrt A * (L : ℝ) ^ 2 +
            Real.sqrt D *
              Real.sqrt ((L : ℝ) ^ 3 * (1 + Real.log L))) /
          (L : ℝ) ^ 2 := by ring

end ZeroFreeRegion.VinogradovKorobov
