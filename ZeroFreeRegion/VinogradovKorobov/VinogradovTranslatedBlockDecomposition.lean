import ZeroFreeRegion.VinogradovKorobov.VinogradovTranslatedBlockMoment
import ZeroFreeRegion.VinogradovKorobov.VinogradovFiniteConditioning
import Mathlib.Data.Fin.Embedding

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

private noncomputable def vinogradovTupleCastLEEmbedding
    {s X Y : ℕ} (hXY : X ≤ Y) :
    (Fin s → Fin X) ↪ (Fin s → Fin Y) :=
  Function.Embedding.piCongrRight fun _ ↦ Fin.castLEEmb hXY

/-- Modular Vinogradov solution counts are monotone in the interval length. -/
theorem vinogradovSolutionCountMod_mono_length
    (Q k s X Y : ℕ) (hXY : X ≤ Y) :
    vinogradovSolutionCountMod Q k s X ≤
      vinogradovSolutionCountMod Q k s Y := by
  classical
  let eTuple := vinogradovTupleCastLEEmbedding (s := s) hXY
  let ePair := Function.Embedding.prodMap eTuple eTuple
  have hsubset :
      (vinogradovSolutionPairSetMod Q k s X).map ePair ⊆
        vinogradovSolutionPairSetMod Q k s Y := by
    intro xy hxy
    rw [Finset.mem_map] at hxy
    obtain ⟨uv, huv, rfl⟩ := hxy
    rcases uv with ⟨x, y⟩
    rw [mem_vinogradovSolutionPairSetMod_iff] at huv ⊢
    intro j
    simpa [vinogradovPowerSumMod, ePair, eTuple,
      vinogradovTupleCastLEEmbedding] using huv j
  rw [← card_vinogradovSolutionPairSetMod Q k s X,
    ← card_vinogradovSolutionPairSetMod Q k s Y]
  calc
    (vinogradovSolutionPairSetMod Q k s X).card =
        ((vinogradovSolutionPairSetMod Q k s X).map ePair).card :=
      (Finset.card_map ePair).symm
    _ ≤ (vinogradovSolutionPairSetMod Q k s Y).card :=
      Finset.card_le_card hsubset

/-- The normalized translated moment is monotone in the interval length. -/
theorem norm_normalizedTranslatedVinogradovMomentMod_mono_length
    (Q m k s X Y : ℕ) [NeZero Q] (hXY : X ≤ Y) :
    ‖normalizedTranslatedVinogradovMomentMod Q m k s X‖ ≤
      ‖normalizedTranslatedVinogradovMomentMod Q m k s Y‖ := by
  rw [normalizedTranslatedVinogradovMomentMod_eq_solutionCount,
    normalizedTranslatedVinogradovMomentMod_eq_solutionCount]
  simpa using
    (show
      (vinogradovTranslatedSolutionCountMod Q m k s X : ℝ) ≤
        vinogradovTranslatedSolutionCountMod Q m k s Y by
      exact_mod_cast
        (by
          rw [vinogradovTranslatedSolutionCountMod_eq_unshifted,
            vinogradovTranslatedSolutionCountMod_eq_unshifted]
          exact vinogradovSolutionCountMod_mono_length Q k s X Y hXY))

/-- The normalized translated moment is its normalized real norm-power
average over coefficient vectors. -/
theorem normalizedTranslatedVinogradovMomentMod_eq_norm_average
    (Q m k s X : ℕ) [NeZero Q] :
    normalizedTranslatedVinogradovMomentMod Q m k s X =
      (((((Q : ℝ)⁻¹ ^ k) *
        ∑ c : Fin k → ZMod Q,
          ‖vinogradovTranslatedWeylSumMod Q m k X c‖ ^ (2 * s) : ℝ)) : ℂ) := by
  unfold normalizedTranslatedVinogradovMomentMod
  have hpair (z : ℂ) (n : ℕ) :
      z ^ n * (starRingEnd ℂ) z ^ n =
        ((‖z‖ ^ (2 * n) : ℝ) : ℂ) := by
    rw [← mul_pow, Complex.mul_conj']
    simp only [Complex.ofReal_pow, pow_mul]
  simp_rw [hpair]
  have hfactor :
      (Q : ℂ)⁻¹ ^ k =
        (((((Q : ℝ)⁻¹ ^ k : ℝ)) : ℂ)) := by
    rw [Complex.ofReal_pow, Complex.ofReal_inv,
      Complex.ofReal_natCast]
  rw [hfactor, ← Complex.ofReal_sum, ← Complex.ofReal_mul]

private def vinogradovTranslatedPhaseNatMod
    (Q m k : ℕ) (a : Fin k → ZMod Q) (n : ℕ) : ZMod Q :=
  ∑ j : Fin k,
    a j * ((m + n + 1 : ℕ) : ZMod Q) ^ (j.val + 1)

private theorem vinogradovTranslatedWeylSumMod_eq_sum_range
    (Q m k X : ℕ) [NeZero Q] (a : Fin k → ZMod Q) :
    vinogradovTranslatedWeylSumMod Q m k X a =
      ∑ n ∈ Finset.range X,
        ZMod.stdAddChar (vinogradovTranslatedPhaseNatMod Q m k a n) := by
  unfold vinogradovTranslatedWeylSumMod
  change (∑ n : Fin X,
      ZMod.stdAddChar
        (vinogradovTranslatedPhaseNatMod Q m k a n.val)) = _
  simpa only using
    (Fin.sum_univ_eq_sum_range
      (fun n ↦ ZMod.stdAddChar
        (vinogradovTranslatedPhaseNatMod Q m k a n)) X)

/-- Consecutive translated Weyl intervals concatenate exactly. -/
theorem vinogradovTranslatedWeylSumMod_add_length
    (Q m k X₁ X₂ : ℕ) [NeZero Q] (a : Fin k → ZMod Q) :
    vinogradovTranslatedWeylSumMod Q m k (X₁ + X₂) a =
      vinogradovTranslatedWeylSumMod Q m k X₁ a +
        vinogradovTranslatedWeylSumMod Q (m + X₁) k X₂ a := by
  rw [vinogradovTranslatedWeylSumMod_eq_sum_range,
    vinogradovTranslatedWeylSumMod_eq_sum_range,
    vinogradovTranslatedWeylSumMod_eq_sum_range,
    Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  simp only [vinogradovTranslatedPhaseNatMod, add_assoc]

/-- A translated interval of length `blocks * B` is the sum of its
consecutive length-`B` Weyl blocks. -/
theorem vinogradovTranslatedWeylSumMod_mul_length
    (Q m k blocks B : ℕ) [NeZero Q] (a : Fin k → ZMod Q) :
    vinogradovTranslatedWeylSumMod Q m k (blocks * B) a =
      ∑ j ∈ Finset.range blocks,
        vinogradovTranslatedWeylSumMod Q (m + j * B) k B a := by
  induction blocks with
  | zero =>
      rw [vinogradovTranslatedWeylSumMod_eq_sum_range]
      simp
  | succ blocks ih =>
      rw [Nat.succ_mul, vinogradovTranslatedWeylSumMod_add_length, ih,
        Finset.sum_range_succ]

/-- Euclidean division splits a translated Weyl interval into equal complete
blocks and one final remainder block. -/
theorem vinogradovTranslatedWeylSumMod_division_blocks
    (Q m k N B : ℕ) [NeZero Q] (a : Fin k → ZMod Q) (_hB : 0 < B) :
    vinogradovTranslatedWeylSumMod Q m k N a =
      (∑ j ∈ Finset.range (N / B),
        vinogradovTranslatedWeylSumMod Q (m + j * B) k B a) +
      vinogradovTranslatedWeylSumMod
        Q (m + (N / B) * B) k (N % B) a := by
  have hsplit :=
    vinogradovTranslatedWeylSumMod_add_length
      Q m k ((N / B) * B) (N % B) a
  rw [Nat.div_add_mod'] at hsplit
  rw [vinogradovTranslatedWeylSumMod_mul_length] at hsplit
  exact hsplit

private theorem norm_normalizedTranslatedVinogradovMomentMod_eq_norm_average
    (Q m k s X : ℕ) [NeZero Q] :
    ‖normalizedTranslatedVinogradovMomentMod Q m k s X‖ =
      ((Q : ℝ)⁻¹ ^ k) *
        ∑ c : Fin k → ZMod Q,
          ‖vinogradovTranslatedWeylSumMod Q m k X c‖ ^ (2 * s) := by
  rw [normalizedTranslatedVinogradovMomentMod_eq_norm_average,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  positivity

/-- Splitting a translated interval into complete length-`B` blocks and one
remainder block bounds its normalized moment by the sum of the corresponding
block moments, with the finite Holder cost for at most `N / B + 1` blocks. -/
theorem norm_normalizedTranslatedVinogradovMomentMod_le_division_blocks
    (Q m k s N B : ℕ) [NeZero Q] (hs : 0 < s) (hB : 0 < B) :
    ‖normalizedTranslatedVinogradovMomentMod Q m k s N‖ ≤
      (((N / B + 1 : ℕ) : ℝ) ^ (2 * s - 1)) *
        ((∑ j ∈ Finset.range (N / B),
            ‖normalizedTranslatedVinogradovMomentMod
              Q (m + j * B) k s B‖) +
          ‖normalizedTranslatedVinogradovMomentMod
            Q (m + (N / B) * B) k s (N % B)‖) := by
  classical
  let blocks := N / B
  let remainder := N % B
  let components (c : Fin k → ZMod Q) (j : ℕ) : ℂ :=
    if j < blocks then
      vinogradovTranslatedWeylSumMod Q (m + j * B) k B c
    else
      vinogradovTranslatedWeylSumMod
        Q (m + blocks * B) k remainder c
  have hcomponentSum (c : Fin k → ZMod Q) :
      ∑ j ∈ Finset.range (blocks + 1), components c j =
        (∑ j ∈ Finset.range blocks,
          vinogradovTranslatedWeylSumMod Q (m + j * B) k B c) +
        vinogradovTranslatedWeylSumMod
          Q (m + blocks * B) k remainder c := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      simp [components, Finset.mem_range.mp hj]
    · simp [components]
  have hcomponentNormSum (c : Fin k → ZMod Q) :
      ∑ j ∈ Finset.range (blocks + 1),
          ‖components c j‖ ^ (2 * s) =
        (∑ j ∈ Finset.range blocks,
          ‖vinogradovTranslatedWeylSumMod
            Q (m + j * B) k B c‖ ^ (2 * s)) +
        ‖vinogradovTranslatedWeylSumMod
          Q (m + blocks * B) k remainder c‖ ^ (2 * s) := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      simp [components, Finset.mem_range.mp hj]
    · simp [components]
  have hpoint (c : Fin k → ZMod Q) :
      ‖vinogradovTranslatedWeylSumMod Q m k N c‖ ^ (2 * s) ≤
        (((blocks + 1 : ℕ) : ℝ) ^ (2 * s - 1)) *
          ((∑ j ∈ Finset.range blocks,
              ‖vinogradovTranslatedWeylSumMod
                Q (m + j * B) k B c‖ ^ (2 * s)) +
            ‖vinogradovTranslatedWeylSumMod
              Q (m + blocks * B) k remainder c‖ ^ (2 * s)) := by
    have hholder :=
      norm_finset_sum_pow_le_card_mul_sum_norm_pow
        (Finset.range (blocks + 1)) (components c) (2 * s - 1)
    have hpow : 2 * s - 1 + 1 = 2 * s := by omega
    rw [hpow] at hholder
    rw [hcomponentSum, ←
      vinogradovTranslatedWeylSumMod_division_blocks Q m k N B c hB,
      hcomponentNormSum] at hholder
    simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using hholder
  have hsumSwap :
      (∑ c : Fin k → ZMod Q,
          ∑ j ∈ Finset.range blocks,
            ‖vinogradovTranslatedWeylSumMod
              Q (m + j * B) k B c‖ ^ (2 * s)) =
        ∑ j ∈ Finset.range blocks,
          ∑ c : Fin k → ZMod Q,
            ‖vinogradovTranslatedWeylSumMod
              Q (m + j * B) k B c‖ ^ (2 * s) := by
    rw [Finset.sum_comm]
  rw [norm_normalizedTranslatedVinogradovMomentMod_eq_norm_average]
  calc
    ((Q : ℝ)⁻¹ ^ k) *
        ∑ c : Fin k → ZMod Q,
          ‖vinogradovTranslatedWeylSumMod Q m k N c‖ ^ (2 * s) ≤
      ((Q : ℝ)⁻¹ ^ k) *
        ∑ c : Fin k → ZMod Q,
          ((((blocks + 1 : ℕ) : ℝ) ^ (2 * s - 1)) *
            ((∑ j ∈ Finset.range blocks,
                ‖vinogradovTranslatedWeylSumMod
                  Q (m + j * B) k B c‖ ^ (2 * s)) +
              ‖vinogradovTranslatedWeylSumMod
                Q (m + blocks * B) k remainder c‖ ^ (2 * s))) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun c _ ↦ hpoint c) (by positivity)
    _ = (((blocks + 1 : ℕ) : ℝ) ^ (2 * s - 1)) *
        ((∑ j ∈ Finset.range blocks,
            (((Q : ℝ)⁻¹ ^ k) *
              ∑ c : Fin k → ZMod Q,
                ‖vinogradovTranslatedWeylSumMod
                  Q (m + j * B) k B c‖ ^ (2 * s))) +
          (((Q : ℝ)⁻¹ ^ k) *
            ∑ c : Fin k → ZMod Q,
              ‖vinogradovTranslatedWeylSumMod
                Q (m + blocks * B) k remainder c‖ ^ (2 * s))) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hsumSwap]
      rw [← Finset.mul_sum]
      ring
    _ = (((blocks + 1 : ℕ) : ℝ) ^ (2 * s - 1)) *
        ((∑ j ∈ Finset.range blocks,
            ‖normalizedTranslatedVinogradovMomentMod
              Q (m + j * B) k s B‖) +
          ‖normalizedTranslatedVinogradovMomentMod
            Q (m + blocks * B) k s remainder‖) := by
      congr 2
      · apply Finset.sum_congr rfl
        intro j hj
        exact
          (norm_normalizedTranslatedVinogradovMomentMod_eq_norm_average
            Q (m + j * B) k s B).symm
      · exact
          (norm_normalizedTranslatedVinogradovMomentMod_eq_norm_average
            Q (m + blocks * B) k s remainder).symm
    _ = (((N / B + 1 : ℕ) : ℝ) ^ (2 * s - 1)) *
        ((∑ j ∈ Finset.range (N / B),
            ‖normalizedTranslatedVinogradovMomentMod
              Q (m + j * B) k s B‖) +
          ‖normalizedTranslatedVinogradovMomentMod
            Q (m + (N / B) * B) k s (N % B)‖) := by
      rfl

/-- The complete-block factor is genuinely smaller than the squared trivial
moment bound: `q! < p^q` supplies the missing power of `p`. -/
theorem primeCubic_completeBlockSaving_sq_lt_trivial
    (p r q : ℕ) [Fact p.Prime] (hq : 0 < q) (hqp : q < p) :
    (q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q) <
      (p : ℝ) ^ (12 * r + 12 * q) := by
  have hfactorialNat : q.factorial < p ^ q :=
    (Nat.factorial_le_pow q).trans_lt
      (Nat.pow_lt_pow_left hqp hq.ne')
  have hfactorialReal : (q.factorial : ℝ) < (p : ℝ) ^ q := by
    exact_mod_cast hfactorialNat
  have hpReal : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hexponent :
      q + (12 * r + 11 * q) = 12 * r + 12 * q := by
    omega
  calc
    (q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q) <
        (p : ℝ) ^ q * (p : ℝ) ^ (12 * r + 11 * q) :=
      mul_lt_mul_of_pos_right hfactorialReal
        (pow_pos hpReal (12 * r + 11 * q))
    _ = (p : ℝ) ^ (12 * r + 12 * q) := by
      rw [← pow_add, hexponent]

/-- Covering an arbitrary translated interval by length-`p^3` blocks
preserves the complete-block moment saving, up to the explicit finite Holder
cost from the number of blocks. -/
theorem
    norm_normalizedTranslatedVinogradovMomentMod_le_primeCubic_blockCoverSaving
    (p m k r q N : ℕ) [Fact p.Prime]
    (hr : 0 < r) (hq : 0 < q) (hqk : q ≤ k) (hqp : q < p)
    (hbudget : 3 * q + 1 ≤ 2 * (k - r + 1)) :
    ‖normalizedTranslatedVinogradovMomentMod
        (p ^ ((k - r + 1) * 2)) m k (r + q) N‖ ≤
      ((((N / (p ^ 2 * p) + 1 : ℕ) : ℝ) ^ (2 * (r + q))) *
        Real.sqrt
          ((q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q))) := by
  let Q := p ^ ((k - r + 1) * 2)
  let B := p ^ 2 * p
  let A :=
    Real.sqrt ((q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q))
  letI : NeZero Q :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hB : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (pow_pos hp 2) hp
  have hblock (start : ℕ) :
      ‖normalizedTranslatedVinogradovMomentMod
          Q start k (r + q) B‖ ≤ A := by
    apply Real.le_sqrt_of_sq_le
    simpa [Q, B, A] using
      norm_normalizedTranslatedVinogradovMomentMod_sq_le_primeCubic_completeBlockSaving
        p start k r q hr hq hqk hqp hbudget
  have hremainder :
      ‖normalizedTranslatedVinogradovMomentMod
          Q (m + (N / B) * B) k (r + q) (N % B)‖ ≤ A := by
    exact
      (norm_normalizedTranslatedVinogradovMomentMod_mono_length
        Q (m + (N / B) * B) k (r + q) (N % B) B
          (Nat.le_of_lt (Nat.mod_lt N hB))).trans
        (hblock (m + (N / B) * B))
  have hdivision :=
    norm_normalizedTranslatedVinogradovMomentMod_le_division_blocks
      Q m k (r + q) N B (by omega) hB
  calc
    ‖normalizedTranslatedVinogradovMomentMod Q m k (r + q) N‖ ≤
      ((((N / B + 1 : ℕ) : ℝ) ^ (2 * (r + q) - 1)) *
        ((∑ j ∈ Finset.range (N / B),
            ‖normalizedTranslatedVinogradovMomentMod
              Q (m + j * B) k (r + q) B‖) +
          ‖normalizedTranslatedVinogradovMomentMod
            Q (m + (N / B) * B) k (r + q) (N % B)‖)) :=
      hdivision
    _ ≤ ((((N / B + 1 : ℕ) : ℝ) ^ (2 * (r + q) - 1)) *
        (((N / B : ℕ) : ℝ) * A + A)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add _ hremainder
      calc
        (∑ j ∈ Finset.range (N / B),
            ‖normalizedTranslatedVinogradovMomentMod
              Q (m + j * B) k (r + q) B‖) ≤
            ∑ _j ∈ Finset.range (N / B), A := by
              exact Finset.sum_le_sum fun j _ ↦ hblock (m + j * B)
        _ = ((N / B : ℕ) : ℝ) * A := by simp
    _ = ((((N / B + 1 : ℕ) : ℝ) ^ (2 * (r + q))) * A) := by
      have hsum :
          ((N / B : ℕ) : ℝ) * A + A =
            (((N / B + 1 : ℕ) : ℝ)) * A := by
        rw [Nat.cast_add, Nat.cast_one]
        ring
      rw [hsum, ← mul_assoc, ← pow_succ]
      congr 2
      omega
    _ = ((((N / (p ^ 2 * p) + 1 : ℕ) : ℝ) ^ (2 * (r + q))) *
        Real.sqrt
          ((q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q))) := by
      rfl

end

end ZeroFreeRegion.VinogradovKorobov
