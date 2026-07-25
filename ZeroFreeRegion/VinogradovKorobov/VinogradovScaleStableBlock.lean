import ZeroFreeRegion.VinogradovKorobov.VinogradovTranslatedBlockDecomposition

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Once an interval contains one full length-`B` block, the padded block
count times `B` is at most twice the interval length. -/
theorem divisionBlockCount_mul_le_two_length
    (N B : ℕ) (hB : 0 < B) (hBN : B ≤ N) :
    (N / B + 1) * B ≤ 2 * N := by
  have hone : 1 ≤ N / B := by
    rw [Nat.le_div_iff_mul_le hB]
    simpa using hBN
  have hcount : N / B + 1 ≤ 2 * (N / B) := by omega
  calc
    (N / B + 1) * B ≤ (2 * (N / B)) * B :=
      Nat.mul_le_mul_right B hcount
    _ = 2 * ((N / B) * B) := by ring
    _ ≤ 2 * N :=
      Nat.mul_le_mul_left 2 (Nat.div_mul_le_self N B)

/-- A simple explicit prime-size threshold implies the factorial gain needed
to absorb the padded block cover. -/
theorem primeCubic_blockCover_gain_of_threshold
    (p r q : ℕ) (hq : 0 < q)
    (hp : 2 ^ (4 * (r + q)) * q < p) :
    2 ^ (4 * (r + q)) * q.factorial < p ^ q := by
  let C := 2 ^ (4 * (r + q))
  have hC : 1 ≤ C := by
    dsimp [C]
    exact one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  have hCpow : C ≤ C ^ q :=
    le_self_pow₀ hC hq.ne'
  calc
    2 ^ (4 * (r + q)) * q.factorial =
        C * q.factorial := by rfl
    _ ≤ C * q ^ q :=
      Nat.mul_le_mul_left C (Nat.factorial_le_pow q)
    _ ≤ C ^ q * q ^ q :=
      Nat.mul_le_mul_right (q ^ q) hCpow
    _ = (C * q) ^ q := by
      rw [mul_pow]
    _ < p ^ q :=
      Nat.pow_lt_pow_left (by simpa [C] using hp) hq.ne'

/-- The explicit factorial saving absorbs the factor-two padded block cover
when `2^(4s) * q! < p^q`, where `s = r + q`. -/
theorem primeCubic_completeBlockCoverFactor_lt_trivial
    (p r q : ℕ) [Fact p.Prime]
    (hgain : 2 ^ (4 * (r + q)) * q.factorial < p ^ q) :
    Real.sqrt
          ((q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q)) *
        (2 : ℝ) ^ (2 * (r + q)) <
      (((p ^ 2 * p : ℕ) : ℝ)) ^ (2 * (r + q)) := by
  have hpReal : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hgainReal :
      (2 : ℝ) ^ (4 * (r + q)) * (q.factorial : ℝ) <
        (p : ℝ) ^ q := by
    exact_mod_cast hgain
  have hradicand :
      0 ≤ (q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q) := by
    positivity
  have htwoSquare :
      (((2 : ℝ) ^ (2 * (r + q))) ^ 2) =
        (2 : ℝ) ^ (4 * (r + q)) := by
    rw [← pow_mul]
    congr 1
    omega
  have hleftSquare :
      (Real.sqrt
            ((q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q)) *
          (2 : ℝ) ^ (2 * (r + q))) ^ 2 =
        ((2 : ℝ) ^ (4 * (r + q)) * (q.factorial : ℝ)) *
          (p : ℝ) ^ (12 * r + 11 * q) := by
    rw [mul_pow, Real.sq_sqrt hradicand, htwoSquare]
    ring
  have hbase : p ^ 2 * p = p ^ 3 := by
    exact (pow_succ p 2).symm
  have hrightSquareNat :
      (((p ^ 2 * p) ^ (2 * (r + q))) ^ 2) =
        p ^ (12 * (r + q)) := by
    calc
      (((p ^ 2 * p) ^ (2 * (r + q))) ^ 2) =
          (((p ^ 3) ^ (2 * (r + q))) ^ 2) := by
            rw [hbase]
      _ = p ^ (3 * ((2 * (r + q)) * 2)) := by
        rw [← pow_mul, ← pow_mul]
      _ = p ^ (12 * (r + q)) := by
        congr 1
        omega
  have hrightSquare :
      ((((p ^ 2 * p : ℕ) : ℝ) ^ (2 * (r + q))) ^ 2) =
        (p : ℝ) ^ (12 * (r + q)) := by
    exact_mod_cast hrightSquareNat
  apply
    (sq_lt_sq₀
      (mul_nonneg (Real.sqrt_nonneg _)
        (by positivity : (0 : ℝ) ≤ 2 ^ (2 * (r + q))))
      (by positivity :
        (0 : ℝ) ≤ (((p ^ 2 * p : ℕ) : ℝ)) ^ (2 * (r + q)))).mp
  rw [hleftSquare, hrightSquare]
  calc
    ((2 : ℝ) ^ (4 * (r + q)) * (q.factorial : ℝ)) *
          (p : ℝ) ^ (12 * r + 11 * q) <
        (p : ℝ) ^ q * (p : ℝ) ^ (12 * r + 11 * q) :=
      mul_lt_mul_of_pos_right hgainReal
        (pow_pos hpReal (12 * r + 11 * q))
    _ = (p : ℝ) ^ (12 * (r + q)) := by
      rw [← pow_add]
      congr 1
      omega

/-- The scale-independent multiplicative gain left after covering a long
interval by length-`p^3` blocks. -/
noncomputable def primeCubicBlockCoverGain
    (p r q : ℕ) : ℝ :=
  (Real.sqrt
      ((q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q)) *
    (2 : ℝ) ^ (2 * (r + q))) /
    (((p ^ 2 * p : ℕ) : ℝ)) ^ (2 * (r + q))

/-- The explicit factorial condition makes the scale-independent block-cover
gain strictly smaller than one. -/
theorem primeCubicBlockCoverGain_lt_one
    (p r q : ℕ) [Fact p.Prime]
    (hgain : 2 ^ (4 * (r + q)) * q.factorial < p ^ q) :
    primeCubicBlockCoverGain p r q < 1 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hB : 0 < p ^ 2 * p :=
    Nat.mul_pos (pow_pos hp 2) hp
  have hBReal : (0 : ℝ) < ((p ^ 2 * p : ℕ) : ℝ) := by
    exact_mod_cast hB
  have hden :
      (0 : ℝ) < (((p ^ 2 * p : ℕ) : ℝ)) ^ (2 * (r + q)) :=
    pow_pos hBReal _
  rw [primeCubicBlockCoverGain, div_lt_one hden]
  exact primeCubic_completeBlockCoverFactor_lt_trivial p r q hgain

/-- The arbitrary translated moment is bounded by the trivial length power
times a gain independent of the interval length. -/
theorem
    norm_normalizedTranslatedVinogradovMomentMod_le_primeCubicBlockCoverGain_mul_trivial
    (p m k r q N : ℕ) [Fact p.Prime]
    (hr : 0 < r) (hq : 0 < q) (hqk : q ≤ k) (hqp : q < p)
    (hbudget : 3 * q + 1 ≤ 2 * (k - r + 1))
    (hN : p ^ 2 * p ≤ N) :
    ‖normalizedTranslatedVinogradovMomentMod
        (p ^ ((k - r + 1) * 2)) m k (r + q) N‖ ≤
      (N : ℝ) ^ (2 * (r + q)) *
        primeCubicBlockCoverGain p r q := by
  let B := p ^ 2 * p
  let A :=
    Real.sqrt ((q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q))
  let e := 2 * (r + q)
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hB : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (pow_pos hp 2) hp
  have hBN : B ≤ N := by
    simpa [B] using hN
  have hmoment :
      ‖normalizedTranslatedVinogradovMomentMod
          (p ^ ((k - r + 1) * 2)) m k (r + q) N‖ ≤
        (((N / B + 1 : ℕ) : ℝ) ^ e) * A := by
    simpa [B, A, e] using
      norm_normalizedTranslatedVinogradovMomentMod_le_primeCubic_blockCoverSaving
        p m k r q N hr hq hqk hqp hbudget
  have hcountNat :
      (N / B + 1) * B ≤ 2 * N :=
    divisionBlockCount_mul_le_two_length N B hB hBN
  have hcountReal :
      (((N / B + 1 : ℕ) : ℝ) * (B : ℝ)) ≤
        (2 : ℝ) * (N : ℝ) := by
    exact_mod_cast hcountNat
  have hcountPower :
      ((((N / B + 1 : ℕ) : ℝ) * (B : ℝ)) ^ e) ≤
        (((2 : ℝ) * (N : ℝ)) ^ e) :=
    pow_le_pow_left₀ (by positivity) hcountReal e
  have hscaled :
      ((((N / B + 1 : ℕ) : ℝ) ^ e) * A) * (B : ℝ) ^ e ≤
        (N : ℝ) ^ e * (A * (2 : ℝ) ^ e) := by
    calc
      ((((N / B + 1 : ℕ) : ℝ) ^ e) * A) * (B : ℝ) ^ e =
          ((((N / B + 1 : ℕ) : ℝ) * (B : ℝ)) ^ e) * A := by
            rw [mul_pow]
            ring
      _ ≤ (((2 : ℝ) * (N : ℝ)) ^ e) * A :=
        mul_le_mul_of_nonneg_right hcountPower (by positivity)
      _ = (N : ℝ) ^ e * (A * (2 : ℝ) ^ e) := by
        rw [mul_pow]
        ring
  have hcover :
      (((N / B + 1 : ℕ) : ℝ) ^ e) * A ≤
        (N : ℝ) ^ e * primeCubicBlockCoverGain p r q := by
    rw [primeCubicBlockCoverGain]
    change
      (((N / B + 1 : ℕ) : ℝ) ^ e) * A ≤
        (N : ℝ) ^ e * ((A * (2 : ℝ) ^ e) / (B : ℝ) ^ e)
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (B : ℝ) ^ e)).2
    simpa only [mul_assoc] using hscaled
  exact hmoment.trans hcover

/-- For intervals of length at least `p^3`, the explicit factorial condition
makes the arbitrary translated moment estimate strictly better than its
length-`N` trivial bound. -/
theorem
    norm_normalizedTranslatedVinogradovMomentMod_lt_trivial_of_primeCubic_blockCoverSaving
    (p m k r q N : ℕ) [Fact p.Prime]
    (hr : 0 < r) (hq : 0 < q) (hqk : q ≤ k) (hqp : q < p)
    (hbudget : 3 * q + 1 ≤ 2 * (k - r + 1))
    (hN : p ^ 2 * p ≤ N)
    (hgain : 2 ^ (4 * (r + q)) * q.factorial < p ^ q) :
    ‖normalizedTranslatedVinogradovMomentMod
        (p ^ ((k - r + 1) * 2)) m k (r + q) N‖ <
      (N : ℝ) ^ (2 * (r + q)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hNpos : 0 < N :=
    (Nat.mul_pos (pow_pos hp 2) hp).trans_le hN
  calc
    ‖normalizedTranslatedVinogradovMomentMod
        (p ^ ((k - r + 1) * 2)) m k (r + q) N‖ ≤
        (N : ℝ) ^ (2 * (r + q)) *
          primeCubicBlockCoverGain p r q :=
      norm_normalizedTranslatedVinogradovMomentMod_le_primeCubicBlockCoverGain_mul_trivial
        p m k r q N hr hq hqk hqp hbudget hN
    _ < (N : ℝ) ^ (2 * (r + q)) * 1 :=
      mul_lt_mul_of_pos_left
        (primeCubicBlockCoverGain_lt_one p r q hgain)
        (pow_pos (by exact_mod_cast hNpos) _)
    _ = (N : ℝ) ^ (2 * (r + q)) := mul_one _

/-- A directly usable scale-stable form: a prime above the explicit threshold
automatically supplies both `q < p` and the factorial block-cover gain. -/
theorem
    norm_normalizedTranslatedVinogradovMomentMod_lt_trivial_of_primeCubic_threshold
    (p m k r q N : ℕ) [Fact p.Prime]
    (hr : 0 < r) (hq : 0 < q) (hqk : q ≤ k)
    (hbudget : 3 * q + 1 ≤ 2 * (k - r + 1))
    (hN : p ^ 2 * p ≤ N)
    (hthreshold : 2 ^ (4 * (r + q)) * q < p) :
    ‖normalizedTranslatedVinogradovMomentMod
        (p ^ ((k - r + 1) * 2)) m k (r + q) N‖ <
      (N : ℝ) ^ (2 * (r + q)) := by
  have hfactorPos : 0 < 2 ^ (4 * (r + q)) :=
    pow_pos (by norm_num : 0 < (2 : ℕ)) _
  have hqp : q < p :=
    (Nat.le_mul_of_pos_left q hfactorPos).trans_lt hthreshold
  exact
    norm_normalizedTranslatedVinogradovMomentMod_lt_trivial_of_primeCubic_blockCoverSaving
      p m k r q N hr hq hqk hqp hbudget hN
        (primeCubic_blockCover_gain_of_threshold p r q hq hthreshold)

end

end ZeroFreeRegion.VinogradovKorobov
