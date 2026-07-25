import ZeroFreeRegion.VinogradovKorobov.VinogradovScaleStableBlock
import Mathlib.NumberTheory.Bertrand

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Every exact integer Vinogradov solution remains a solution modulo `Q`,
so the exact solution count is bounded by the modular count. -/
theorem vinogradovSolutionCountNat_le_mod
    (Q k s X : ℕ) :
    vinogradovSolutionCountNat k s X ≤
      vinogradovSolutionCountMod Q k s X := by
  classical
  unfold vinogradovSolutionCountNat vinogradovSolutionCountMod
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  exact hy.toMod Q k s X

/-- Consequently, every normalized translated modular moment is an upper
bound for the ordinary exact Vinogradov solution count. -/
theorem
    vinogradovSolutionCountNat_le_norm_normalizedTranslatedVinogradovMomentMod
    (Q m k s X : ℕ) [NeZero Q] :
    (vinogradovSolutionCountNat k s X : ℝ) ≤
      ‖normalizedTranslatedVinogradovMomentMod Q m k s X‖ := by
  have hcount :
      (vinogradovSolutionCountNat k s X : ℝ) ≤
        (vinogradovSolutionCountMod Q k s X : ℝ) := by
    exact_mod_cast vinogradovSolutionCountNat_le_mod Q k s X
  rw [normalizedTranslatedVinogradovMomentMod_eq_solutionCount,
    vinogradovTranslatedSolutionCountMod_eq_unshifted]
  simpa only [Complex.norm_natCast] using hcount

/-- The scale-stable modular block estimate therefore gives the same
explicit gain for the ordinary exact Vinogradov solution count. -/
theorem vinogradovSolutionCountNat_le_primeCubicBlockCoverGain_mul_trivial
    (p k r q N : ℕ) [Fact p.Prime]
    (hr : 0 < r) (hq : 0 < q) (hqk : q ≤ k) (hqp : q < p)
    (hbudget : 3 * q + 1 ≤ 2 * (k - r + 1))
    (hN : p ^ 2 * p ≤ N) :
    (vinogradovSolutionCountNat k (r + q) N : ℝ) ≤
      (N : ℝ) ^ (2 * (r + q)) *
        primeCubicBlockCoverGain p r q := by
  calc
    (vinogradovSolutionCountNat k (r + q) N : ℝ) ≤
        ‖normalizedTranslatedVinogradovMomentMod
          (p ^ ((k - r + 1) * 2)) 0 k (r + q) N‖ :=
      vinogradovSolutionCountNat_le_norm_normalizedTranslatedVinogradovMomentMod
        (p ^ ((k - r + 1) * 2)) 0 k (r + q) N
    _ ≤ (N : ℝ) ^ (2 * (r + q)) *
          primeCubicBlockCoverGain p r q :=
      norm_normalizedTranslatedVinogradovMomentMod_le_primeCubicBlockCoverGain_mul_trivial
        p 0 k r q N hr hq hqk hqp hbudget hN

/-- Squaring the block-cover gain exposes its exact inverse `p^q` saving. -/
theorem primeCubicBlockCoverGain_sq
    (p r q : ℕ) (hp : 0 < p) :
    primeCubicBlockCoverGain p r q ^ 2 =
      ((2 : ℝ) ^ (4 * (r + q)) * (q.factorial : ℝ)) /
        (p : ℝ) ^ q := by
  have hpReal : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp
  have hradicand :
      0 ≤ (q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q) := by
    positivity
  have htwo :
      (((2 : ℝ) ^ (2 * (r + q))) ^ 2) =
        (2 : ℝ) ^ (4 * (r + q)) := by
    rw [← pow_mul]
    congr 1
    omega
  have hbase :
      (((p ^ 2 * p : ℕ) : ℝ)) = (p : ℝ) ^ 3 := by
    norm_cast
  have hden :
      ((((p ^ 2 * p : ℕ) : ℝ) ^ (2 * (r + q))) ^ 2) =
        (p : ℝ) ^ (12 * (r + q)) := by
    rw [hbase, ← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [primeCubicBlockCoverGain, div_pow, mul_pow,
    Real.sq_sqrt hradicand, htwo, hden]
  apply
    (div_eq_div_iff
      (pow_ne_zero _ hpReal.ne')
      (pow_ne_zero _ hpReal.ne')).2
  calc
    ((q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q)) *
          (2 : ℝ) ^ (4 * (r + q)) * (p : ℝ) ^ q =
        ((2 : ℝ) ^ (4 * (r + q)) * (q.factorial : ℝ)) *
          (p : ℝ) ^ ((12 * r + 11 * q) + q) := by
            rw [pow_add]
            ring
    _ = ((2 : ℝ) ^ (4 * (r + q)) * (q.factorial : ℝ)) *
          (p : ℝ) ^ (12 * (r + q)) := by
            congr 2
            omega

/-- The scale-independent block-cover gain is always nonnegative. -/
theorem primeCubicBlockCoverGain_nonneg
    (p r q : ℕ) :
    0 ≤ primeCubicBlockCoverGain p r q := by
  rw [primeCubicBlockCoverGain]
  positivity

/-- Bertrand's postulate selects a prime scale comparable to `x`, turning
the exact inverse-`p^q` square gain into an inverse-`x^q` gain. -/
theorem exists_primeCubicBlockCoverGain_sq_lt
    (x r q : ℕ) (hx : 0 < x) (hq : 0 < q) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ p ≤ 2 * x ∧
      primeCubicBlockCoverGain p r q ^ 2 <
        ((2 : ℝ) ^ (4 * (r + q)) * (q.factorial : ℝ)) /
          (x : ℝ) ^ q := by
  obtain ⟨p, hp, hxp, hp2x⟩ :=
    Nat.exists_prime_lt_and_le_two_mul x hx.ne'
  refine ⟨p, hp, hxp, hp2x, ?_⟩
  rw [primeCubicBlockCoverGain_sq p r q hp.pos]
  have hxpPowNat : x ^ q < p ^ q :=
    Nat.pow_lt_pow_left hxp hq.ne'
  have hxpPowReal : (x : ℝ) ^ q < (p : ℝ) ^ q := by
    exact_mod_cast hxpPowNat
  exact
    div_lt_div_of_pos_left
      (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)
        (by positivity))
      (pow_pos (by exact_mod_cast hx) q)
      hxpPowReal

/-- On the cubic cofinal scale `(2x)^3`, a Bertrand prime converts the
finite block estimate into a genuine power-decaying bound for the ordinary
integer Vinogradov solution count. -/
theorem vinogradovSolutionCountNat_lt_cubicScalePowerSaving
    (x k r q : ℕ)
    (hx : 0 < x) (hr : 0 < r) (hq : 0 < q) (hqk : q ≤ k)
    (hbudget : 3 * q + 1 ≤ 2 * (k - r + 1))
    (hthreshold : 2 ^ (4 * (r + q)) * q ≤ x) :
    (vinogradovSolutionCountNat
        k (r + q) ((2 * x) ^ 3) : ℝ) <
      (((2 * x) ^ 3 : ℕ) : ℝ) ^ (2 * (r + q)) *
        Real.sqrt
          (((2 : ℝ) ^ (4 * (r + q)) * (q.factorial : ℝ)) /
            (x : ℝ) ^ q) := by
  obtain ⟨p, hp, hxp, hp2x, hgainSq⟩ :=
    exists_primeCubicBlockCoverGain_sq_lt x r q hx hq
  letI : Fact p.Prime := ⟨hp⟩
  have hfactorPos : 0 < 2 ^ (4 * (r + q)) :=
    pow_pos (by norm_num : 0 < (2 : ℕ)) _
  have hqp : q < p :=
    (Nat.le_mul_of_pos_left q hfactorPos).trans_lt
      (hthreshold.trans_lt hxp)
  have hN : p ^ 2 * p ≤ (2 * x) ^ 3 := by
    have hpCube : p ^ 3 ≤ (2 * x) ^ 3 :=
      Nat.pow_le_pow_left hp2x 3
    simpa [pow_succ] using hpCube
  have hradicandPos :
      (0 : ℝ) <
        ((2 : ℝ) ^ (4 * (r + q)) * (q.factorial : ℝ)) /
          (x : ℝ) ^ q := by
    exact div_pos
      (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)
        (by positivity))
      (pow_pos (by exact_mod_cast hx) q)
  have hgain :
      primeCubicBlockCoverGain p r q <
        Real.sqrt
          (((2 : ℝ) ^ (4 * (r + q)) * (q.factorial : ℝ)) /
            (x : ℝ) ^ q) := by
    apply
      (sq_lt_sq₀
        (primeCubicBlockCoverGain_nonneg p r q)
        (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hradicandPos.le]
    exact hgainSq
  calc
    (vinogradovSolutionCountNat
        k (r + q) ((2 * x) ^ 3) : ℝ) ≤
      (((2 * x) ^ 3 : ℕ) : ℝ) ^ (2 * (r + q)) *
        primeCubicBlockCoverGain p r q :=
      vinogradovSolutionCountNat_le_primeCubicBlockCoverGain_mul_trivial
        p k r q ((2 * x) ^ 3) hr hq hqk hqp hbudget hN
    _ < (((2 * x) ^ 3 : ℕ) : ℝ) ^ (2 * (r + q)) *
        Real.sqrt
          (((2 : ℝ) ^ (4 * (r + q)) * (q.factorial : ℝ)) /
            (x : ℝ) ^ q) :=
      mul_lt_mul_of_pos_left hgain
        (pow_pos (by positivity) _)

end

end ZeroFreeRegion.VinogradovKorobov
