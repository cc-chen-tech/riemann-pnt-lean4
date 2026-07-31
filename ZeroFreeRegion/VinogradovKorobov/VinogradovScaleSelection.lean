import ZeroFreeRegion.VinogradovKorobov.VinogradovScaleStableBlock
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.NumberTheory.Bertrand

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The integer scale immediately above the real cubic scale of `N`. -/
def vinogradovCubicScale (N : ℕ) : ℕ :=
  Nat.nthRoot 3 N + 1

/-- Every length lies below the doubled cube of its selected cubic scale. -/
theorem le_vinogradovCubicEnvelope (N : ℕ) :
    N ≤ (2 * vinogradovCubicScale N) ^ 3 := by
  have hcube :
      N ≤ vinogradovCubicScale N ^ 3 := by
    exact
      (Nat.lt_pow_nthRoot_add_one
        (by norm_num : 3 ≠ 0) N).le
  exact hcube.trans
    (Nat.pow_le_pow_left (by
      unfold vinogradovCubicScale
      omega) 3)

/-- For positive lengths, the selected cubic envelope loses at most the
absolute factor `64`. -/
theorem vinogradovCubicEnvelope_le_sixtyFour_mul
    (N : ℕ) (hN : 0 < N) :
    (2 * vinogradovCubicScale N) ^ 3 ≤ 64 * N := by
  have hroot :
      1 ≤ Nat.nthRoot 3 N := by
    rw [Nat.le_nthRoot_iff (by norm_num : 3 ≠ 0)]
    simpa using hN
  have hrootCube :
      Nat.nthRoot 3 N ^ 3 ≤ N :=
    Nat.pow_nthRoot_le (.inl (by norm_num : 3 ≠ 0))
  calc
    (2 * vinogradovCubicScale N) ^ 3 ≤
        (4 * Nat.nthRoot 3 N) ^ 3 := by
      apply Nat.pow_le_pow_left
      unfold vinogradovCubicScale
      omega
    _ = 64 * (Nat.nthRoot 3 N) ^ 3 := by ring
    _ ≤ 64 * N := Nat.mul_le_mul_left 64 hrootCube

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

/-- Ordinary integer Vinogradov solution counts are monotone in the
interval length. -/
theorem vinogradovSolutionCountNat_mono_length
    (k s X Y : ℕ) (hXY : X ≤ Y) :
    vinogradovSolutionCountNat k s X ≤
      vinogradovSolutionCountNat k s Y := by
  by_cases hY : Y = 0
  · subst Y
    have hX : X = 0 := Nat.eq_zero_of_le_zero hXY
    subst X
    exact le_rfl
  · have hYpos : 1 ≤ Y := Nat.one_le_iff_ne_zero.mpr hY
    let Q := s * Y ^ k + 1
    have hQtop : s * Y ^ k < Q := by
      simp [Q]
    have hQY : ∀ j : Fin k, s * Y ^ (j.val + 1) < Q := by
      intro j
      exact
        (Nat.mul_le_mul_left s
          (pow_le_pow_right' hYpos
            (Nat.succ_le_iff.mpr j.isLt))).trans_lt hQtop
    have hQX : ∀ j : Fin k, s * X ^ (j.val + 1) < Q := by
      intro j
      exact
        (Nat.mul_le_mul_left s
          (Nat.pow_le_pow_left hXY (j.val + 1))).trans_lt (hQY j)
    rw [← vinogradovSolutionCountMod_eq_nat_of_scale Q k s X hQX,
      ← vinogradovSolutionCountMod_eq_nat_of_scale Q k s Y hQY]
    exact vinogradovSolutionCountMod_mono_length Q k s X Y hXY

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

/-- The cubic-scale saving extends to every length by monotonicity and the
least strictly larger integer cubic scale. -/
theorem vinogradovSolutionCountNat_lt_cubicEnvelopePowerSaving
    (N k r q : ℕ)
    (hr : 0 < r) (hq : 0 < q) (hqk : q ≤ k)
    (hbudget : 3 * q + 1 ≤ 2 * (k - r + 1))
    (hthreshold :
      2 ^ (4 * (r + q)) * q ≤ vinogradovCubicScale N) :
    (vinogradovSolutionCountNat k (r + q) N : ℝ) <
      ((((2 * vinogradovCubicScale N) ^ 3 : ℕ) : ℝ) ^
          (2 * (r + q))) *
        Real.sqrt
          (((2 : ℝ) ^ (4 * (r + q)) * (q.factorial : ℝ)) /
            (vinogradovCubicScale N : ℝ) ^ q) := by
  have hscalePos : 0 < vinogradovCubicScale N := by
    unfold vinogradovCubicScale
    omega
  have hmono :
      (vinogradovSolutionCountNat k (r + q) N : ℝ) ≤
        (vinogradovSolutionCountNat
          k (r + q) ((2 * vinogradovCubicScale N) ^ 3) : ℝ) := by
    exact_mod_cast
      vinogradovSolutionCountNat_mono_length
        k (r + q) N ((2 * vinogradovCubicScale N) ^ 3)
        (le_vinogradovCubicEnvelope N)
  exact hmono.trans_lt
    (vinogradovSolutionCountNat_lt_cubicScalePowerSaving
      (vinogradovCubicScale N) k r q hscalePos hr hq hqk
      hbudget hthreshold)

/-- For positive lengths, the arbitrary-scale estimate has a fixed-factor
polynomial envelope while retaining the explicit cubic-root saving. -/
theorem vinogradovSolutionCountNat_lt_sixtyFourMulPowerSaving
    (N k r q : ℕ) (hN : 0 < N)
    (hr : 0 < r) (hq : 0 < q) (hqk : q ≤ k)
    (hbudget : 3 * q + 1 ≤ 2 * (k - r + 1))
    (hthreshold :
      2 ^ (4 * (r + q)) * q ≤ vinogradovCubicScale N) :
    (vinogradovSolutionCountNat k (r + q) N : ℝ) <
      (((64 * N : ℕ) : ℝ) ^ (2 * (r + q))) *
        Real.sqrt
          (((2 : ℝ) ^ (4 * (r + q)) * (q.factorial : ℝ)) /
            (vinogradovCubicScale N : ℝ) ^ q) := by
  calc
    (vinogradovSolutionCountNat k (r + q) N : ℝ) <
        ((((2 * vinogradovCubicScale N) ^ 3 : ℕ) : ℝ) ^
            (2 * (r + q))) *
          Real.sqrt
            (((2 : ℝ) ^ (4 * (r + q)) * (q.factorial : ℝ)) /
              (vinogradovCubicScale N : ℝ) ^ q) :=
      vinogradovSolutionCountNat_lt_cubicEnvelopePowerSaving
        N k r q hr hq hqk hbudget hthreshold
    _ ≤ (((64 * N : ℕ) : ℝ) ^ (2 * (r + q))) *
          Real.sqrt
            (((2 : ℝ) ^ (4 * (r + q)) * (q.factorial : ℝ)) /
              (vinogradovCubicScale N : ℝ) ^ q) := by
      gcongr
      exact_mod_cast
        vinogradovCubicEnvelope_le_sixtyFour_mul N hN

private theorem sqrt_div_pow_six
    (A x : ℝ) (hA : 0 ≤ A) (hx : 0 ≤ x) :
    Real.sqrt (A / x ^ 6) =
      Real.sqrt A / x ^ 3 := by
  rw [Real.sqrt_div hA]
  congr 1
  rw [show x ^ 6 = (x ^ 3) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

/-- Choosing six conditioning variables turns the cubic-root gain into an
explicit inverse-linear factor in the interval length. -/
theorem vinogradovSolutionCountNat_lt_inverseLinearSavingSix
    (N k r : ℕ) (hN : 0 < N)
    (hr : 0 < r) (hk : 6 ≤ k)
    (hbudget : 19 ≤ 2 * (k - r + 1))
    (hthreshold :
      2 ^ (4 * (r + 6)) * 6 ≤ vinogradovCubicScale N) :
    (vinogradovSolutionCountNat k (r + 6) N : ℝ) <
      (((64 * N : ℕ) : ℝ) ^ (2 * (r + 6))) *
        (8 *
            Real.sqrt
              ((2 : ℝ) ^ (4 * (r + 6)) *
                (Nat.factorial 6 : ℝ)) /
          (N : ℝ)) := by
  let A : ℝ :=
    (2 : ℝ) ^ (4 * (r + 6)) * (Nat.factorial 6 : ℝ)
  let x : ℝ := (vinogradovCubicScale N : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hx : 0 < x := by
    dsimp [x, vinogradovCubicScale]
    positivity
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hsqrt :
      Real.sqrt (A / x ^ 6) =
        Real.sqrt A / x ^ 3 :=
    sqrt_div_pow_six A x hA hx.le
  have hNleEnvelope :
      (N : ℝ) ≤
        (((2 * vinogradovCubicScale N) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast le_vinogradovCubicEnvelope N
  have hNleEight :
      (N : ℝ) ≤ 8 * x ^ 3 := by
    calc
      (N : ℝ) ≤
          (((2 * vinogradovCubicScale N) ^ 3 : ℕ) : ℝ) :=
        hNleEnvelope
      _ = 8 * x ^ 3 := by
        dsimp [x]
        simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
        ring
  have hfrac :
      Real.sqrt A / x ^ 3 ≤
        8 * Real.sqrt A / (N : ℝ) := by
    apply (div_le_div_iff₀ (pow_pos hx 3) hNreal).2
    calc
      Real.sqrt A * (N : ℝ) ≤
          Real.sqrt A * (8 * x ^ 3) :=
        mul_le_mul_of_nonneg_left hNleEight (Real.sqrt_nonneg A)
      _ = (8 * Real.sqrt A) * x ^ 3 := by ring
  calc
    (vinogradovSolutionCountNat k (r + 6) N : ℝ) <
        (((64 * N : ℕ) : ℝ) ^ (2 * (r + 6))) *
          Real.sqrt
            (((2 : ℝ) ^ (4 * (r + 6)) *
                (Nat.factorial 6 : ℝ)) /
              (vinogradovCubicScale N : ℝ) ^ 6) := by
      exact
        vinogradovSolutionCountNat_lt_sixtyFourMulPowerSaving
          N k r 6 hN hr (by norm_num) hk hbudget hthreshold
    _ = (((64 * N : ℕ) : ℝ) ^ (2 * (r + 6))) *
          (Real.sqrt A / x ^ 3) := by
      rw [hsqrt]
    _ ≤ (((64 * N : ℕ) : ℝ) ^ (2 * (r + 6))) *
          (8 * Real.sqrt A / (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = (((64 * N : ℕ) : ℝ) ^ (2 * (r + 6))) *
          (8 *
              Real.sqrt
                ((2 : ℝ) ^ (4 * (r + 6)) *
                  (Nat.factorial 6 : ℝ)) /
            (N : ℝ)) := by
      rfl

private theorem mul_pow_mul_div_eq_mul_pow_pred
    (a b x : ℝ) (m : ℕ) (hx : x ≠ 0) (hm : 1 ≤ m) :
    (a * x) ^ m * (b / x) =
      (a ^ m * b) * x ^ (m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 :=
    ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  simp only [Nat.add_sub_cancel]
  have hpow : x ^ (n + 1) / x = x ^ n := by
    rw [pow_succ, mul_div_cancel_right₀ _ hx]
  rw [mul_pow]
  calc
    (a ^ (n + 1) * x ^ (n + 1)) * (b / x) =
        (a ^ (n + 1) * b) * (x ^ (n + 1) / x) := by ring
    _ = (a ^ (n + 1) * b) * x ^ n := by rw [hpow]

/-- In conventional mean-value notation, the six-variable specialization
saves one full power of `N` over the trivial exponent. -/
theorem vinogradovSolutionCountNat_lt_powerSavingOne
    (N k r : ℕ) (hN : 0 < N)
    (hr : 0 < r) (hk : 6 ≤ k)
    (hbudget : 19 ≤ 2 * (k - r + 1))
    (hthreshold :
      2 ^ (4 * (r + 6)) * 6 ≤ vinogradovCubicScale N) :
    (vinogradovSolutionCountNat k (r + 6) N : ℝ) <
      ((64 : ℝ) ^ (2 * (r + 6)) *
          (8 *
            Real.sqrt
              ((2 : ℝ) ^ (4 * (r + 6)) *
                (Nat.factorial 6 : ℝ)))) *
        (N : ℝ) ^ (2 * (r + 6) - 1) := by
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast hN.ne'
  calc
    (vinogradovSolutionCountNat k (r + 6) N : ℝ) <
        (((64 * N : ℕ) : ℝ) ^ (2 * (r + 6))) *
          (8 *
              Real.sqrt
                ((2 : ℝ) ^ (4 * (r + 6)) *
                  (Nat.factorial 6 : ℝ)) /
            (N : ℝ)) :=
      vinogradovSolutionCountNat_lt_inverseLinearSavingSix
        N k r hN hr hk hbudget hthreshold
    _ = ((64 : ℝ) ^ (2 * (r + 6)) *
          (8 *
            Real.sqrt
              ((2 : ℝ) ^ (4 * (r + 6)) *
                (Nat.factorial 6 : ℝ)))) *
        (N : ℝ) ^ (2 * (r + 6) - 1) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (mul_pow_mul_div_eq_mul_pow_pred
          (64 : ℝ)
          (8 *
            Real.sqrt
              ((2 : ℝ) ^ (4 * (r + 6)) *
                (Nat.factorial 6 : ℝ)))
          (N : ℝ) (2 * (r + 6)) hNne (by omega))

end

end ZeroFreeRegion.VinogradovKorobov
