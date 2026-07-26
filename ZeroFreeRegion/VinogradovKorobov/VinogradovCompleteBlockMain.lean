import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedDecomposition
import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedTailMoment

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- On a complete interval of length `p^a * Y`, a fixed main residue class
contains only `Y` choices per coordinate.  Forgetting the Vinogradov equations
therefore bounds the restricted main solution-pair count by `Y^(2s)`. -/
theorem card_vinogradovMixedMainSolutionPairSet_completeBlock_le
    (p B a k s Y : ℕ) [NeZero (p ^ a)] [NeZero (p ^ B)]
    (z : Fin (p ^ a)) :
    (vinogradovMixedMainSolutionPairSet p B a k s (p ^ a * Y)
      (((z.val + 1 : ℕ) : ℤ))).card ≤ Y ^ (2 * s) := by
  classical
  let R := vinogradovResidueClassFinset (p ^ a) (p ^ a * Y)
    (((z.val + 1 : ℕ) : ZMod (p ^ a)))
  let T := Fintype.piFinset (fun _ : Fin s ↦ R)
  let P := T ×ˢ T
  have hres (m : Fin (p ^ a * Y))
      (hm : Int.ModEq ((p : ℤ) ^ a) (((z.val + 1 : ℕ) : ℤ))
        (((m.val + 1 : ℕ) : ℤ))) :
      m ∈ R := by
    rw [show R = vinogradovResidueClassFinset (p ^ a) (p ^ a * Y)
      (((z.val + 1 : ℕ) : ZMod (p ^ a))) from rfl]
    rw [mem_vinogradovResidueClassFinset]
    have hcast := (ZMod.intCast_eq_intCast_iff
      (((z.val + 1 : ℕ) : ℤ)) (((m.val + 1 : ℕ) : ℤ))
      (p ^ a)).mpr (by simpa only [Nat.cast_pow] using hm)
    simpa only [Int.cast_natCast] using hcast.symm
  have hsubset :
      vinogradovMixedMainSolutionPairSet p B a k s (p ^ a * Y)
          (((z.val + 1 : ℕ) : ℤ)) ⊆ P := by
    intro xy hxy
    rw [Finset.mem_product]
    have hmem := (mem_vinogradovMixedMainSolutionPairSet_iff
      p B a k s (p ^ a * Y) (((z.val + 1 : ℕ) : ℤ)) xy).mp hxy
    constructor
    · rw [show T = Fintype.piFinset (fun _ : Fin s ↦ R) from rfl]
      rw [Fintype.mem_piFinset]
      intro i
      exact hres (xy.1 i) (hmem.1 i)
    · rw [show T = Fintype.piFinset (fun _ : Fin s ↦ R) from rfl]
      rw [Fintype.mem_piFinset]
      intro i
      exact hres (xy.2 i) (hmem.2.1 i)
  have hRcard : R.card = Y := by
    simpa only [R, Nat.cast_add, Nat.cast_one] using
      card_vinogradovResidueClassFinset_completeBlock p a Y z
  calc
    (vinogradovMixedMainSolutionPairSet p B a k s (p ^ a * Y)
        (((z.val + 1 : ℕ) : ℤ))).card ≤ P.card :=
      Finset.card_le_card hsubset
    _ = Y ^ (2 * s) := by
      simp [P, T, hRcard, ← pow_add, show s + s = 2 * s by omega]

/-- The Cauchy-separated mixed moment retains the factorial tail saving while
the main factor is counted at its actual residue-block length `Z`, rather than
at the ambient interval length `p^a * Z`. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_completeMainBlock_factorialTail
    (p B a b k r t Y Z n q : ℕ)
    [NeZero (p ^ a)] [NeZero (p ^ B)]
    (hp : p ≠ 0) (hqk : q ≤ k) (hsplit : n + q = 2 * t)
    (hnowrap : VinogradovResidualTailNoWrap p B b q Y)
    (z : Fin (p ^ a)) (eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p B a b k r t (p ^ a * Z) Y
          (((z.val + 1 : ℕ) : ℤ)) eta‖ ^ 2 ≤
      (Z : ℝ) ^ (4 * r) *
        ((q.factorial : ℝ) * (Y : ℝ) ^ (2 * n + q)) := by
  have h :=
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_factorialTail
      p B a b k r t (p ^ a * Z) Y n q hp hqk hsplit hnowrap
        (((z.val + 1 : ℕ) : ℤ)) eta
  rw [normalizedVinogradovMixedMainNormMoment_eq_solutionPairSetCard] at h
  have hmainNat :=
    card_vinogradovMixedMainSolutionPairSet_completeBlock_le
      p B a k (2 * r) Z z
  have hmain :
      ((vinogradovMixedMainSolutionPairSet p B a k (2 * r)
        (p ^ a * Z) (((z.val + 1 : ℕ) : ℤ))).card : ℝ) ≤
          (Z : ℝ) ^ (4 * r) := by
    have hmainCast :
        ((vinogradovMixedMainSolutionPairSet p B a k (2 * r)
          (p ^ a * Z) (((z.val + 1 : ℕ) : ℤ))).card : ℝ) ≤
            ((Z ^ (2 * (2 * r)) : ℕ) : ℝ) := by
      exact_mod_cast hmainNat
    simpa only [Nat.cast_pow, show 2 * (2 * r) = 4 * r by omega] using hmainCast
  exact h.trans
    (mul_le_mul_of_nonneg_right hmain (by positivity))

/-- At the scale used by the upward recurrence, a complete main block modulo
`p^2` has residual length `p`.  Combining that exact block count with `q`
recoverable tail variables saves `q` powers of `p` in the squared mixed
moment. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_primeCompleteBlock_balancedTail
    (p k r q : ℕ) [Fact p.Prime]
    (hqk : q ≤ k) (hqp : q < p)
    (hbudget : 3 * q + 1 ≤ 2 * (k - r + 1))
    (z : Fin (p ^ 2)) (eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * 2) 2 2 k r q
          (p ^ 2 * p) p (((z.val + 1 : ℕ) : ℤ)) eta‖ ^ 2 ≤
      (p : ℝ) ^ (4 * r) *
        ((q.factorial : ℝ) * (p : ℝ) ^ (3 * q)) := by
  letI : NeZero (p ^ 2) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p ^ ((k - r + 1) * 2)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hdegree : 2 * q ≤ (k - r + 1) * 2 := by omega
  have htailExponent :
      q + 1 ≤ (k - r + 1) * 2 - 2 * q := by
    omega
  have hcoefficient :
      q * p ^ q < p * p ^ q :=
    Nat.mul_lt_mul_of_pos_right hqp (pow_pos hp0 q)
  have htop :
      q * p ^ q < p ^ ((k - r + 1) * 2 - 2 * q) := by
    calc
      q * p ^ q < p * p ^ q := hcoefficient
      _ = p ^ (q + 1) := by simp [pow_succ, Nat.mul_comm]
      _ ≤ p ^ ((k - r + 1) * 2 - 2 * q) :=
        Nat.pow_le_pow_right hp0 htailExponent
  have hnowrap :
      VinogradovResidualTailNoWrap
        p ((k - r + 1) * 2) 2 q p :=
    VinogradovResidualTailNoWrap.of_mixed_recurrence_top_degree
      p 2 k r q p hp0 hp0 hdegree htop
  simpa only [show 2 * q + q = 3 * q by omega] using
    (norm_normalizedVinogradovMixedModConditionedMoment_sq_le_completeMainBlock_factorialTail
      p ((k - r + 1) * 2) 2 2 k r q p p q q
        (Fact.out : p.Prime).ne_zero hqk (by omega) hnowrap z eta)

/-- The complete-block mixed estimate feeds back into the ordinary moment at
length `p^3`.  The displayed bound keeps the square root visible; squaring it
reveals a saving of one factor `p^q` over the squared trivial exponent. -/
theorem norm_normalizedVinogradovMomentMod_le_primeCubic_completeBlockSaving
    (p k r q : ℕ) [Fact p.Prime]
    (hr : 0 < r) (hq : 0 < q) (hqk : q ≤ k) (hqp : q < p)
    (hbudget : 3 * q + 1 ≤ 2 * (k - r + 1)) :
    ‖normalizedVinogradovMomentMod
        (p ^ ((k - r + 1) * 2)) k (r + q) (p ^ 2 * p)‖ ≤
      (((p ^ 2 : ℕ) : ℝ) ^ (2 * r - 1)) *
        (((p ^ 2 : ℕ) : ℝ) ^ (2 * q - 1)) *
          (((p ^ 2 : ℕ) : ℝ) * ((p ^ 2 : ℕ) : ℝ) *
            Real.sqrt
              ((p : ℝ) ^ (4 * r) *
                ((q.factorial : ℝ) * (p : ℝ) ^ (3 * q)))) := by
  letI : NeZero (p ^ 2) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p ^ ((k - r + 1) * 2)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let C : ℝ :=
    (p : ℝ) ^ (4 * r) *
      ((q.factorial : ℝ) * (p : ℝ) ^ (3 * q))
  have hpoint (z : Fin (p ^ 2) × Fin (p ^ 2)) :
      ‖normalizedVinogradovMixedModConditionedMoment
          p ((k - r + 1) * 2) 2 2 k r q
            (p ^ 2 * p) p
              (vinogradovCenterValue z.1)
              (vinogradovCenterValue z.2 - (p : ℤ) ^ 2)‖ ≤
        Real.sqrt C := by
    exact Real.le_sqrt_of_sq_le
      (norm_normalizedVinogradovMixedModConditionedMoment_sq_le_primeCompleteBlock_balancedTail
        p k r q hqk hqp hbudget z.1
          (vinogradovCenterValue z.2 - (p : ℤ) ^ 2))
  have hsum :
      normalizedVinogradovShiftedAllCenterMixedMomentSum
          p ((k - r + 1) * 2) 2 2 k r q p ≤
        (((p ^ 2 : ℕ) : ℝ) * ((p ^ 2 : ℕ) : ℝ)) *
          Real.sqrt C := by
    unfold normalizedVinogradovShiftedAllCenterMixedMomentSum
    calc
      (∑ z : Fin (p ^ 2) × Fin (p ^ 2),
        ‖normalizedVinogradovMixedModConditionedMoment
          p ((k - r + 1) * 2) 2 2 k r q (p ^ 2 * p) p
            (vinogradovCenterValue z.1)
            (vinogradovCenterValue z.2 - (p : ℤ) ^ 2)‖) ≤
          ∑ _z : Fin (p ^ 2) × Fin (p ^ 2), Real.sqrt C := by
            exact Finset.sum_le_sum fun z _ ↦ hpoint z
      _ = (((p ^ 2 : ℕ) : ℝ) * ((p ^ 2 : ℕ) : ℝ)) *
          Real.sqrt C := by simp [mul_assoc]
  have hbridge :=
    norm_normalizedVinogradovMomentMod_le_shiftedAllCenterMixedMomentSum
      p ((k - r + 1) * 2) 2 2 k r q p hr hq
  exact hbridge.trans
    (mul_le_mul_of_nonneg_left hsum (by positivity))

/-- Squared form of the complete-block ordinary-moment estimate.  The
exponent `12r + 11q` is one factor `p^q` below the squared trivial exponent
`12r + 12q` for a `2(r+q)`-th moment on a block of length `p^3`. -/
theorem norm_normalizedVinogradovMomentMod_sq_le_primeCubic_completeBlockSaving
    (p k r q : ℕ) [Fact p.Prime]
    (hr : 0 < r) (hq : 0 < q) (hqk : q ≤ k) (hqp : q < p)
    (hbudget : 3 * q + 1 ≤ 2 * (k - r + 1)) :
    ‖normalizedVinogradovMomentMod
        (p ^ ((k - r + 1) * 2)) k (r + q) (p ^ 2 * p)‖ ^ 2 ≤
      (q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q) := by
  let C : ℝ :=
    (p : ℝ) ^ (4 * r) *
      ((q.factorial : ℝ) * (p : ℝ) ^ (3 * q))
  let A : ℝ :=
    (((p ^ 2 : ℕ) : ℝ) ^ (2 * r - 1)) *
      (((p ^ 2 : ℕ) : ℝ) ^ (2 * q - 1)) *
        (((p ^ 2 : ℕ) : ℝ) * ((p ^ 2 : ℕ) : ℝ) * Real.sqrt C)
  have hbound :
      ‖normalizedVinogradovMomentMod
          (p ^ ((k - r + 1) * 2)) k (r + q) (p ^ 2 * p)‖ ≤ A := by
    simpa [A, C] using
      norm_normalizedVinogradovMomentMod_le_primeCubic_completeBlockSaving
        p k r q hr hq hqk hqp hbudget
  have hrpow :
      (((p : ℝ) ^ 2) ^ (2 * r - 1)) * ((p : ℝ) ^ 2) =
        ((p : ℝ) ^ 2) ^ (2 * r) := by
    rw [← pow_succ]
    congr 1
    omega
  have hqpow :
      (((p : ℝ) ^ 2) ^ (2 * q - 1)) * ((p : ℝ) ^ 2) =
        ((p : ℝ) ^ 2) ^ (2 * q) := by
    rw [← pow_succ]
    congr 1
    omega
  have hA :
      A = (p : ℝ) ^ (4 * r + 4 * q) * Real.sqrt C := by
    dsimp [A]
    simp only [Nat.cast_pow]
    calc
      ((p : ℝ) ^ 2) ^ (2 * r - 1) *
            ((p : ℝ) ^ 2) ^ (2 * q - 1) *
          (((p : ℝ) ^ 2) * (p : ℝ) ^ 2 * Real.sqrt C) =
        ((((p : ℝ) ^ 2) ^ (2 * r - 1)) * (p : ℝ) ^ 2) *
          ((((p : ℝ) ^ 2) ^ (2 * q - 1)) * (p : ℝ) ^ 2) *
            Real.sqrt C := by ring
      _ = ((p : ℝ) ^ 2) ^ (2 * r) *
          ((p : ℝ) ^ 2) ^ (2 * q) * Real.sqrt C := by
            rw [hrpow, hqpow]
      _ = ((p : ℝ) ^ 2) ^ (2 * r + 2 * q) * Real.sqrt C := by
            rw [← pow_add]
      _ = (p : ℝ) ^ (2 * (2 * r + 2 * q)) * Real.sqrt C := by
            rw [← pow_mul]
      _ = (p : ℝ) ^ (4 * r + 4 * q) * Real.sqrt C := by
            congr 2
            omega
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hA_sq :
      A ^ 2 = (q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q) := by
    rw [hA, mul_pow, Real.sq_sqrt hC]
    rw [← pow_mul]
    dsimp [C]
    calc
      (p : ℝ) ^ ((4 * r + 4 * q) * 2) *
          ((p : ℝ) ^ (4 * r) *
            ((q.factorial : ℝ) * (p : ℝ) ^ (3 * q))) =
        (q.factorial : ℝ) *
          (((p : ℝ) ^ ((4 * r + 4 * q) * 2) *
            (p : ℝ) ^ (4 * r)) * (p : ℝ) ^ (3 * q)) := by ring
      _ = (q.factorial : ℝ) *
          (p : ℝ) ^ (((4 * r + 4 * q) * 2 + 4 * r) + 3 * q) := by
            rw [← pow_add, ← pow_add]
      _ = (q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q) := by
            congr 2
            omega
  calc
    ‖normalizedVinogradovMomentMod
        (p ^ ((k - r + 1) * 2)) k (r + q) (p ^ 2 * p)‖ ^ 2 ≤
      A ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = (q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q) := hA_sq

end

end ZeroFreeRegion.VinogradovKorobov
