import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedRecurrence
import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedHolder
import ZeroFreeRegion.VinogradovKorobov.VinogradovResidueConditioning

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The integer-congruence restricted Weyl sum used by the mixed-moment
machinery is exactly the corresponding standard residue-class sum. -/
theorem vinogradovMixedMainWeylSum_eq_residueClassSum
    (p a Q k X : ℕ) [NeZero (p ^ a)] [NeZero Q]
    (z : Fin (p ^ a)) (c : Fin k → ZMod Q) :
    vinogradovMixedMainWeylSum p a Q k X
        (((z.val + 1 : ℕ) : ℤ)) c =
      vinogradovResidueClassSum (p ^ a) X
        (((z.val + 1 : ℕ) : ZMod (p ^ a)))
        (fun n ↦ ZMod.stdAddChar (vinogradovPhaseMod Q c n)) := by
  classical
  unfold vinogradovMixedMainWeylSum vinogradovResidueClassSum
    vinogradovResidueClassFinset
  simp only [Finset.sum_filter]
  apply Fintype.sum_congr
  intro n
  have hres :
      Int.ModEq ((p : ℤ) ^ a) (((z.val + 1 : ℕ) : ℤ))
          (((n.val + 1 : ℕ) : ℤ)) ↔
        ((n.val + 1 : ℕ) : ZMod (p ^ a)) =
          ((z.val + 1 : ℕ) : ZMod (p ^ a)) := by
    constructor
    · intro h
      have h' := (ZMod.intCast_eq_intCast_iff
        (((z.val + 1 : ℕ) : ℤ)) (((n.val + 1 : ℕ) : ℤ))
        (p ^ a)).mpr (by simpa only [Nat.cast_pow] using h)
      simpa only [Int.cast_natCast] using h'.symm
    · intro h
      have hcast :
          ((((z.val + 1 : ℕ) : ℤ) : ZMod (p ^ a))) =
            ((((n.val + 1 : ℕ) : ℤ) : ZMod (p ^ a))) := by
        simpa only [Int.cast_natCast] using h.symm
      have h' := (ZMod.intCast_eq_intCast_iff
        (((z.val + 1 : ℕ) : ℤ)) (((n.val + 1 : ℕ) : ℤ))
        (p ^ a)).mp hcast
      simpa only [Nat.cast_pow] using h'
  simp only [hres]
  simp [vinogradovIntPhaseMod, vinogradovPhaseMod]

/-- The complete Weyl sum is the exact sum of the restricted main Weyl sums
over all one-based residue centers modulo `p^a`. -/
theorem vinogradovWeylSumMod_eq_sum_mixedMainWeylSum
    (p a Q k X : ℕ) [NeZero (p ^ a)] [NeZero Q]
    (c : Fin k → ZMod Q) :
    vinogradovWeylSumMod Q k X c =
      ∑ z : Fin (p ^ a),
        vinogradovMixedMainWeylSum p a Q k X
          (((z.val + 1 : ℕ) : ℤ)) c := by
  rw [vinogradovWeylSumMod]
  rw [← sum_vinogradovResidueClassSum_eq_full (p ^ a) X
    (fun n ↦ ZMod.stdAddChar (vinogradovPhaseMod Q c n))]
  simp_rw [vinogradovMixedMainWeylSum_eq_residueClassSum]
  let e := vinogradovCompleteResidueEquiv (p ^ a)
  have he (z : Fin (p ^ a)) :
      e z = ((z.val + 1 : ℕ) : ZMod (p ^ a)) := by
    simpa only [e, Nat.cast_add, Nat.cast_one] using
      (vinogradovCompleteResidueEquiv_apply (p ^ a) z)
  simpa only [he] using
    (e.sum_comp (fun ξ : ZMod (p ^ a) ↦
      vinogradovResidueClassSum (p ^ a) X ξ
        (fun n ↦ ZMod.stdAddChar (vinogradovPhaseMod Q c n)))).symm

/-- Applying finite Holder independently at two residue scales controls the
full `2(r+t)`-th power by the sum of the corresponding mixed main-block
products.  This is the upward conditioning inequality needed before the
restricted tail is reparameterized. -/
theorem norm_vinogradovWeylSumMod_pow_le_double_mixedMainConditioning
    (p a b Q k r t X : ℕ)
    [NeZero (p ^ a)] [NeZero (p ^ b)] [NeZero Q]
    (hr : 0 < r) (ht : 0 < t) (c : Fin k → ZMod Q) :
    ‖vinogradovWeylSumMod Q k X c‖ ^ (2 * (r + t)) ≤
      (((p ^ a : ℕ) : ℝ) ^ (2 * r - 1)) *
        (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
          ∑ xi : Fin (p ^ a), ∑ eta : Fin (p ^ b),
            ‖vinogradovMixedMainWeylSum p a Q k X
                (((xi.val + 1 : ℕ) : ℤ)) c‖ ^ (2 * r) *
              ‖vinogradovMixedMainWeylSum p b Q k X
                (((eta.val + 1 : ℕ) : ℤ)) c‖ ^ (2 * t) := by
  have hrpow : 1 ≤ 2 * r := by omega
  have htpow : 1 ≤ 2 * t := by omega
  have ha :
      ‖vinogradovWeylSumMod Q k X c‖ ^ (2 * r) ≤
        (((p ^ a : ℕ) : ℝ) ^ (2 * r - 1)) *
          ∑ xi : Fin (p ^ a),
            ‖vinogradovMixedMainWeylSum p a Q k X
              (((xi.val + 1 : ℕ) : ℤ)) c‖ ^ (2 * r) := by
    rw [vinogradovWeylSumMod_eq_sum_mixedMainWeylSum p a Q k X c]
    simpa only [Finset.card_univ, Fintype.card_fin,
      Nat.sub_add_cancel hrpow] using
      (norm_finset_sum_pow_le_card_mul_sum_norm_pow
        (Finset.univ : Finset (Fin (p ^ a)))
        (fun xi ↦ vinogradovMixedMainWeylSum p a Q k X
          (((xi.val + 1 : ℕ) : ℤ)) c)
        (2 * r - 1))
  have hb :
      ‖vinogradovWeylSumMod Q k X c‖ ^ (2 * t) ≤
        (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
          ∑ eta : Fin (p ^ b),
            ‖vinogradovMixedMainWeylSum p b Q k X
              (((eta.val + 1 : ℕ) : ℤ)) c‖ ^ (2 * t) := by
    rw [vinogradovWeylSumMod_eq_sum_mixedMainWeylSum p b Q k X c]
    simpa only [Finset.card_univ, Fintype.card_fin,
      Nat.sub_add_cancel htpow] using
      (norm_finset_sum_pow_le_card_mul_sum_norm_pow
        (Finset.univ : Finset (Fin (p ^ b)))
        (fun eta ↦ vinogradovMixedMainWeylSum p b Q k X
          (((eta.val + 1 : ℕ) : ℤ)) c)
        (2 * t - 1))
  calc
    ‖vinogradovWeylSumMod Q k X c‖ ^ (2 * (r + t)) =
        ‖vinogradovWeylSumMod Q k X c‖ ^ (2 * r) *
          ‖vinogradovWeylSumMod Q k X c‖ ^ (2 * t) := by
      rw [show 2 * (r + t) = 2 * r + 2 * t by omega, pow_add]
    _ ≤
        ((((p ^ a : ℕ) : ℝ) ^ (2 * r - 1)) *
          ∑ xi : Fin (p ^ a),
            ‖vinogradovMixedMainWeylSum p a Q k X
              (((xi.val + 1 : ℕ) : ℤ)) c‖ ^ (2 * r)) *
        ((((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
          ∑ eta : Fin (p ^ b),
            ‖vinogradovMixedMainWeylSum p b Q k X
              (((eta.val + 1 : ℕ) : ℤ)) c‖ ^ (2 * t)) :=
      mul_le_mul ha hb (by positivity) (by positivity)
    _ = (((p ^ a : ℕ) : ℝ) ^ (2 * r - 1)) *
        (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
          ∑ xi : Fin (p ^ a), ∑ eta : Fin (p ^ b),
            ‖vinogradovMixedMainWeylSum p a Q k X
                (((xi.val + 1 : ℕ) : ℤ)) c‖ ^ (2 * r) *
              ‖vinogradovMixedMainWeylSum p b Q k X
                (((eta.val + 1 : ℕ) : ℤ)) c‖ ^ (2 * t) := by
      have hsum :
          (∑ xi : Fin (p ^ a),
              ‖vinogradovMixedMainWeylSum p a Q k X
                (((xi.val + 1 : ℕ) : ℤ)) c‖ ^ (2 * r)) *
            (∑ eta : Fin (p ^ b),
              ‖vinogradovMixedMainWeylSum p b Q k X
                (((eta.val + 1 : ℕ) : ℤ)) c‖ ^ (2 * t)) =
            ∑ xi : Fin (p ^ a), ∑ eta : Fin (p ^ b),
              ‖vinogradovMixedMainWeylSum p a Q k X
                  (((xi.val + 1 : ℕ) : ℤ)) c‖ ^ (2 * r) *
                ‖vinogradovMixedMainWeylSum p b Q k X
                  (((eta.val + 1 : ℕ) : ℤ)) c‖ ^ (2 * t) := by
        rw [Finset.sum_mul]
        apply Fintype.sum_congr
        intro xi
        rw [Finset.mul_sum]
      rw [← hsum]
      ring

/-- The zero-based index of the `n`-th element in the one-based residue
class represented by `z` inside the complete interval of length `p^b * Y`. -/
def vinogradovResidueBlockIndex
    (p b Y : ℕ) [NeZero (p ^ b)]
    (z : Fin (p ^ b)) (n : Fin Y) : Fin (p ^ b * Y) := by
  refine ⟨z.val + p ^ b * n.val, ?_⟩
  calc
    z.val + p ^ b * n.val < p ^ b + p ^ b * n.val :=
      Nat.add_lt_add_right z.isLt _
    _ = p ^ b * (n.val + 1) := by ring
    _ ≤ p ^ b * Y :=
      Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr n.isLt)

/-- On a complete prime-power block, the residue-restricted main Weyl sum at
level `b` is exactly the affine tail Weyl sum with shifted center
`eta = center - p^b`. -/
theorem vinogradovMixedMainWeylSum_eq_shiftedTailWeylSum
    (p b Q k Y : ℕ) [NeZero (p ^ b)] [NeZero Q]
    (z : Fin (p ^ b)) (c : Fin k → ZMod Q) :
    vinogradovMixedMainWeylSum p b Q k (p ^ b * Y)
        (((z.val + 1 : ℕ) : ℤ)) c =
      vinogradovIntWeylSum Q k Y
        (vinogradovMixedTailValue p b Y
          ((((z.val + 1 : ℕ) : ℤ)) - (p : ℤ) ^ b)) c := by
  rw [vinogradovMixedMainWeylSum_eq_residueClassSum]
  unfold vinogradovResidueClassSum vinogradovIntWeylSum
  symm
  apply Finset.sum_bij
      (fun n _ ↦ vinogradovResidueBlockIndex p b Y z n)
  · intro n hn
    rw [mem_vinogradovResidueClassFinset]
    simp [vinogradovResidueBlockIndex, Nat.cast_add, Nat.cast_mul]
  · intro n₁ hn₁ n₂ hn₂ heq
    apply Fin.ext
    have hval := congrArg Fin.val heq
    simp only [vinogradovResidueBlockIndex] at hval
    have hmul : p ^ b * n₁.val = p ^ b * n₂.val :=
      Nat.add_left_cancel hval
    exact Nat.eq_of_mul_eq_mul_left (NeZero.pos (p ^ b)) hmul
  · intro m hm
    have hmres := (mem_vinogradovResidueClassFinset
      (p ^ b) (p ^ b * Y)
      (((z.val + 1 : ℕ) : ZMod (p ^ b))) m).mp hm
    have hbase :
        ((m.val : ℕ) : ZMod (p ^ b)) =
          ((z.val : ℕ) : ZMod (p ^ b)) := by
      have h := congrArg (fun w : ZMod (p ^ b) ↦ w - 1) hmres
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h
    have hrem : m.val % (p ^ b) = z.val := by
      have hval := congrArg ZMod.val hbase
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt z.isLt] using hval
    let n : Fin Y :=
      ⟨m.val / (p ^ b), Nat.div_lt_of_lt_mul m.isLt⟩
    refine ⟨n, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change z.val + p ^ b * (m.val / p ^ b) = m.val
    simpa only [hrem] using Nat.mod_add_div m.val (p ^ b)
  · intro n hn
    congr 1
    unfold vinogradovMixedTailValue
    simp only [vinogradovResidueBlockIndex, vinogradovIntPhaseMod,
      vinogradovPhaseMod, Fin.val_mk, Nat.cast_add, Nat.cast_mul,
      Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast]
    congr 1
    funext j
    congr 1
    push_cast
    ring

/-- The double conditioning inequality in the exact main-tail coordinates
used by the mixed moment.  The tail center is shifted by `p^b` so that its
affine enumeration covers the complete residue block without an endpoint
error. -/
theorem norm_vinogradovWeylSumMod_pow_le_shiftedMixedConditioning
    (p a b Q k r t Y : ℕ)
    [NeZero (p ^ a)] [NeZero (p ^ b)] [NeZero Q]
    (hr : 0 < r) (ht : 0 < t) (c : Fin k → ZMod Q) :
    ‖vinogradovWeylSumMod Q k (p ^ b * Y) c‖ ^ (2 * (r + t)) ≤
      (((p ^ a : ℕ) : ℝ) ^ (2 * r - 1)) *
        (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
          ∑ xi : Fin (p ^ a), ∑ eta : Fin (p ^ b),
            ‖vinogradovMixedMainWeylSum p a Q k (p ^ b * Y)
                (((xi.val + 1 : ℕ) : ℤ)) c‖ ^ (2 * r) *
              ‖vinogradovIntWeylSum Q k Y
                (vinogradovMixedTailValue p b Y
                  ((((eta.val + 1 : ℕ) : ℤ)) - (p : ℤ) ^ b)) c‖ ^
                    (2 * t) := by
  simpa only [vinogradovMixedMainWeylSum_eq_shiftedTailWeylSum] using
    (norm_vinogradovWeylSumMod_pow_le_double_mixedMainConditioning
      p a b Q k r t (p ^ b * Y) hr ht c)

/-- Pairing a complete Weyl sum with its conjugate identifies the normalized
Vinogradov moment with the normalized real average of the corresponding norm
powers. -/
theorem normalizedVinogradovMomentMod_eq_norm_average
    (Q k s X : ℕ) [NeZero Q] :
    normalizedVinogradovMomentMod Q k s X =
      (((((Q : ℝ)⁻¹ ^ k) *
        ∑ c : Fin k → ZMod Q,
          ‖vinogradovWeylSumMod Q k X c‖ ^ (2 * s) : ℝ)) : ℂ) := by
  unfold normalizedVinogradovMomentMod
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

/-- Sum of the mixed-moment norms over every pair of main centers and the
shifted tail centers that enumerate a complete block from its first point. -/
noncomputable def normalizedVinogradovShiftedAllCenterMixedMomentSum
    (p B a b k r t Y : ℕ) [NeZero (p ^ B)] : ℝ :=
  ∑ z : Fin (p ^ a) × Fin (p ^ b),
    ‖normalizedVinogradovMixedModConditionedMoment
      p B a b k r t (p ^ b * Y) Y
        (vinogradovCenterValue z.1)
        (vinogradovCenterValue z.2 - (p : ℤ) ^ b)‖

/-- Averaging the pointwise double-conditioning inequality over all
coefficient vectors bounds the ordinary Vinogradov moment by the shifted
all-center mixed-moment sum. -/
theorem norm_normalizedVinogradovMomentMod_le_shiftedAllCenterMixedMomentSum
    (p B a b k r t Y : ℕ)
    [NeZero (p ^ a)] [NeZero (p ^ b)] [NeZero (p ^ B)]
    (hr : 0 < r) (ht : 0 < t) :
    ‖normalizedVinogradovMomentMod
        (p ^ B) k (r + t) (p ^ b * Y)‖ ≤
      (((p ^ a : ℕ) : ℝ) ^ (2 * r - 1)) *
        (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
          normalizedVinogradovShiftedAllCenterMixedMomentSum
            p B a b k r t Y := by
  classical
  let q : ℝ := (((p ^ B : ℕ) : ℝ)⁻¹ ^ k)
  let A : ℝ :=
    (((p ^ a : ℕ) : ℝ) ^ (2 * r - 1)) *
      (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1))
  let F :
      (Fin k → ZMod (p ^ B)) → Fin (p ^ a) → Fin (p ^ b) → ℝ :=
    fun c xi eta ↦
      ‖vinogradovMixedMainWeylSum p a (p ^ B) k (p ^ b * Y)
          (vinogradovCenterValue xi) c‖ ^ (2 * r) *
        ‖vinogradovIntWeylSum (p ^ B) k Y
          (vinogradovMixedTailValue p b Y
            (vinogradovCenterValue eta - (p : ℤ) ^ b)) c‖ ^ (2 * t)
  have hpoint (c : Fin k → ZMod (p ^ B)) :
      ‖vinogradovWeylSumMod (p ^ B) k (p ^ b * Y) c‖ ^
          (2 * (r + t)) ≤
        A * ∑ xi : Fin (p ^ a), ∑ eta : Fin (p ^ b), F c xi eta := by
    simpa only [A, F, vinogradovCenterValue] using
      (norm_vinogradovWeylSumMod_pow_le_shiftedMixedConditioning
        p a b (p ^ B) k r t Y hr ht c)
  have hsum :
      (∑ c : Fin k → ZMod (p ^ B),
          ‖vinogradovWeylSumMod (p ^ B) k (p ^ b * Y) c‖ ^
            (2 * (r + t))) ≤
        ∑ c : Fin k → ZMod (p ^ B),
          A * ∑ xi : Fin (p ^ a), ∑ eta : Fin (p ^ b), F c xi eta := by
    exact Finset.sum_le_sum fun c _ ↦ hpoint c
  have hswap :
      (∑ c : Fin k → ZMod (p ^ B),
          ∑ xi : Fin (p ^ a), ∑ eta : Fin (p ^ b), F c xi eta) =
        ∑ xi : Fin (p ^ a), ∑ eta : Fin (p ^ b),
          ∑ c : Fin k → ZMod (p ^ B), F c xi eta := by
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro xi
    rw [Finset.sum_comm]
  have hmixed (xi : Fin (p ^ a)) (eta : Fin (p ^ b)) :
      ‖normalizedVinogradovMixedModConditionedMoment
          p B a b k r t (p ^ b * Y) Y
            (vinogradovCenterValue xi)
            (vinogradovCenterValue eta - (p : ℤ) ^ b)‖ =
        q * ∑ c : Fin k → ZMod (p ^ B), F c xi eta := by
    rw [normalizedVinogradovMixedModConditionedMoment_eq_norm_product_average]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  rw [normalizedVinogradovMomentMod_eq_norm_average]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  · change
      q * (∑ c : Fin k → ZMod (p ^ B),
        ‖vinogradovWeylSumMod (p ^ B) k (p ^ b * Y) c‖ ^
          (2 * (r + t))) ≤
        A * normalizedVinogradovShiftedAllCenterMixedMomentSum
          p B a b k r t Y
    calc
      q * (∑ c : Fin k → ZMod (p ^ B),
          ‖vinogradovWeylSumMod (p ^ B) k (p ^ b * Y) c‖ ^
            (2 * (r + t))) ≤
        q * ∑ c : Fin k → ZMod (p ^ B),
          A * ∑ xi : Fin (p ^ a), ∑ eta : Fin (p ^ b),
            F c xi eta :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = q * (A * ∑ c : Fin k → ZMod (p ^ B),
          ∑ xi : Fin (p ^ a), ∑ eta : Fin (p ^ b), F c xi eta) := by
        congr 2
        rw [Finset.mul_sum]
      _ = A * (q * ∑ xi : Fin (p ^ a), ∑ eta : Fin (p ^ b),
          ∑ c : Fin k → ZMod (p ^ B), F c xi eta) := by
        rw [hswap]
        ring
      _ = A * ∑ xi : Fin (p ^ a), ∑ eta : Fin (p ^ b),
          q * ∑ c : Fin k → ZMod (p ^ B), F c xi eta := by
        congr 1
        rw [Finset.mul_sum]
        apply Fintype.sum_congr
        intro xi
        rw [Finset.mul_sum]
      _ = A * normalizedVinogradovShiftedAllCenterMixedMomentSum
          p B a b k r t Y := by
        unfold normalizedVinogradovShiftedAllCenterMixedMomentSum
        rw [Fintype.sum_prod_type]
        simp_rw [hmixed]
  · positivity

/-- Shifting the tail center by `p^b` preserves every exact `p`-adic
center-difference scale strictly below `b`. -/
theorem exists_coprime_shifted_center_factor_of_exactScale
    (p a b gamma : ℕ) (hgb : gamma < b)
    (z : Fin (p ^ a) × Fin (p ^ b))
    (hz : z ∈ vinogradovCenterPairExactScaleSet p a b gamma) :
    ∃ omega : ℤ,
      vinogradovCenterValue z.1 -
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b) =
        omega * (p : ℤ) ^ gamma ∧
      IsCoprime (p : ℤ) omega := by
  rcases (mem_vinogradovCenterPairExactScaleSet_iff
    p a b gamma z).mp hz with ⟨omega, hcenter, homega⟩
  let d := b - (gamma + 1)
  refine ⟨omega + (p : ℤ) ^ d * p, ?_, ?_⟩
  · calc
      vinogradovCenterValue z.1 -
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b) =
        (vinogradovCenterValue z.1 - vinogradovCenterValue z.2) +
          (p : ℤ) ^ b := by ring
      _ = omega * (p : ℤ) ^ gamma + (p : ℤ) ^ b := by
        rw [hcenter]
      _ = (omega + (p : ℤ) ^ d * p) * (p : ℤ) ^ gamma := by
        have hexp : d + 1 + gamma = b := by
          dsimp [d]
          omega
        rw [← hexp]
        simp only [pow_add, pow_one]
        ring
  · exact (IsCoprime.add_mul_right_right_iff).mpr homega

/-- Shifted mixed-moment sum over one nonterminal exact center-difference
scale. -/
noncomputable def normalizedVinogradovShiftedExactScaleMixedMomentSum
    (p a b k r t Y gamma : ℕ) [Fact p.Prime] : ℝ := by
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  exact ∑ z ∈ vinogradovCenterPairExactScaleSet p a b gamma,
    ‖normalizedVinogradovMixedModConditionedMoment
      p ((k - r + 1) * b) a b k r t (p ^ b * Y) Y
        (vinogradovCenterValue z.1)
        (vinogradovCenterValue z.2 - (p : ℤ) ^ b)‖

/-- The existing pointwise far-scale recurrence applies uniformly to the
shifted center sum on every scale `gamma < b`. -/
theorem
    normalizedVinogradovShiftedExactScaleMixedMomentSum_le_farScaleMoment
    (p a b k r t Y gamma : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b) (hgb : gamma < b)
    (hgammaa : gamma ≤ a)
    (hbudget : gamma * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hscale :
      p ^ b * Y ≤ p ^ a * p ^ vinogradovFarScale k r a b gamma) :
    normalizedVinogradovShiftedExactScaleMixedMomentSum
        p a b k r t Y gamma ≤
      (vinogradovCenterPairExactScaleSet p a b gamma).card *
        (‖normalizedVinogradovMomentMod
          (p ^ vinogradovFarScale k r a b gamma) r r
            (p ^ vinogradovFarScale k r a b gamma)‖ *
          (Y ^ (2 * t) : ℝ)) := by
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p ^ vinogradovFarScale k r a b gamma) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  unfold normalizedVinogradovShiftedExactScaleMixedMomentSum
  calc
    (∑ z ∈ vinogradovCenterPairExactScaleSet p a b gamma,
      ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * b) a b k r t (p ^ b * Y) Y
          (vinogradovCenterValue z.1)
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b)‖) ≤
      ∑ _z ∈ vinogradovCenterPairExactScaleSet p a b gamma,
        ‖normalizedVinogradovMomentMod
          (p ^ vinogradovFarScale k r a b gamma) r r
            (p ^ vinogradovFarScale k r a b gamma)‖ *
          (Y ^ (2 * t) : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      rcases exists_coprime_shifted_center_factor_of_exactScale
        p a b gamma hgb z hz with ⟨omega, hcenter, homega⟩
      exact norm_normalizedVinogradovMixedModConditionedMoment_le_farScaleMoment
        p a b k r t (p ^ b * Y) Y gamma
          (vinogradovCenterValue z.1)
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b) omega
          hrk hkp hb hgammaa hbudget htail hcenter homega hscale
    _ = (vinogradovCenterPairExactScaleSet p a b gamma).card *
        (‖normalizedVinogradovMomentMod
          (p ^ vinogradovFarScale k r a b gamma) r r
            (p ^ vinogradovFarScale k r a b gamma)‖ *
          (Y ^ (2 * t) : ℝ)) := by
      simp

/-- Shifted mixed-moment sum on the terminal layer where the two residue
centers are congruent modulo `p^b`. -/
noncomputable def normalizedVinogradovShiftedTerminalMixedMomentSum
    (p a b k r t Y : ℕ) [Fact p.Prime] : ℝ := by
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  exact ∑ z ∈ vinogradovCenterPairCongruentSet p a b b,
    ‖normalizedVinogradovMixedModConditionedMoment
      p ((k - r + 1) * b) a b k r t (p ^ b * Y) Y
        (vinogradovCenterValue z.1)
        (vinogradovCenterValue z.2 - (p : ℤ) ^ b)‖

/-- The shifted terminal layer is bounded by its honest ambient tuple count. -/
theorem normalizedVinogradovShiftedTerminalMixedMomentSum_le_trivial
    (p a b k r t Y : ℕ) [Fact p.Prime] :
    normalizedVinogradovShiftedTerminalMixedMomentSum
        p a b k r t Y ≤
      (p ^ a : ℕ) *
        ((((p ^ b * Y) ^ (2 * r) * Y ^ (2 * t) : ℕ)) : ℝ) := by
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  unfold normalizedVinogradovShiftedTerminalMixedMomentSum
  calc
    (∑ z ∈ vinogradovCenterPairCongruentSet p a b b,
      ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * b) a b k r t (p ^ b * Y) Y
          (vinogradovCenterValue z.1)
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b)‖) ≤
      ∑ _z ∈ vinogradovCenterPairCongruentSet p a b b,
        ((((p ^ b * Y) ^ (2 * r) * Y ^ (2 * t) : ℕ)) : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      exact norm_normalizedVinogradovMixedModConditionedMoment_le_trivial
        p ((k - r + 1) * b) a b k r t (p ^ b * Y) Y
          (vinogradovCenterValue z.1)
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b)
    _ = (p ^ a : ℕ) *
        ((((p ^ b * Y) ^ (2 * r) * Y ^ (2 * t) : ℕ)) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        card_vinogradovCenterPairCongruentSet_self]

/-- The shifted all-center sum has the same exact-scale partition as the
unshifted sum, because the partition is taken on the underlying residue
indices before evaluating the mixed moment. -/
theorem
    normalizedVinogradovShiftedAllCenterMixedMomentSum_eq_exactScales_add_terminal
    (p a b k r t Y : ℕ) [Fact p.Prime] :
    normalizedVinogradovShiftedAllCenterMixedMomentSum
        p ((k - r + 1) * b) a b k r t Y =
      (∑ gamma ∈ Finset.range b,
        normalizedVinogradovShiftedExactScaleMixedMomentSum
          p a b k r t Y gamma) +
        normalizedVinogradovShiftedTerminalMixedMomentSum
          p a b k r t Y := by
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  change
    (∑ z : Fin (p ^ a) × Fin (p ^ b),
      ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * b) a b k r t (p ^ b * Y) Y
          (vinogradovCenterValue z.1)
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b)‖) =
      (∑ gamma ∈ Finset.range b,
        ∑ z ∈ vinogradovCenterPairExactScaleSet p a b gamma,
          ‖normalizedVinogradovMixedModConditionedMoment
            p ((k - r + 1) * b) a b k r t (p ^ b * Y) Y
              (vinogradovCenterValue z.1)
              (vinogradovCenterValue z.2 - (p : ℤ) ^ b)‖) +
        ∑ z ∈ vinogradovCenterPairCongruentSet p a b b,
          ‖normalizedVinogradovMixedModConditionedMoment
            p ((k - r + 1) * b) a b k r t (p ^ b * Y) Y
              (vinogradovCenterValue z.1)
              (vinogradovCenterValue z.2 - (p : ℤ) ^ b)‖
  exact sum_univ_centerPairs_eq_exactScales_add_terminal
    p a b b (fun z ↦
      ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * b) a b k r t (p ^ b * Y) Y
          (vinogradovCenterValue z.1)
          (vinogradovCenterValue z.2 - (p : ℤ) ^ b)‖)

/-- Global shifted-center recurrence: every nonterminal scale is controlled
by its far-scale ordinary moment, and the terminal layer retains the ambient
tuple bound. -/
theorem
    normalizedVinogradovShiftedAllCenterMixedMomentSum_le_exactScales_add_terminal
    (p a b k r t Y : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b)
    (hgammaa : ∀ gamma < b, gamma ≤ a)
    (hbudget : ∀ gamma < b,
      gamma * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hscale : ∀ gamma < b,
      p ^ b * Y ≤ p ^ a * p ^ vinogradovFarScale k r a b gamma) :
    normalizedVinogradovShiftedAllCenterMixedMomentSum
        p ((k - r + 1) * b) a b k r t Y ≤
      (∑ gamma ∈ Finset.range b,
        (vinogradovCenterPairExactScaleSet p a b gamma).card *
          (‖normalizedVinogradovMomentMod
            (p ^ vinogradovFarScale k r a b gamma) r r
              (p ^ vinogradovFarScale k r a b gamma)‖ *
            (Y ^ (2 * t) : ℝ))) +
        (p ^ a : ℕ) *
          ((((p ^ b * Y) ^ (2 * r) * Y ^ (2 * t) : ℕ)) : ℝ) := by
  rw [
    normalizedVinogradovShiftedAllCenterMixedMomentSum_eq_exactScales_add_terminal]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro gamma hgamma
    have hgb : gamma < b := Finset.mem_range.mp hgamma
    exact
      normalizedVinogradovShiftedExactScaleMixedMomentSum_le_farScaleMoment
        p a b k r t Y gamma hrk hkp hb hgb
          (hgammaa gamma hgb) (hbudget gamma hgb) htail
          (hscale gamma hgb)
  · exact normalizedVinogradovShiftedTerminalMixedMomentSum_le_trivial
      p a b k r t Y

/-- First complete one-step recurrence from an ordinary Vinogradov moment:
double conditioning produces shifted mixed blocks, exact center scales feed
back into lower-degree ordinary moments, and only the terminal layer is left
with a trivial bound. -/
theorem norm_normalizedVinogradovMomentMod_le_shiftedExactScales_add_terminal
    (p a b k r t Y : ℕ) [Fact p.Prime]
    (hr : 0 < r) (ht : 0 < t)
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b)
    (hgammaa : ∀ gamma < b, gamma ≤ a)
    (hbudget : ∀ gamma < b,
      gamma * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hscale : ∀ gamma < b,
      p ^ b * Y ≤ p ^ a * p ^ vinogradovFarScale k r a b gamma) :
    ‖normalizedVinogradovMomentMod
        (p ^ ((k - r + 1) * b)) k (r + t) (p ^ b * Y)‖ ≤
      (((p ^ a : ℕ) : ℝ) ^ (2 * r - 1)) *
        (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
          ((∑ gamma ∈ Finset.range b,
            (vinogradovCenterPairExactScaleSet p a b gamma).card *
              (‖normalizedVinogradovMomentMod
                (p ^ vinogradovFarScale k r a b gamma) r r
                  (p ^ vinogradovFarScale k r a b gamma)‖ *
                (Y ^ (2 * t) : ℝ))) +
            (p ^ a : ℕ) *
              ((((p ^ b * Y) ^ (2 * r) * Y ^ (2 * t) : ℕ)) : ℝ)) := by
  letI : NeZero (p ^ a) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p ^ b) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  calc
    ‖normalizedVinogradovMomentMod
        (p ^ ((k - r + 1) * b)) k (r + t) (p ^ b * Y)‖ ≤
      (((p ^ a : ℕ) : ℝ) ^ (2 * r - 1)) *
        (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
          normalizedVinogradovShiftedAllCenterMixedMomentSum
            p ((k - r + 1) * b) a b k r t Y :=
      norm_normalizedVinogradovMomentMod_le_shiftedAllCenterMixedMomentSum
        p ((k - r + 1) * b) a b k r t Y hr ht
    _ ≤ (((p ^ a : ℕ) : ℝ) ^ (2 * r - 1)) *
        (((p ^ b : ℕ) : ℝ) ^ (2 * t - 1)) *
          ((∑ gamma ∈ Finset.range b,
            (vinogradovCenterPairExactScaleSet p a b gamma).card *
              (‖normalizedVinogradovMomentMod
                (p ^ vinogradovFarScale k r a b gamma) r r
                  (p ^ vinogradovFarScale k r a b gamma)‖ *
                (Y ^ (2 * t) : ℝ))) +
            (p ^ a : ℕ) *
              ((((p ^ b * Y) ^ (2 * r) * Y ^ (2 * t) : ℕ)) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (normalizedVinogradovShiftedAllCenterMixedMomentSum_le_exactScales_add_terminal
          p a b k r t Y hrk hkp hb hgammaa hbudget htail hscale)
        (by positivity)

end

end ZeroFreeRegion.VinogradovKorobov
