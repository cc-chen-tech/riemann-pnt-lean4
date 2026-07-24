import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedRecurrence
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

end

end ZeroFreeRegion.VinogradovKorobov
