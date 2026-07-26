import ZeroFreeRegion.VinogradovKorobov.VinogradovCoupledTailRecurrence
import ZeroFreeRegion.VinogradovKorobov.VinogradovCompleteBlockMain
import ZeroFreeRegion.VinogradovKorobov.VinogradovTailIteration

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The endpoint-sensitive tree obtained by iterating the coupled mixed
tail recurrence.  The main block and its center remain fixed, while every
tail residue digit updates the tail length and center. -/
noncomputable def normalizedVinogradovMixedCoupledTailIteratedNormMoment
    (p B a k r t X : ℕ) [Fact p.Prime] [NeZero (p ^ B)] :
    ℕ → ℕ → ℕ → ℤ → ℤ → ℝ
  | 0, b, Y, xi, eta =>
      ‖normalizedVinogradovMixedModConditionedMoment
        p B a b k r t X Y xi eta‖
  | d + 1, b, Y, xi, eta =>
      ∑ rho : ZMod p,
        normalizedVinogradovMixedCoupledTailIteratedNormMoment
          p B a k r t X d (b + 1)
            (vinogradovTailResidueLength p Y rho) xi
            (vinogradovTailResidueRefinedCenter p b eta rho)

@[simp] theorem normalizedVinogradovMixedCoupledTailIteratedNormMoment_zero
    (p B a b k r t X Y : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (xi eta : ℤ) :
    normalizedVinogradovMixedCoupledTailIteratedNormMoment
        p B a k r t X 0 b Y xi eta =
      ‖normalizedVinogradovMixedModConditionedMoment
        p B a b k r t X Y xi eta‖ := by
  rfl

@[simp] theorem normalizedVinogradovMixedCoupledTailIteratedNormMoment_succ
    (p B a b k r t X Y d : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (xi eta : ℤ) :
    normalizedVinogradovMixedCoupledTailIteratedNormMoment
        p B a k r t X (d + 1) b Y xi eta =
      ∑ rho : ZMod p,
        normalizedVinogradovMixedCoupledTailIteratedNormMoment
          p B a k r t X d (b + 1)
            (vinogradovTailResidueLength p Y rho) xi
            (vinogradovTailResidueRefinedCenter p b eta rho) := by
  rfl

/-- Iterating the coupled one-digit recurrence `d` times retains the original
mixed moment order.  The only accumulated Holder cost is
`p^(d * (2t - 1))`. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_le_coupledTailIterated
    (p B a b k r t X Y d : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (ht : 0 < t) (xi eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p B a b k r t X Y xi eta‖ ≤
      (p : ℝ) ^ (d * (2 * t - 1)) *
        normalizedVinogradovMixedCoupledTailIteratedNormMoment
          p B a k r t X d b Y xi eta := by
  induction d generalizing b Y eta with
  | zero =>
      simp
  | succ d ih =>
      have hstep :=
        norm_normalizedVinogradovMixedModConditionedMoment_le_nextScaleCoupledSum
          p B a b k r t X Y ht xi eta
      have hleaves :
          (∑ rho : ZMod p,
            ‖normalizedVinogradovMixedModConditionedMoment
              p B a (b + 1) k r t X
                (vinogradovTailResidueLength p Y rho) xi
                (vinogradovTailResidueRefinedCenter p b eta rho)‖) ≤
            ∑ rho : ZMod p,
              (p : ℝ) ^ (d * (2 * t - 1)) *
                normalizedVinogradovMixedCoupledTailIteratedNormMoment
                  p B a k r t X d (b + 1)
                    (vinogradovTailResidueLength p Y rho) xi
                    (vinogradovTailResidueRefinedCenter p b eta rho) := by
        apply Finset.sum_le_sum
        intro rho hrho
        exact ih
          (b := b + 1)
          (Y := vinogradovTailResidueLength p Y rho)
          (eta := vinogradovTailResidueRefinedCenter p b eta rho)
      calc
        ‖normalizedVinogradovMixedModConditionedMoment
            p B a b k r t X Y xi eta‖ ≤
          (p : ℝ) ^ (2 * t - 1) *
            ∑ rho : ZMod p,
              ‖normalizedVinogradovMixedModConditionedMoment
                p B a (b + 1) k r t X
                  (vinogradovTailResidueLength p Y rho) xi
                  (vinogradovTailResidueRefinedCenter p b eta rho)‖ :=
          hstep
        _ ≤ (p : ℝ) ^ (2 * t - 1) *
            ∑ rho : ZMod p,
              (p : ℝ) ^ (d * (2 * t - 1)) *
                normalizedVinogradovMixedCoupledTailIteratedNormMoment
                  p B a k r t X d (b + 1)
                    (vinogradovTailResidueLength p Y rho) xi
                    (vinogradovTailResidueRefinedCenter p b eta rho) :=
          mul_le_mul_of_nonneg_left hleaves (by positivity)
        _ = (p : ℝ) ^ ((d + 1) * (2 * t - 1)) *
            normalizedVinogradovMixedCoupledTailIteratedNormMoment
              p B a k r t X (d + 1) b Y xi eta := by
          rw [normalizedVinogradovMixedCoupledTailIteratedNormMoment_succ]
          rw [← Finset.mul_sum, ← mul_assoc, ← pow_add]
          congr 2
          ring

/-- A uniform bound `L` for every depth-`d` mixed leaf sums to at most
`p^d * L` over the coupled endpoint-sensitive residue tree. -/
theorem
    normalizedVinogradovMixedCoupledTailIteratedNormMoment_le_uniformLeaf
    (p B a b k r t X Y d : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (xi : ℤ)
    (L : ℝ)
    (hleaf :
      ∀ Y' eta',
        Y' ≤ vinogradovTailLengthEnvelope p d Y →
          ‖normalizedVinogradovMixedModConditionedMoment
            p B a (b + d) k r t X Y' xi eta'‖ ≤ L)
    (eta : ℤ) :
    normalizedVinogradovMixedCoupledTailIteratedNormMoment
        p B a k r t X d b Y xi eta ≤
      (p : ℝ) ^ d * L := by
  induction d generalizing b Y eta with
  | zero =>
      rw [normalizedVinogradovMixedCoupledTailIteratedNormMoment_zero,
        pow_zero, one_mul]
      simpa using hleaf Y eta le_rfl
  | succ d ih =>
      rw [normalizedVinogradovMixedCoupledTailIteratedNormMoment_succ]
      calc
        (∑ rho : ZMod p,
          normalizedVinogradovMixedCoupledTailIteratedNormMoment
            p B a k r t X d (b + 1)
              (vinogradovTailResidueLength p Y rho) xi
              (vinogradovTailResidueRefinedCenter p b eta rho)) ≤
            ∑ _rho : ZMod p, (p : ℝ) ^ d * L := by
          apply Finset.sum_le_sum
          intro rho hrho
          apply ih
          intro Y' eta' hY'
          have hp : 0 < p := (Fact.out : p.Prime).pos
          have hEnvelope :
              Y' ≤ vinogradovTailLengthEnvelope p (d + 1) Y := by
            rw [vinogradovTailLengthEnvelope_succ]
            exact hY'.trans
              (vinogradovTailLengthEnvelope_mono p d
                (vinogradovTailResidueLength p Y rho) (Y ⌈/⌉ p) hp
                (vinogradovTailResidueLength_le_ceilDiv p Y rho))
          have hscale : b + 1 + d = b + (d + 1) := by omega
          simpa only [hscale] using hleaf Y' eta' hEnvelope
        _ = (p : ℝ) ^ (d + 1) * L := by
          simp [ZMod.card, pow_succ, mul_comm, mul_left_comm]

/-- The no-wrap condition is monotone in the tail interval length. -/
theorem VinogradovResidualTailNoWrap.mono_length
    (p B b q X Y : ℕ)
    (hnowrap : VinogradovResidualTailNoWrap p B b q Y)
    (hXY : X ≤ Y) :
    VinogradovResidualTailNoWrap p B b q X := by
  intro degree hdegree hdegreeq
  rcases hnowrap degree hdegree hdegreeq with ⟨hscale, hbound⟩
  refine ⟨hscale, ?_⟩
  exact
    (Nat.mul_le_mul_left q
      (Nat.pow_le_pow_left hXY degree)).trans_lt hbound

/-- Coupled tail refinement cannot make the factorial-tail no-wrap condition
newly applicable.  If the depth-`d` length envelope does not wrap at scale
`b+d`, then the original interval already does not wrap at scale `b`. -/
theorem vinogradovTailLengthEnvelope_noWrap_condition_implies_root
    (p B b q Y d : ℕ) [Fact p.Prime]
    (hleaf :
      VinogradovResidualTailNoWrap p B (b + d) q
        (vinogradovTailLengthEnvelope p d Y)) :
    VinogradovResidualTailNoWrap p B b q Y := by
  intro degree hdegree hdegreeq
  rcases hleaf degree hdegree hdegreeq with
    ⟨hscaleLeaf, hboundLeaf⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hlength :
      Y ≤ p ^ d * vinogradovTailLengthEnvelope p d Y :=
    vinogradovTailLength_le_pow_mul_envelope p d Y hp
  have hscaleRoot : b * degree ≤ B := by
    exact
      (Nat.mul_le_mul_right degree (Nat.le_add_right b d)).trans
        hscaleLeaf
  constructor
  · exact hscaleRoot
  · calc
      q * Y ^ degree ≤
          q * (p ^ d *
            vinogradovTailLengthEnvelope p d Y) ^ degree :=
        Nat.mul_le_mul_left q (Nat.pow_le_pow_left hlength degree)
      _ = p ^ (d * degree) *
          (q *
            vinogradovTailLengthEnvelope p d Y ^ degree) := by
        rw [mul_pow, ← pow_mul]
        ring
      _ < p ^ (d * degree) *
          p ^ (B - (b + d) * degree) :=
        Nat.mul_lt_mul_of_pos_left hboundLeaf
          (pow_pos hp (d * degree))
      _ = p ^ (B - b * degree) := by
        rw [← pow_add]
        congr 1
        rw [Nat.add_mul] at hscaleLeaf ⊢
        omega

/-- At every depth-`d` leaf, a complete main block can be combined with the
factorial tail estimate using the common tail-length envelope. -/
theorem
    normalizedVinogradovMixedCoupledTailIteratedNormMoment_le_completeBlockFactorialTail
    (p B a b k r t Y Z n q d : ℕ)
    [Fact p.Prime] [NeZero (p ^ B)]
    (hqk : q ≤ k) (hsplit : n + q = 2 * t)
    (hnowrap :
      VinogradovResidualTailNoWrap p B (b + d) q
        (vinogradovTailLengthEnvelope p d Y))
    (z : Fin (p ^ a)) (eta : ℤ) :
    normalizedVinogradovMixedCoupledTailIteratedNormMoment
        p B a k r t (p ^ a * Z) d b Y
          (vinogradovCenterValue z) eta ≤
      (p : ℝ) ^ d *
        Real.sqrt
          ((Z : ℝ) ^ (4 * r) *
            ((q.factorial : ℝ) *
              (vinogradovTailLengthEnvelope p d Y : ℝ) ^
                (2 * n + q))) := by
  letI : NeZero (p ^ a) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  apply
    normalizedVinogradovMixedCoupledTailIteratedNormMoment_le_uniformLeaf
  intro Y' eta' hY'
  have hnowrap' :=
    hnowrap.mono_length p B (b + d) q Y'
      (vinogradovTailLengthEnvelope p d Y) hY'
  have hsquare :=
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_completeMainBlock_factorialTail
      p B a (b + d) k r t Y' Z n q
        (Fact.out : p.Prime).ne_zero hqk hsplit hnowrap' z eta'
  apply Real.le_sqrt_of_sq_le
  calc
    ‖normalizedVinogradovMixedModConditionedMoment
        p B a (b + d) k r t (p ^ a * Z) Y'
          (vinogradovCenterValue z) eta'‖ ^ 2 ≤
      (Z : ℝ) ^ (4 * r) *
        ((q.factorial : ℝ) * (Y' : ℝ) ^ (2 * n + q)) := by
      simpa [vinogradovCenterValue] using hsquare
    _ ≤
      (Z : ℝ) ^ (4 * r) *
        ((q.factorial : ℝ) *
          (vinogradovTailLengthEnvelope p d Y : ℝ) ^
            (2 * n + q)) := by
      gcongr

/-- The coupled recurrence stopped after `d` digits and closed by the
complete-main-block factorial-tail estimate.  The residue cost simplifies to
`p^(2td)`; any eventual VK saving must come from the lower leaf exponent and
the parameter schedule, not from the residue tree itself. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_le_coupledTailIteratedCompleteBlockFactorialTail
    (p B a b k r t Y Z n q d : ℕ)
    [Fact p.Prime] [NeZero (p ^ B)]
    (ht : 0 < t) (hqk : q ≤ k) (hsplit : n + q = 2 * t)
    (hnowrap :
      VinogradovResidualTailNoWrap p B (b + d) q
        (vinogradovTailLengthEnvelope p d Y))
    (z : Fin (p ^ a)) (eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p B a b k r t (p ^ a * Z) Y
          (vinogradovCenterValue z) eta‖ ≤
      (p : ℝ) ^ (d * (2 * t)) *
        Real.sqrt
          ((Z : ℝ) ^ (4 * r) *
            ((q.factorial : ℝ) *
              (vinogradovTailLengthEnvelope p d Y : ℝ) ^
                (2 * n + q))) := by
  have htree :=
    normalizedVinogradovMixedCoupledTailIteratedNormMoment_le_completeBlockFactorialTail
      p B a b k r t Y Z n q d hqk hsplit hnowrap z eta
  calc
    ‖normalizedVinogradovMixedModConditionedMoment
        p B a b k r t (p ^ a * Z) Y
          (vinogradovCenterValue z) eta‖ ≤
      (p : ℝ) ^ (d * (2 * t - 1)) *
        normalizedVinogradovMixedCoupledTailIteratedNormMoment
          p B a k r t (p ^ a * Z) d b Y
            (vinogradovCenterValue z) eta :=
      norm_normalizedVinogradovMixedModConditionedMoment_le_coupledTailIterated
        p B a b k r t (p ^ a * Z) Y d ht
          (vinogradovCenterValue z) eta
    _ ≤
      (p : ℝ) ^ (d * (2 * t - 1)) *
        ((p : ℝ) ^ d *
          Real.sqrt
            ((Z : ℝ) ^ (4 * r) *
              ((q.factorial : ℝ) *
                (vinogradovTailLengthEnvelope p d Y : ℝ) ^
                  (2 * n + q)))) :=
      mul_le_mul_of_nonneg_left htree (by positivity)
    _ =
      (p : ℝ) ^ (d * (2 * t)) *
        Real.sqrt
          ((Z : ℝ) ^ (4 * r) *
            ((q.factorial : ℝ) *
              (vinogradovTailLengthEnvelope p d Y : ℝ) ^
                (2 * n + q))) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      calc
        d * (2 * t - 1) + d =
            d * (2 * t - 1) + d * 1 := by rw [mul_one]
        _ = d * ((2 * t - 1) + 1) := by
          rw [Nat.mul_add]
        _ = d * (2 * t) := by
          congr 1
          omega

end

end ZeroFreeRegion.VinogradovKorobov
