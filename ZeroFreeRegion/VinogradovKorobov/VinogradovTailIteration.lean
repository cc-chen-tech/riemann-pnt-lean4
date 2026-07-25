import ZeroFreeRegion.VinogradovKorobov.VinogradovTailResidueReparameterization
import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedTailMoment
import Mathlib.Algebra.Order.Floor.Div

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The endpoint-sensitive tail-moment tree after repeatedly exposing one
`p`-adic residue digit.  At depth zero it is the original tail moment; at
depth `d + 1` it is the sum of the depth-`d` trees rooted at every refined
residue fiber. -/
noncomputable def normalizedVinogradovMixedTailIteratedNormMoment
    (p B k s : ℕ) [Fact p.Prime] [NeZero (p ^ B)] :
    ℕ → ℕ → ℕ → ℤ → ℝ
  | 0, b, Y, eta =>
      normalizedVinogradovMixedTailNormMoment p B b k s Y eta
  | d + 1, b, Y, eta =>
      ∑ rho : ZMod p,
        normalizedVinogradovMixedTailIteratedNormMoment p B k s
          d (b + 1) (vinogradovTailResidueLength p Y rho)
            (vinogradovTailResidueRefinedCenter p b eta rho)

@[simp] theorem normalizedVinogradovMixedTailIteratedNormMoment_zero
    (p B b k s Y : ℕ) [Fact p.Prime] [NeZero (p ^ B)] (eta : ℤ) :
    normalizedVinogradovMixedTailIteratedNormMoment
        p B k s 0 b Y eta =
      normalizedVinogradovMixedTailNormMoment p B b k s Y eta := by
  rfl

@[simp] theorem normalizedVinogradovMixedTailIteratedNormMoment_succ
    (p B b k s Y d : ℕ) [Fact p.Prime] [NeZero (p ^ B)] (eta : ℤ) :
    normalizedVinogradovMixedTailIteratedNormMoment
        p B k s (d + 1) b Y eta =
      ∑ rho : ZMod p,
        normalizedVinogradovMixedTailIteratedNormMoment p B k s
          d (b + 1) (vinogradovTailResidueLength p Y rho)
            (vinogradovTailResidueRefinedCenter p b eta rho) := by
  rfl

/-- Iterating the one-digit recurrence `d` times costs exactly the accumulated
Holder factor `p^(d * (2s - 1))`; the remaining quantity is the honest sum of
all depth-`d` endpoint-sensitive leaf moments. -/
theorem normalizedVinogradovMixedTailNormMoment_le_iterated
    (p B b k s Y d : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (hs : 0 < s) (eta : ℤ) :
    normalizedVinogradovMixedTailNormMoment p B b k s Y eta ≤
      (p : ℝ) ^ (d * (2 * s - 1)) *
        normalizedVinogradovMixedTailIteratedNormMoment
          p B k s d b Y eta := by
  induction d generalizing b Y eta with
  | zero =>
      simp
  | succ d ih =>
      have hstep :=
        normalizedVinogradovMixedTailNormMoment_le_nextScaleResidueSum
          p B b k s Y hs eta
      have hleaves :
          (∑ rho : ZMod p,
            normalizedVinogradovMixedTailNormMoment p B (b + 1) k s
              (vinogradovTailResidueLength p Y rho)
              (vinogradovTailResidueRefinedCenter p b eta rho)) ≤
            ∑ rho : ZMod p,
              (p : ℝ) ^ (d * (2 * s - 1)) *
                normalizedVinogradovMixedTailIteratedNormMoment p B k s
                  d (b + 1) (vinogradovTailResidueLength p Y rho)
                  (vinogradovTailResidueRefinedCenter p b eta rho) := by
        apply Finset.sum_le_sum
        intro rho hrho
        exact ih
          (b := b + 1)
          (Y := vinogradovTailResidueLength p Y rho)
          (eta := vinogradovTailResidueRefinedCenter p b eta rho)
      calc
        normalizedVinogradovMixedTailNormMoment p B b k s Y eta ≤
            (p : ℝ) ^ (2 * s - 1) *
              ∑ rho : ZMod p,
                normalizedVinogradovMixedTailNormMoment p B (b + 1) k s
                  (vinogradovTailResidueLength p Y rho)
                  (vinogradovTailResidueRefinedCenter p b eta rho) :=
          hstep
        _ ≤ (p : ℝ) ^ (2 * s - 1) *
              ∑ rho : ZMod p,
                (p : ℝ) ^ (d * (2 * s - 1)) *
                  normalizedVinogradovMixedTailIteratedNormMoment p B k s
                    d (b + 1) (vinogradovTailResidueLength p Y rho)
                    (vinogradovTailResidueRefinedCenter p b eta rho) :=
          mul_le_mul_of_nonneg_left hleaves (by positivity)
        _ = (p : ℝ) ^ ((d + 1) * (2 * s - 1)) *
              normalizedVinogradovMixedTailIteratedNormMoment
                p B k s (d + 1) b Y eta := by
          rw [normalizedVinogradovMixedTailIteratedNormMoment_succ]
          rw [← Finset.mul_sum, ← mul_assoc, ← pow_add]
          congr 2
          ring

/-- The leaf length obtained by following a prescribed sequence of refined
residue digits. -/
def vinogradovTailPathLength
    (p : ℕ) : (d : ℕ) → ℕ → (Fin d → ZMod p) → ℕ
  | 0, Y, _ => Y
  | d + 1, Y, path =>
      vinogradovTailPathLength p d
        (vinogradovTailResidueLength p Y (path 0)) (Fin.tail path)

/-- Every one-digit residue fiber has length at most `ceil(Y / p)`. -/
theorem vinogradovTailResidueLength_le_ceilDiv
    (p Y : ℕ) [Fact p.Prime] (rho : ZMod p) :
    vinogradovTailResidueLength p Y rho ≤ Y ⌈/⌉ p := by
  rw [vinogradovTailResidueLength, Nat.ceilDiv_eq_add_pred_div]
  apply Nat.div_le_div_right
  have hrpos :=
    vinogradovPositiveResidueRepresentative_pos p rho
  omega

/-- A center-independent upper envelope for every leaf length after exposing
`d` base-`p` residue digits. -/
def vinogradovTailLengthEnvelope
    (p : ℕ) : ℕ → ℕ → ℕ
  | 0, Y => Y
  | d + 1, Y =>
      vinogradovTailLengthEnvelope p d (Y ⌈/⌉ p)

@[simp] theorem vinogradovTailLengthEnvelope_zero
    (p Y : ℕ) :
    vinogradovTailLengthEnvelope p 0 Y = Y := by
  rfl

@[simp] theorem vinogradovTailLengthEnvelope_succ
    (p d Y : ℕ) :
    vinogradovTailLengthEnvelope p (d + 1) Y =
      vinogradovTailLengthEnvelope p d (Y ⌈/⌉ p) := by
  rfl

/-- Repeated ceiling division is monotone in the starting interval length. -/
theorem vinogradovTailLengthEnvelope_mono
    (p d X Y : ℕ) (hp : 0 < p) (hXY : X ≤ Y) :
    vinogradovTailLengthEnvelope p d X ≤
      vinogradovTailLengthEnvelope p d Y := by
  induction d generalizing X Y with
  | zero =>
      simpa using hXY
  | succ d ih =>
      rw [vinogradovTailLengthEnvelope_succ,
        vinogradovTailLengthEnvelope_succ]
      apply ih
      rw [ceilDiv_le_iff_le_mul hp]
      exact hXY.trans ((ceilDiv_le_iff_le_mul hp).mp le_rfl)

/-- The original interval is covered by `p^d` residue paths, each of length
at most the depth-`d` envelope. -/
theorem vinogradovTailLength_le_pow_mul_envelope
    (p d Y : ℕ) (hp : 0 < p) :
    Y ≤ p ^ d * vinogradovTailLengthEnvelope p d Y := by
  induction d generalizing Y with
  | zero =>
      simp
  | succ d ih =>
      rw [vinogradovTailLengthEnvelope_succ]
      calc
        Y ≤ p * (Y ⌈/⌉ p) :=
          (ceilDiv_le_iff_le_mul hp).mp le_rfl
        _ ≤ p *
            (p ^ d *
              vinogradovTailLengthEnvelope p d (Y ⌈/⌉ p)) :=
          Nat.mul_le_mul_left p (ih (Y ⌈/⌉ p))
        _ = p ^ (d + 1) *
            vinogradovTailLengthEnvelope p d (Y ⌈/⌉ p) := by
          simp [pow_succ, Nat.mul_comm, Nat.mul_assoc]

/-- Refining the tail cannot make the first-residual-congruence scale
condition newly applicable.  If the depth-`d` envelope fits the residual
modulus at scale `b+d`, then the original interval already fits the residual
modulus at scale `b`. -/
theorem vinogradovTailLengthEnvelope_firstPower_condition_implies_root
    (p B b Y d : ℕ) (hp : 0 < p) (hbB : b + d ≤ B)
    (hY :
      vinogradovTailLengthEnvelope p d Y ≤
        p ^ (B - (b + d))) :
    Y ≤ p ^ (B - b) := by
  calc
    Y ≤ p ^ d * vinogradovTailLengthEnvelope p d Y :=
      vinogradovTailLength_le_pow_mul_envelope p d Y hp
    _ ≤ p ^ d * p ^ (B - (b + d)) :=
      Nat.mul_le_mul_left (p ^ d) hY
    _ = p ^ (B - b) := by
      rw [← pow_add]
      congr 1
      omega

/-- A uniform bound `L` for every depth-`d` leaf moment sums to at most
`p^d * L` over the endpoint-sensitive residue tree.  This is the bridge used
to stop the recurrence before singleton leaves and insert a genuinely
nontrivial tail estimate. -/
theorem normalizedVinogradovMixedTailIteratedNormMoment_le_uniformLeaf
    (p B b k s Y d : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (L : ℝ)
    (hleaf :
      ∀ Y' eta',
        Y' ≤ vinogradovTailLengthEnvelope p d Y →
          normalizedVinogradovMixedTailNormMoment
              p B (b + d) k s Y' eta' ≤ L)
    (eta : ℤ) :
    normalizedVinogradovMixedTailIteratedNormMoment
        p B k s d b Y eta ≤ (p : ℝ) ^ d * L := by
  induction d generalizing b Y eta with
  | zero =>
      rw [normalizedVinogradovMixedTailIteratedNormMoment_zero,
        pow_zero, one_mul]
      simpa using hleaf Y eta le_rfl
  | succ d ih =>
      rw [normalizedVinogradovMixedTailIteratedNormMoment_succ]
      calc
        (∑ rho : ZMod p,
          normalizedVinogradovMixedTailIteratedNormMoment p B k s
            d (b + 1) (vinogradovTailResidueLength p Y rho)
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

/-- Stop the residue recurrence after `d` digits and apply the first residual
congruence at every leaf.  The leaf exponent drops from `2(n+1)` to
`2n+1`, while the residue tree contributes only `p^d` leaves. -/
theorem normalizedVinogradovMixedTailIteratedNormMoment_le_firstPower
    (p B b k n Y d : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (hp : p ≠ 0) (hk : 0 < k) (hbB : b + d ≤ B)
    (hY :
      vinogradovTailLengthEnvelope p d Y ≤
        p ^ (B - (b + d)))
    (eta : ℤ) :
    normalizedVinogradovMixedTailIteratedNormMoment
        p B k (n + 1) d b Y eta ≤
      (p : ℝ) ^ d *
        (vinogradovTailLengthEnvelope p d Y : ℝ) ^ (2 * n + 1) := by
  apply normalizedVinogradovMixedTailIteratedNormMoment_le_uniformLeaf
  intro Y' eta' hY'
  calc
    normalizedVinogradovMixedTailNormMoment
        p B (b + d) k (n + 1) Y' eta' ≤
      (Y' : ℝ) ^ (2 * n + 1) :=
        normalizedVinogradovMixedTailNormMoment_le_firstPower
          p B (b + d) k n Y' hp hk hbB (hY'.trans hY) eta'
    _ ≤
      (vinogradovTailLengthEnvelope p d Y : ℝ) ^ (2 * n + 1) := by
        gcongr

/-- The hybrid stopped recurrence yields
`p^(2(n+1)d) * E^(2n+1)`, where `E` is the depth-`d` leaf-length envelope.
Unlike full refinement to singleton leaves, this is potentially nontrivial
when the recurrence stops while `E` is still larger than one. -/
theorem normalizedVinogradovMixedTailNormMoment_le_iteratedFirstPower
    (p B b k n Y d : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (hp : p ≠ 0) (hk : 0 < k) (hbB : b + d ≤ B)
    (hY :
      vinogradovTailLengthEnvelope p d Y ≤
        p ^ (B - (b + d)))
    (eta : ℤ) :
    normalizedVinogradovMixedTailNormMoment
        p B b k (n + 1) Y eta ≤
      (p : ℝ) ^ (d * (2 * (n + 1))) *
        (vinogradovTailLengthEnvelope p d Y : ℝ) ^ (2 * n + 1) := by
  have htree :=
    normalizedVinogradovMixedTailIteratedNormMoment_le_firstPower
      p B b k n Y d hp hk hbB hY eta
  calc
    normalizedVinogradovMixedTailNormMoment
        p B b k (n + 1) Y eta ≤
      (p : ℝ) ^ (d * (2 * (n + 1) - 1)) *
        normalizedVinogradovMixedTailIteratedNormMoment
          p B k (n + 1) d b Y eta :=
        normalizedVinogradovMixedTailNormMoment_le_iterated
          p B b k (n + 1) Y d (by omega) eta
    _ ≤
      (p : ℝ) ^ (d * (2 * (n + 1) - 1)) *
        ((p : ℝ) ^ d *
          (vinogradovTailLengthEnvelope p d Y : ℝ) ^ (2 * n + 1)) :=
        mul_le_mul_of_nonneg_left htree (by positivity)
    _ =
      (p : ℝ) ^ (d * (2 * (n + 1))) *
        (vinogradovTailLengthEnvelope p d Y : ℝ) ^ (2 * n + 1) := by
        rw [← mul_assoc, ← pow_add]
        congr 2

/-- Once the exposed modulus `p^d` is at least the original interval length,
every depth-`d` residue path contains at most one integer. -/
theorem vinogradovTailPathLength_le_one_of_length_le_pow
    (p d Y : ℕ) [Fact p.Prime] (path : Fin d → ZMod p)
    (hY : Y ≤ p ^ d) :
    vinogradovTailPathLength p d Y path ≤ 1 := by
  induction d generalizing Y with
  | zero =>
      simpa [vinogradovTailPathLength] using hY
  | succ d ih =>
      rw [vinogradovTailPathLength]
      apply ih
      have hp : 0 < p := (Fact.out : p.Prime).pos
      have hceil : Y ⌈/⌉ p ≤ p ^ d := by
        rw [ceilDiv_le_iff_le_mul hp]
        simpa [pow_succ, Nat.mul_comm] using hY
      exact
        (vinogradovTailResidueLength_le_ceilDiv p Y (path 0)).trans hceil

/-- The ambient tuple-count bound for an affine tail moment. -/
theorem normalizedVinogradovMixedTailNormMoment_le_trivial
    (p B b k s Y : ℕ) [NeZero (p ^ B)] (eta : ℤ) :
    normalizedVinogradovMixedTailNormMoment p B b k s Y eta ≤
      (Y : ℝ) ^ (2 * s) := by
  rw [normalizedVinogradovMixedTailNormMoment_eq_solutionPairSetCard]
  norm_cast
  calc
    (vinogradovIntSolutionPairSet (p ^ B) k s Y
        (vinogradovMixedTailValue p b Y eta)).card ≤
        Fintype.card ((Fin s → Fin Y) × (Fin s → Fin Y)) := by
      simpa using
        (Finset.card_le_univ
          (vinogradovIntSolutionPairSet (p ^ B) k s Y
            (vinogradovMixedTailValue p b Y eta)))
    _ = Y ^ (2 * s) := by
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
      rw [← pow_add]
      congr 1
      omega

/-- If `p^d` covers the starting interval, the depth-`d` tree has at most
`p^d` total leaf mass: there are `p^d` residue paths and every leaf moment is
at most one. -/
theorem normalizedVinogradovMixedTailIteratedNormMoment_le_leafCount
    (p B b k s Y d : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (hY : Y ≤ p ^ d) (eta : ℤ) :
    normalizedVinogradovMixedTailIteratedNormMoment
        p B k s d b Y eta ≤ (p : ℝ) ^ d := by
  induction d generalizing b Y eta with
  | zero =>
      rw [normalizedVinogradovMixedTailIteratedNormMoment_zero, pow_zero]
      calc
        normalizedVinogradovMixedTailNormMoment p B b k s Y eta ≤
            (Y : ℝ) ^ (2 * s) :=
          normalizedVinogradovMixedTailNormMoment_le_trivial
            p B b k s Y eta
        _ ≤ 1 := by
          have hY' : Y = 0 ∨ Y = 1 := by
            have hYle : Y ≤ 1 := by simpa using hY
            omega
          rcases hY' with rfl | rfl
          · by_cases hs0 : s = 0
            · simp [hs0]
            · have hexp : 2 * s ≠ 0 := by omega
              simp [hexp]
          · simp
  | succ d ih =>
      rw [normalizedVinogradovMixedTailIteratedNormMoment_succ]
      have hp : 0 < p := (Fact.out : p.Prime).pos
      have hceil : Y ⌈/⌉ p ≤ p ^ d := by
        rw [ceilDiv_le_iff_le_mul hp]
        simpa [pow_succ, Nat.mul_comm] using hY
      calc
        (∑ rho : ZMod p,
          normalizedVinogradovMixedTailIteratedNormMoment p B k s
            d (b + 1) (vinogradovTailResidueLength p Y rho)
              (vinogradovTailResidueRefinedCenter p b eta rho)) ≤
            ∑ _rho : ZMod p, (p : ℝ) ^ d := by
          apply Finset.sum_le_sum
          intro rho hrho
          exact ih
            (b := b + 1)
            (Y := vinogradovTailResidueLength p Y rho)
            ((vinogradovTailResidueLength_le_ceilDiv p Y rho).trans hceil)
            (vinogradovTailResidueRefinedCenter p b eta rho)
        _ = (p : ℝ) ^ (d + 1) := by
          simp [ZMod.card, pow_succ, mul_comm]

/-- Fully refining until `p^d ≥ Y` and then using only singleton leaf bounds
recovers the ambient exponent `p^(2sd)`.  Thus residue splitting by itself
does not create a power saving; a nontrivial estimate must enter before or
across the leaves. -/
theorem normalizedVinogradovMixedTailNormMoment_le_iterated_trivial
    (p B b k s Y d : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (hs : 0 < s) (hY : Y ≤ p ^ d) (eta : ℤ) :
    normalizedVinogradovMixedTailNormMoment p B b k s Y eta ≤
      (p : ℝ) ^ (d * (2 * s)) := by
  calc
    normalizedVinogradovMixedTailNormMoment p B b k s Y eta ≤
        (p : ℝ) ^ (d * (2 * s - 1)) *
          normalizedVinogradovMixedTailIteratedNormMoment
            p B k s d b Y eta :=
      normalizedVinogradovMixedTailNormMoment_le_iterated
        p B b k s Y d hs eta
    _ ≤ (p : ℝ) ^ (d * (2 * s - 1)) * (p : ℝ) ^ d :=
      mul_le_mul_of_nonneg_left
        (normalizedVinogradovMixedTailIteratedNormMoment_le_leafCount
          p B b k s Y d hY eta) (by positivity)
    _ = (p : ℝ) ^ (d * (2 * s)) := by
      rw [← pow_add]
      congr 1
      have hsone : 1 ≤ 2 * s := by omega
      calc
        d * (2 * s - 1) + d = d * ((2 * s - 1) + 1) := by ring
        _ = d * (2 * s) := by rw [Nat.sub_add_cancel hsone]

end

end ZeroFreeRegion.VinogradovKorobov
