import ZeroFreeRegion.VinogradovKorobov.VinogradovLowDiversity
import ZeroFreeRegion.VinogradovKorobov.VinogradovCorrectionFiber

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance vinogradovLowDiversityPrimePowerPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-- The left base tuple reduced to one-based residues modulo `p`. -/
def vinogradovPrimePowerBaseLeftResidue
    (p s n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n) : Fin s → ZMod p :=
  fun i ↦ (vinogradovPrimePowerBaseLeftInt xy i : ZMod p)

/-- The analogous right residue tuple. -/
def vinogradovPrimePowerBaseRightResidue
    (p s n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n) : Fin s → ZMod p :=
  fun i ↦ (vinogradovPrimePowerBaseRightInt xy i : ZMod p)

/-- One unrestricted digit lift leaves the left one-based residue tuple
unchanged. -/
theorem vinogradovPrimePowerLiftAmbientEquiv_leftResidue
    (p s n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n)
    (z : vinogradovPrimePowerSplitCorrection p 0 s) :
    vinogradovPrimePowerBaseLeftResidue p s (n + 1)
        (vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩) =
      vinogradovPrimePowerBaseLeftResidue p s n xy := by
  funext i
  simpa [vinogradovPrimePowerBaseLeftResidue,
    vinogradovPrimePowerBaseLeftInt] using
      (vinogradovPrimePowerLiftAmbientEquiv_fst_mod
        p 0 s n xy z (Fin.natAdd 0 i))

/-- One unrestricted digit lift also leaves the right residue tuple
unchanged. -/
theorem vinogradovPrimePowerLiftAmbientEquiv_rightResidue
    (p s n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n)
    (z : vinogradovPrimePowerSplitCorrection p 0 s) :
    vinogradovPrimePowerBaseRightResidue p s (n + 1)
        (vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩) =
      vinogradovPrimePowerBaseRightResidue p s n xy := by
  funext i
  simp only [vinogradovPrimePowerBaseRightResidue,
    vinogradovPrimePowerBaseRightInt]
  rw [vinogradovPrimePowerLiftAmbientEquiv_apply_snd_val]
  push_cast
  simp [pow_succ]

/-- Prime-power base pairs whose left and right reductions both take fewer
than `d` values. -/
noncomputable def vinogradovPrimePowerLowDiversityAmbientSet
    (p s d n : ℕ) [Fact p.Prime] :
    Finset (vinogradovPrimePowerBasePair p 0 s n) :=
  Finset.univ.filter fun xy ↦
    vinogradovPrimePowerBaseLeftResidue p s n xy ∈
        vinogradovLowDiversityTupleSet p s d ∧
      vinogradovPrimePowerBaseRightResidue p s n xy ∈
        vinogradovLowDiversityTupleSet p s d

theorem mem_vinogradovPrimePowerLowDiversityAmbientSet_iff
    (p s d n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n) :
    xy ∈ vinogradovPrimePowerLowDiversityAmbientSet p s d n ↔
      vinogradovPrimePowerBaseLeftResidue p s n xy ∈
          vinogradovLowDiversityTupleSet p s d ∧
        vinogradovPrimePowerBaseRightResidue p s n xy ∈
          vinogradovLowDiversityTupleSet p s d := by
  simp [vinogradovPrimePowerLowDiversityAmbientSet]

/-- Complete one-based residue encoding at the first prime level. -/
noncomputable def vinogradovPrimePowerLowDiversityBaseZeroEquiv
    (p s : ℕ) [Fact p.Prime] :
    vinogradovPrimePowerBasePair p 0 s 0 ≃
      ((Fin s → ZMod p) × (Fin s → ZMod p)) :=
  (Equiv.prodCongr
      (Equiv.arrowCongr (finCongr (Nat.zero_add s)) (Equiv.refl _))
      (Equiv.arrowCongr (finCongr (Nat.zero_add s)) (Equiv.refl _))).trans
    (vinogradovFirstStratumCompleteResiduePairEquiv p s)

/-- The first-level low-diversity pair count is bounded by two independent
center-label encodings. -/
theorem card_vinogradovPrimePowerLowDiversityAmbientSet_zero_le
    (p s d : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerLowDiversityAmbientSet p s d 0).card ≤
      (p ^ (d - 1) * (d - 1) ^ s) ^ 2 := by
  classical
  let e := vinogradovPrimePowerLowDiversityBaseZeroEquiv p s
  let target :=
    (vinogradovLowDiversityTupleSet p s d).product
      (vinogradovLowDiversityTupleSet p s d)
  have hcard :
      (vinogradovPrimePowerLowDiversityAmbientSet p s d 0).card =
        target.card := by
    apply Finset.card_equiv e
    intro xy
    have hx : (e xy).1 = vinogradovPrimePowerBaseLeftResidue p s 0 xy := by
      funext i
      simpa [e, vinogradovPrimePowerLowDiversityBaseZeroEquiv,
        vinogradovPrimePowerBaseLeftResidue,
        vinogradovPrimePowerBaseLeftInt,
        vinogradovFirstStratumCompleteResiduePairEquiv,
        vinogradovFirstStratumCompleteResidueEquiv_apply]
    have hy : (e xy).2 = vinogradovPrimePowerBaseRightResidue p s 0 xy := by
      funext i
      simpa [e, vinogradovPrimePowerLowDiversityBaseZeroEquiv,
        vinogradovPrimePowerBaseRightResidue,
        vinogradovPrimePowerBaseRightInt,
        vinogradovFirstStratumCompleteResiduePairEquiv,
        vinogradovFirstStratumCompleteResidueEquiv_apply]
    rw [mem_vinogradovPrimePowerLowDiversityAmbientSet_iff]
    dsimp [target]
    rw [Finset.mem_product, hx, hy]
  calc
    (vinogradovPrimePowerLowDiversityAmbientSet p s d 0).card =
        target.card := hcard
    _ = (vinogradovLowDiversityTupleSet p s d).card ^ 2 := by
      dsimp [target]
      rw [Finset.card_product, pow_two]
    _ ≤ (p ^ (d - 1) * (d - 1) ^ s) ^ 2 := by
      exact Nat.pow_le_pow_left
        (card_vinogradovLowDiversityTupleSet_le p s d) 2

/-- A base pair and arbitrary next digits, restricted only by low diversity
of the base residues. -/
noncomputable def vinogradovPrimePowerLowDiversityAmbientLiftSet
    (p s d n : ℕ) [Fact p.Prime] :
    Finset (Σ _ : vinogradovPrimePowerBasePair p 0 s n,
      vinogradovPrimePowerSplitCorrection p 0 s) :=
  (vinogradovPrimePowerLowDiversityAmbientSet p s d n).sigma
    fun _ ↦ Finset.univ

theorem card_vinogradovPrimePowerLowDiversityAmbientLiftSet
    (p s d n : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerLowDiversityAmbientLiftSet p s d n).card =
      (vinogradovPrimePowerLowDiversityAmbientSet p s d n).card *
        p ^ (2 * s) := by
  rw [vinogradovPrimePowerLowDiversityAmbientLiftSet, Finset.card_sigma]
  simp only [Finset.card_univ, Finset.sum_const_nat]
  rw [card_vinogradovPrimePowerSplitCorrection]
  simp

theorem
    mem_vinogradovPrimePowerLowDiversityAmbientLiftSet_iff_image_mem
    (p s d n : ℕ) [Fact p.Prime]
    (u : Σ _ : vinogradovPrimePowerBasePair p 0 s n,
      vinogradovPrimePowerSplitCorrection p 0 s) :
    u ∈ vinogradovPrimePowerLowDiversityAmbientLiftSet p s d n ↔
      vinogradovPrimePowerLiftAmbientEquiv p 0 s n u ∈
        vinogradovPrimePowerLowDiversityAmbientSet p s d (n + 1) := by
  rcases u with ⟨xy, z⟩
  simp only [vinogradovPrimePowerLowDiversityAmbientLiftSet,
    Finset.mem_sigma, Finset.mem_univ, and_true]
  rw [mem_vinogradovPrimePowerLowDiversityAmbientSet_iff,
    mem_vinogradovPrimePowerLowDiversityAmbientSet_iff,
    vinogradovPrimePowerLiftAmbientEquiv_leftResidue,
    vinogradovPrimePowerLiftAmbientEquiv_rightResidue]

theorem map_vinogradovPrimePowerLowDiversityAmbientLiftSet_eq
    (p s d n : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerLowDiversityAmbientLiftSet p s d n).map
        (vinogradovPrimePowerLiftAmbientEquiv p 0 s n).toEmbedding =
      vinogradovPrimePowerLowDiversityAmbientSet p s d (n + 1) := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_map.mp hv with ⟨u, hu, rfl⟩
    exact
      (mem_vinogradovPrimePowerLowDiversityAmbientLiftSet_iff_image_mem
        p s d n u).mp hu
  · intro hv
    let e := vinogradovPrimePowerLiftAmbientEquiv p 0 s n
    let u := e.symm v
    have heu : e u = v := e.apply_symm_apply v
    apply Finset.mem_map.mpr
    refine ⟨u, ?_, heu⟩
    apply
      (mem_vinogradovPrimePowerLowDiversityAmbientLiftSet_iff_image_mem
        p s d n u).mpr
    simpa [e, u] using hv

/-- Exact one-step ambient recurrence. -/
theorem card_vinogradovPrimePowerLowDiversityAmbientSet_succ
    (p s d n : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerLowDiversityAmbientSet p s d (n + 1)).card =
      (vinogradovPrimePowerLowDiversityAmbientSet p s d n).card *
        p ^ (2 * s) := by
  rw [← map_vinogradovPrimePowerLowDiversityAmbientLiftSet_eq p s d n,
    Finset.card_map,
    card_vinogradovPrimePowerLowDiversityAmbientLiftSet]

/-- Uniform prime-power count for low-diversity base pairs. -/
theorem card_vinogradovPrimePowerLowDiversityAmbientSet_le
    (p s d n : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerLowDiversityAmbientSet p s d n).card ≤
      (p ^ (d - 1) * (d - 1) ^ s) ^ 2 *
        (p ^ (2 * s)) ^ n := by
  induction n with
  | zero =>
      simpa using card_vinogradovPrimePowerLowDiversityAmbientSet_zero_le
        p s d
  | succ n ih =>
      rw [card_vinogradovPrimePowerLowDiversityAmbientSet_succ]
      calc
        (vinogradovPrimePowerLowDiversityAmbientSet p s d n).card *
            p ^ (2 * s) ≤
          ((p ^ (d - 1) * (d - 1) ^ s) ^ 2 *
            (p ^ (2 * s)) ^ n) * p ^ (2 * s) :=
          Nat.mul_le_mul_right _ ih
        _ = (p ^ (d - 1) * (d - 1) ^ s) ^ 2 *
            (p ^ (2 * s)) ^ (n + 1) := by
          rw [pow_succ (p ^ (2 * s)) n, mul_assoc]

end

end ZeroFreeRegion.VinogradovKorobov
