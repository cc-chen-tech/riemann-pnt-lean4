import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedNormalizedConditioning
import ZeroFreeRegion.VinogradovKorobov.VinogradovTailResidueReparameterization
import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedDecomposition

open scoped BigOperators NNReal

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- For the constant coefficient sequence `1`, the squared residue mass is
exactly the number of indices in that residue class. -/
theorem vinogradovResidueMassSq_one_eq_card
    (Q X : ℕ) [NeZero Q] (rho : ZMod Q) :
    vinogradovResidueMassSq Q X rho (fun _ : Fin X ↦ (1 : ℂ)) =
      ((vinogradovResidueClassFinset Q X rho).card : ℝ≥0) := by
  simp [vinogradovResidueMassSq]

/-- The square of the constant-coefficient residue mass is its residue-class
cardinality. -/
theorem vinogradovResidueMass_one_sq_eq_card
    (Q X : ℕ) [NeZero Q] (rho : ZMod Q) :
    vinogradovResidueMass Q X rho (fun _ : Fin X ↦ (1 : ℂ)) ^ 2 =
      ((vinogradovResidueClassFinset Q X rho).card : ℝ≥0) := by
  simp [vinogradovResidueMass, vinogradovResidueMassSq_one_eq_card]

/-- The mass factor needed to convert a normalized `2t`-th moment back to a
raw moment is exactly `card^(t-1)` for constant coefficients. -/
theorem vinogradovResidueMass_one_evenPow_eq_card_pow
    (Q X t : ℕ) [NeZero Q] (rho : ZMod Q) (ht : 1 ≤ t) :
    vinogradovResidueMass Q X rho (fun _ : Fin X ↦ (1 : ℂ)) ^
        (2 * t - 2) =
      ((vinogradovResidueClassFinset Q X rho).card : ℝ≥0) ^ (t - 1) := by
  have hexponent : 2 * t - 2 = 2 * (t - 1) := by omega
  calc
    vinogradovResidueMass Q X rho (fun _ : Fin X ↦ (1 : ℂ)) ^
        (2 * t - 2) =
      vinogradovResidueMass Q X rho (fun _ : Fin X ↦ (1 : ℂ)) ^
        (2 * (t - 1)) := by rw [hexponent]
    _ = (vinogradovResidueMass Q X rho
          (fun _ : Fin X ↦ (1 : ℂ)) ^ 2) ^ (t - 1) := by
      rw [pow_mul]
    _ = ((vinogradovResidueClassFinset Q X rho).card : ℝ≥0) ^
        (t - 1) := by
      rw [vinogradovResidueMass_one_sq_eq_card]

/-- At one prime digit, the squared constant-coefficient residue mass is the
exact endpoint-sensitive tail-fiber length. -/
theorem vinogradovResidueMassSq_one_eq_tailResidueLength
    (p Y : ℕ) [Fact p.Prime] [NeZero p] (rho : ZMod p) :
    vinogradovResidueMassSq p Y rho (fun _ : Fin Y ↦ (1 : ℂ)) =
      (vinogradovTailResidueLength p Y rho : ℝ≥0) := by
  rw [vinogradovResidueMassSq_one_eq_card,
    card_vinogradovResidueClassFinset_eq_tailResidueLength]

/-- The raw-conversion mass factor on a prime residue fiber is the exact
tail length raised to `t-1`. -/
theorem vinogradovResidueMass_one_evenPow_eq_tailResidueLength_pow
    (p Y t : ℕ) [Fact p.Prime] [NeZero p] (rho : ZMod p) (ht : 1 ≤ t) :
    vinogradovResidueMass p Y rho (fun _ : Fin Y ↦ (1 : ℂ)) ^
        (2 * t - 2) =
      (vinogradovTailResidueLength p Y rho : ℝ≥0) ^ (t - 1) := by
  rw [vinogradovResidueMass_one_evenPow_eq_card_pow p Y t rho ht,
    card_vinogradovResidueClassFinset_eq_tailResidueLength]

/-- Every residue class has exactly `Y` members in a complete block of length
`p^v * Y`, stated for an arbitrary `ZMod` representative. -/
theorem card_vinogradovResidueClassFinset_completePrimePowerBlock
    (p v Y : ℕ) [NeZero (p ^ v)] (rho : ZMod (p ^ v)) :
    (vinogradovResidueClassFinset (p ^ v) (p ^ v * Y) rho).card = Y := by
  let z : Fin (p ^ v) :=
    ⟨(rho - 1).val, (rho - 1).val_lt⟩
  have hz : (((z.val + 1 : ℕ) : ZMod (p ^ v))) = rho := by
    rw [Nat.cast_add, Nat.cast_one]
    change (((rho - 1).val : ZMod (p ^ v)) + 1) = rho
    rw [ZMod.natCast_zmod_val]
    exact sub_add_cancel rho 1
  rw [← hz]
  exact card_vinogradovResidueClassFinset_completeBlock p v Y z

/-- A complete block at the finer scale `v` contains exactly
`p^(v-u) * Y` points in each coarser class at scale `u`. -/
theorem card_vinogradovResidueClassFinset_nestedPrimePowerBlock
    (p u v Y : ℕ) (huv : u ≤ v)
    [NeZero (p ^ u)] [NeZero (p ^ v)] (rho : ZMod (p ^ u)) :
    (vinogradovResidueClassFinset (p ^ u) (p ^ v * Y) rho).card =
      p ^ (v - u) * Y := by
  have hpow : p ^ v = p ^ u * p ^ (v - u) := by
    rw [← pow_add, Nat.add_sub_of_le huv]
  rw [hpow, mul_assoc]
  exact card_vinogradovResidueClassFinset_completePrimePowerBlock
    p u (p ^ (v - u) * Y) rho

/-- On a nested complete block, the constant-coefficient raw-conversion
factor at the coarse scale is `(p^(v-u) * Y)^(t-1)`. -/
theorem vinogradovResidueMass_one_evenPow_eq_nestedPrimePowerBlock_pow
    (p u v Y t : ℕ) (huv : u ≤ v)
    [NeZero (p ^ u)] [NeZero (p ^ v)]
    (rho : ZMod (p ^ u)) (ht : 1 ≤ t) :
    vinogradovResidueMass (p ^ u) (p ^ v * Y) rho
        (fun _ : Fin (p ^ v * Y) ↦ (1 : ℂ)) ^ (2 * t - 2) =
      ((p ^ (v - u) * Y : ℕ) : ℝ≥0) ^ (t - 1) := by
  rw [vinogradovResidueMass_one_evenPow_eq_card_pow
      (p ^ u) (p ^ v * Y) t rho ht,
    card_vinogradovResidueClassFinset_nestedPrimePowerBlock p u v Y huv]

/-- Constant coefficients expose the exact cardinality cost hidden by the
normalized mixed residue moment. -/
theorem vinogradovMixedNormalizedResidueMoment_one_to_raw
    (p B a b k r t X Y Q : ℕ)
    [NeZero (p ^ B)] [NeZero Q]
    (xi eta : ℤ) (rho : ZMod Q) (ht : 1 ≤ t) :
    ((vinogradovResidueClassFinset Q Y rho).card : ℝ≥0) ^ (t - 1) *
        vinogradovMixedNormalizedResidueMoment
          p B a b k r t X Y Q xi eta rho
            (fun _ : Fin Y ↦ (1 : ℂ)) =
      vinogradovMixedRawResidueNormMoment
        p B a b k r t X Y Q xi eta rho
          (fun _ : Fin Y ↦ (1 : ℂ)) := by
  rw [← vinogradovResidueMass_one_evenPow_eq_card_pow Q Y t rho ht]
  exact vinogradovMixedNormalizedResidueMoment_to_raw
    p B a b k r t X Y Q xi eta rho (fun _ : Fin Y ↦ (1 : ℂ)) ht

/-- On a complete fine block with constant coefficients, converting the
normalized prime-power refinement back to raw moments recovers exactly the
ordinary Holder loss `p^((v-u)(2t-1))`. Thus normalization alone creates no
new exponent saving in the uniform-mass case. -/
theorem vinogradovMixedRawResidueNormMoment_one_le_refinement_via_normalized
    (p B a b k r t X Y u v : ℕ) [Fact p.Prime]
    [NeZero (p ^ B)] [NeZero (p ^ u)] [NeZero (p ^ v)]
    (huv : u ≤ v) (xi eta : ℤ) (rho : ZMod (p ^ u)) (ht : 1 ≤ t) :
    vinogradovMixedRawResidueNormMoment
        p B a b k r t X (p ^ v * Y) (p ^ u) xi eta rho
          (fun _ : Fin (p ^ v * Y) ↦ (1 : ℂ)) ≤
      (((p ^ (v - u) : ℕ) : ℝ≥0) ^ (2 * t - 1)) *
        ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ v) ↦
          ZMod.castHom (pow_dvd_pow p huv) (ZMod (p ^ u)) z = rho),
          vinogradovMixedRawResidueNormMoment
            p B a b k r t X (p ^ v * Y) (p ^ v) xi eta z
              (fun _ : Fin (p ^ v * Y) ↦ (1 : ℂ)) := by
  let q : ℝ≥0 := ((p ^ (v - u) : ℕ) : ℝ≥0)
  let y : ℝ≥0 := (Y : ℝ≥0)
  let S : Finset (ZMod (p ^ v)) :=
    Finset.univ.filter fun z : ZMod (p ^ v) ↦
      ZMod.castHom (pow_dvd_pow p huv) (ZMod (p ^ u)) z = rho
  let coarseNormalized : ℝ≥0 :=
    vinogradovMixedNormalizedResidueMoment
      p B a b k r t X (p ^ v * Y) (p ^ u) xi eta rho
        (fun _ : Fin (p ^ v * Y) ↦ (1 : ℂ))
  let fineNormalized : ZMod (p ^ v) → ℝ≥0 := fun z ↦
    vinogradovMixedNormalizedResidueMoment
      p B a b k r t X (p ^ v * Y) (p ^ v) xi eta z
        (fun _ : Fin (p ^ v * Y) ↦ (1 : ℂ))
  let coarseRaw : ℝ≥0 :=
    vinogradovMixedRawResidueNormMoment
      p B a b k r t X (p ^ v * Y) (p ^ u) xi eta rho
        (fun _ : Fin (p ^ v * Y) ↦ (1 : ℂ))
  let fineRaw : ZMod (p ^ v) → ℝ≥0 := fun z ↦
    vinogradovMixedRawResidueNormMoment
      p B a b k r t X (p ^ v * Y) (p ^ v) xi eta z
        (fun _ : Fin (p ^ v * Y) ↦ (1 : ℂ))
  have hnormalized : coarseNormalized ≤
      q ^ t * ∑ z ∈ S, fineNormalized z := by
    simpa only [q, S, coarseNormalized, fineNormalized] using
      (vinogradovMixedNormalizedResidueMoment_le_refinement
        p B a b k r t X (p ^ v * Y) u v huv xi eta rho
          (fun _ : Fin (p ^ v * Y) ↦ (1 : ℂ)) ht)
  have hcoarse :
      (q * y) ^ (t - 1) * coarseNormalized = coarseRaw := by
    have hraw := vinogradovMixedNormalizedResidueMoment_one_to_raw
      p B a b k r t X (p ^ v * Y) (p ^ u) xi eta rho ht
    rw [card_vinogradovResidueClassFinset_nestedPrimePowerBlock
      p u v Y huv] at hraw
    simpa only [q, y, coarseNormalized, coarseRaw, Nat.cast_mul] using hraw
  have hfine (z : ZMod (p ^ v)) :
      y ^ (t - 1) * fineNormalized z = fineRaw z := by
    have hraw := vinogradovMixedNormalizedResidueMoment_one_to_raw
      p B a b k r t X (p ^ v * Y) (p ^ v) xi eta z ht
    rw [card_vinogradovResidueClassFinset_completePrimePowerBlock
      p v Y z] at hraw
    simpa only [y, fineNormalized, fineRaw] using hraw
  have hexponent : (t - 1) + t = 2 * t - 1 := by omega
  change coarseRaw ≤ q ^ (2 * t - 1) * ∑ z ∈ S, fineRaw z
  calc
    coarseRaw = (q * y) ^ (t - 1) * coarseNormalized := hcoarse.symm
    _ ≤ (q * y) ^ (t - 1) *
        (q ^ t * ∑ z ∈ S, fineNormalized z) :=
      mul_le_mul_right hnormalized _
    _ = (q ^ (t - 1) * q ^ t) *
        (y ^ (t - 1) * ∑ z ∈ S, fineNormalized z) := by
      rw [mul_pow]
      ring
    _ = q ^ (2 * t - 1) *
        (y ^ (t - 1) * ∑ z ∈ S, fineNormalized z) := by
      rw [← pow_add, hexponent]
    _ = q ^ (2 * t - 1) *
        ∑ z ∈ S, y ^ (t - 1) * fineNormalized z := by
      rw [Finset.mul_sum]
    _ = q ^ (2 * t - 1) * ∑ z ∈ S, fineRaw z := by
      congr 1
      apply Finset.sum_congr rfl
      intro z hz
      exact hfine z

end

end ZeroFreeRegion.VinogradovKorobov
