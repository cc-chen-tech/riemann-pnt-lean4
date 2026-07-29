import ZeroFreeRegion.VinogradovKorobov.VinogradovResidueMassAudit

open scoped BigOperators NNReal

open ZeroFreeRegion.VinogradovKorobov

example (Q X : ℕ) [NeZero Q] (rho : ZMod Q) :
    vinogradovResidueMassSq Q X rho (fun _ : Fin X ↦ (1 : ℂ)) =
      ((vinogradovResidueClassFinset Q X rho).card : ℝ≥0) :=
  vinogradovResidueMassSq_one_eq_card Q X rho

example (Q X : ℕ) [NeZero Q] (rho : ZMod Q) :
    vinogradovResidueMass Q X rho (fun _ : Fin X ↦ (1 : ℂ)) ^ 2 =
      ((vinogradovResidueClassFinset Q X rho).card : ℝ≥0) :=
  vinogradovResidueMass_one_sq_eq_card Q X rho

example (Q X t : ℕ) [NeZero Q] (rho : ZMod Q) (ht : 1 ≤ t) :
    vinogradovResidueMass Q X rho (fun _ : Fin X ↦ (1 : ℂ)) ^
        (2 * t - 2) =
      ((vinogradovResidueClassFinset Q X rho).card : ℝ≥0) ^ (t - 1) :=
  vinogradovResidueMass_one_evenPow_eq_card_pow Q X t rho ht

example (p Y : ℕ) [Fact p.Prime] [NeZero p] (rho : ZMod p) :
    vinogradovResidueMassSq p Y rho (fun _ : Fin Y ↦ (1 : ℂ)) =
      (vinogradovTailResidueLength p Y rho : ℝ≥0) :=
  vinogradovResidueMassSq_one_eq_tailResidueLength p Y rho

example (p Y t : ℕ) [Fact p.Prime] [NeZero p]
    (rho : ZMod p) (ht : 1 ≤ t) :
    vinogradovResidueMass p Y rho (fun _ : Fin Y ↦ (1 : ℂ)) ^
        (2 * t - 2) =
      (vinogradovTailResidueLength p Y rho : ℝ≥0) ^ (t - 1) :=
  vinogradovResidueMass_one_evenPow_eq_tailResidueLength_pow p Y t rho ht

example (p B a b k r t X Y Q : ℕ)
    [NeZero (p ^ B)] [NeZero Q]
    (xi eta : ℤ) (rho : ZMod Q) (ht : 1 ≤ t) :
    ((vinogradovResidueClassFinset Q Y rho).card : ℝ≥0) ^ (t - 1) *
        vinogradovMixedNormalizedResidueMoment
          p B a b k r t X Y Q xi eta rho
            (fun _ : Fin Y ↦ (1 : ℂ)) =
      vinogradovMixedRawResidueNormMoment
        p B a b k r t X Y Q xi eta rho
          (fun _ : Fin Y ↦ (1 : ℂ)) :=
  vinogradovMixedNormalizedResidueMoment_one_to_raw
    p B a b k r t X Y Q xi eta rho ht

example (p v Y : ℕ) [NeZero (p ^ v)] (rho : ZMod (p ^ v)) :
    (vinogradovResidueClassFinset (p ^ v) (p ^ v * Y) rho).card = Y :=
  card_vinogradovResidueClassFinset_completePrimePowerBlock p v Y rho

example (p u v Y : ℕ) (huv : u ≤ v)
    [NeZero (p ^ u)] [NeZero (p ^ v)] (rho : ZMod (p ^ u)) :
    (vinogradovResidueClassFinset (p ^ u) (p ^ v * Y) rho).card =
      p ^ (v - u) * Y :=
  card_vinogradovResidueClassFinset_nestedPrimePowerBlock
    p u v Y huv rho

example (p u v Y t : ℕ) (huv : u ≤ v)
    [NeZero (p ^ u)] [NeZero (p ^ v)]
    (rho : ZMod (p ^ u)) (ht : 1 ≤ t) :
    vinogradovResidueMass (p ^ u) (p ^ v * Y) rho
        (fun _ : Fin (p ^ v * Y) ↦ (1 : ℂ)) ^ (2 * t - 2) =
      ((p ^ (v - u) * Y : ℕ) : ℝ≥0) ^ (t - 1) :=
  vinogradovResidueMass_one_evenPow_eq_nestedPrimePowerBlock_pow
    p u v Y t huv rho ht

example (p B a b k r t X Y u v : ℕ) [Fact p.Prime]
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
              (fun _ : Fin (p ^ v * Y) ↦ (1 : ℂ)) :=
  vinogradovMixedRawResidueNormMoment_one_le_refinement_via_normalized
    p B a b k r t X Y u v huv xi eta rho ht
