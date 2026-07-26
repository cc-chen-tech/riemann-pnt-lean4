import ZeroFreeRegion.VinogradovKorobov.VinogradovNormalizedConditioning
import ZeroFreeRegion.VinogradovKorobov.VinogradovWeightedMoment

open scoped BigOperators NNReal

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- A finite average of normalized residue sums.  This is the discrete
coefficient-space analogue of the normalized conditioned moments in efficient
congruencing. -/
def vinogradovNormalizedConditionedMoment
    {C : Type*} [Fintype C]
    (Q X w : ℕ) [NeZero Q] (ξ : ZMod Q)
    (coefficient : Fin X → ℂ) (phase : C → Fin X → ℂ) : ℝ≥0 :=
  ∑ c : C, vinogradovResidueMass Q X ξ coefficient ^ 2 *
    vinogradovNormalizedResidueNorm Q X ξ coefficient (phase c) ^ (2 * w)

/-- Summing the pointwise normalized conditioning inequality over an arbitrary
finite phase space preserves the exact prime-power loss. -/
theorem vinogradovNormalizedConditionedMoment_le_refinement
    {C : Type*} [Fintype C]
    (p a b X w : ℕ) (hp : 0 < p) (hab : a ≤ b)
    [NeZero (p ^ a)] [NeZero (p ^ b)]
    (ξ : ZMod (p ^ a)) (coefficient : Fin X → ℂ)
    (phase : C → Fin X → ℂ) (hw : 1 ≤ w) :
    vinogradovNormalizedConditionedMoment
        (p ^ a) X w ξ coefficient phase ≤
      (((p ^ (b - a) : ℕ) : ℝ≥0) ^ w) *
        ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
          ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
          vinogradovNormalizedConditionedMoment
            (p ^ b) X w z coefficient phase := by
  unfold vinogradovNormalizedConditionedMoment
  calc
    (∑ c : C, vinogradovResidueMass (p ^ a) X ξ coefficient ^ 2 *
        vinogradovNormalizedResidueNorm
          (p ^ a) X ξ coefficient (phase c) ^ (2 * w)) ≤
      ∑ c : C, (((p ^ (b - a) : ℕ) : ℝ≥0) ^ w) *
        ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
          ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
          vinogradovResidueMass (p ^ b) X z coefficient ^ 2 *
            vinogradovNormalizedResidueNorm
              (p ^ b) X z coefficient (phase c) ^ (2 * w) := by
        apply Finset.sum_le_sum
        intro c hc
        exact normalized_vinogradovResidueNorm_primePower_refinement
          p a b X hp hab ξ coefficient (phase c) w hw
    _ = (((p ^ (b - a) : ℕ) : ℝ≥0) ^ w) *
        ∑ c : C, ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
          ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
          vinogradovResidueMass (p ^ b) X z coefficient ^ 2 *
            vinogradovNormalizedResidueNorm
              (p ^ b) X z coefficient (phase c) ^ (2 * w) := by
        rw [Finset.mul_sum]
    _ = (((p ^ (b - a) : ℕ) : ℝ≥0) ^ w) *
        ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
          ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
          ∑ c : C, vinogradovResidueMass (p ^ b) X z coefficient ^ 2 *
            vinogradovNormalizedResidueNorm
              (p ^ b) X z coefficient (phase c) ^ (2 * w) := by
        congr 1
        rw [Finset.sum_comm]

/-- The normalized conditioned moment for the finite degree-weighted Weyl
coefficient space. -/
def vinogradovWeightedNormalizedConditionedMoment
    (p coefficientScale k X Q w : ℕ) [Fact p.Prime] [NeZero Q]
    (ξ : ZMod Q) (coefficient : Fin X → ℂ) : ℝ≥0 :=
  vinogradovNormalizedConditionedMoment Q X w ξ coefficient
    (fun c : VinogradovWeightedCoefficient p coefficientScale k ↦
      vinogradovWeightedPhaseTerm p coefficientScale c)

/-- Wooley's normalized conditioning step specialized to the finite
degree-weighted Weyl coefficient space. -/
theorem vinogradovWeightedNormalizedConditionedMoment_le_refinement
    (p coefficientScale k X a b w : ℕ) [Fact p.Prime]
    (hab : a ≤ b) [NeZero (p ^ a)] [NeZero (p ^ b)]
    (ξ : ZMod (p ^ a)) (coefficient : Fin X → ℂ) (hw : 1 ≤ w) :
    vinogradovWeightedNormalizedConditionedMoment
        p coefficientScale k X (p ^ a) w ξ coefficient ≤
      (((p ^ (b - a) : ℕ) : ℝ≥0) ^ w) *
        ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
          ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
          vinogradovWeightedNormalizedConditionedMoment
            p coefficientScale k X (p ^ b) w z coefficient := by
  exact vinogradovNormalizedConditionedMoment_le_refinement
    (C := VinogradovWeightedCoefficient p coefficientScale k)
    p a b X w (Fact.out : p.Prime).pos hab ξ coefficient
      (fun c ↦ vinogradovWeightedPhaseTerm p coefficientScale c) hw

end

end ZeroFreeRegion.VinogradovKorobov
