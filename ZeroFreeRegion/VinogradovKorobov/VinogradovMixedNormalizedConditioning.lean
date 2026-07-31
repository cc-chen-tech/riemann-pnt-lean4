import ZeroFreeRegion.VinogradovKorobov.VinogradovNormalizedConditionedMoment
import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedMoment

open scoped BigOperators NNReal

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- A normalized residue moment with an arbitrary nonnegative weight on the
outer phase space.  This is the form needed to retain a main Weyl block while
conditioning the tail coefficient sequence. -/
noncomputable def vinogradovOuterWeightedNormalizedConditionedMoment
    {C : Type*} [Fintype C]
    (Q X w : ℕ) [NeZero Q] (rho : ZMod Q)
    (coefficient : Fin X → ℂ) (phase : C → Fin X → ℂ)
    (outerWeight : C → ℝ≥0) : ℝ≥0 :=
  ∑ c : C, outerWeight c *
    (vinogradovResidueMass Q X rho coefficient ^ 2 *
      vinogradovNormalizedResidueNorm
        Q X rho coefficient (phase c) ^ (2 * w))

/-- Wooley's normalized prime-power conditioning inequality remains valid
after multiplication by an arbitrary nonnegative outer weight and summation
over the outer phase space. -/
theorem vinogradovOuterWeightedNormalizedConditionedMoment_le_refinement
    {C : Type*} [Fintype C]
    (p u v X w : ℕ) (hp : 0 < p) (huv : u ≤ v)
    [NeZero (p ^ u)] [NeZero (p ^ v)]
    (rho : ZMod (p ^ u)) (coefficient : Fin X → ℂ)
    (phase : C → Fin X → ℂ) (outerWeight : C → ℝ≥0)
    (hw : 1 ≤ w) :
    vinogradovOuterWeightedNormalizedConditionedMoment
        (p ^ u) X w rho coefficient phase outerWeight ≤
      (((p ^ (v - u) : ℕ) : ℝ≥0) ^ w) *
        ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ v) ↦
          ZMod.castHom (pow_dvd_pow p huv) (ZMod (p ^ u)) z = rho),
          vinogradovOuterWeightedNormalizedConditionedMoment
            (p ^ v) X w z coefficient phase outerWeight := by
  classical
  let K : ℝ≥0 := (((p ^ (v - u) : ℕ) : ℝ≥0) ^ w)
  let S : Finset (ZMod (p ^ v)) :=
    Finset.univ.filter fun z : ZMod (p ^ v) ↦
      ZMod.castHom (pow_dvd_pow p huv) (ZMod (p ^ u)) z = rho
  let coarse : C → ℝ≥0 := fun c ↦
    vinogradovResidueMass (p ^ u) X rho coefficient ^ 2 *
      vinogradovNormalizedResidueNorm
        (p ^ u) X rho coefficient (phase c) ^ (2 * w)
  let fine : C → ZMod (p ^ v) → ℝ≥0 := fun c z ↦
    vinogradovResidueMass (p ^ v) X z coefficient ^ 2 *
      vinogradovNormalizedResidueNorm
        (p ^ v) X z coefficient (phase c) ^ (2 * w)
  have hpoint (c : C) :
      coarse c ≤ K * ∑ z ∈ S, fine c z := by
    simpa only [K, S, coarse, fine] using
      (normalized_vinogradovResidueNorm_primePower_refinement
        p u v X hp huv rho coefficient (phase c) w hw)
  unfold vinogradovOuterWeightedNormalizedConditionedMoment
  change (∑ c : C, outerWeight c * coarse c) ≤
    K * ∑ z ∈ S, ∑ c : C, outerWeight c * fine c z
  calc
    (∑ c : C, outerWeight c * coarse c) ≤
        ∑ c : C, outerWeight c * (K * ∑ z ∈ S, fine c z) := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_right (hpoint c) (outerWeight c)
    _ = K * ∑ z ∈ S, ∑ c : C, outerWeight c * fine c z := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp [mul_left_comm]

/-- Multiplying a normalized residue moment by the missing coefficient-mass
power recovers the corresponding raw norm power.  This identity records
exactly where normalized conditioning gains can be lost when converted back
to unweighted Weyl sums. -/
theorem vinogradovResidueMass_pow_mul_normalizedMoment_eq_norm_pow
    (Q X w : ℕ) [NeZero Q] (rho : ZMod Q)
    (coefficient phase : Fin X → ℂ) (hw : 1 ≤ w) :
    vinogradovResidueMass Q X rho coefficient ^ (2 * w - 2) *
        (vinogradovResidueMass Q X rho coefficient ^ 2 *
          vinogradovNormalizedResidueNorm
            Q X rho coefficient phase ^ (2 * w)) =
      ‖vinogradovResidueWeightedSum
        Q X rho coefficient phase‖₊ ^ (2 * w) := by
  have hmass :=
    vinogradovResidueMass_mul_normalizedResidueNorm
      Q X rho coefficient phase
  calc
    vinogradovResidueMass Q X rho coefficient ^ (2 * w - 2) *
        (vinogradovResidueMass Q X rho coefficient ^ 2 *
          vinogradovNormalizedResidueNorm
            Q X rho coefficient phase ^ (2 * w)) =
      (vinogradovResidueMass Q X rho coefficient *
        vinogradovNormalizedResidueNorm
          Q X rho coefficient phase) ^ (2 * w) := by
        rw [mul_pow]
        calc
          vinogradovResidueMass Q X rho coefficient ^ (2 * w - 2) *
              (vinogradovResidueMass Q X rho coefficient ^ 2 *
                vinogradovNormalizedResidueNorm
                  Q X rho coefficient phase ^ (2 * w)) =
            (vinogradovResidueMass Q X rho coefficient ^ (2 * w - 2) *
              vinogradovResidueMass Q X rho coefficient ^ 2) *
                vinogradovNormalizedResidueNorm
                  Q X rho coefficient phase ^ (2 * w) := by
              rw [mul_assoc]
          _ = vinogradovResidueMass Q X rho coefficient ^
                ((2 * w - 2) + 2) *
              vinogradovNormalizedResidueNorm
                Q X rho coefficient phase ^ (2 * w) := by
            rw [← pow_add]
          _ = vinogradovResidueMass Q X rho coefficient ^ (2 * w) *
              vinogradovNormalizedResidueNorm
                Q X rho coefficient phase ^ (2 * w) := by
            congr 2
            omega
    _ = ‖vinogradovResidueWeightedSum
          Q X rho coefficient phase‖₊ ^ (2 * w) := by
      rw [hmass]

/-- Raw-sum form of an outer-weighted normalized residue moment.  The residue
mass is independent of the outer phase parameter and therefore factors out
of the complete outer average. -/
theorem vinogradovOuterWeightedNormalizedConditionedMoment_to_raw
    {C : Type*} [Fintype C]
    (Q X w : ℕ) [NeZero Q] (rho : ZMod Q)
    (coefficient : Fin X → ℂ) (phase : C → Fin X → ℂ)
    (outerWeight : C → ℝ≥0) (hw : 1 ≤ w) :
    vinogradovResidueMass Q X rho coefficient ^ (2 * w - 2) *
        vinogradovOuterWeightedNormalizedConditionedMoment
          Q X w rho coefficient phase outerWeight =
      ∑ c : C, outerWeight c *
        ‖vinogradovResidueWeightedSum
          Q X rho coefficient (phase c)‖₊ ^ (2 * w) := by
  unfold vinogradovOuterWeightedNormalizedConditionedMoment
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro c
  calc
    vinogradovResidueMass Q X rho coefficient ^ (2 * w - 2) *
        (outerWeight c *
          (vinogradovResidueMass Q X rho coefficient ^ 2 *
            vinogradovNormalizedResidueNorm
              Q X rho coefficient (phase c) ^ (2 * w))) =
      outerWeight c *
        (vinogradovResidueMass Q X rho coefficient ^ (2 * w - 2) *
          (vinogradovResidueMass Q X rho coefficient ^ 2 *
            vinogradovNormalizedResidueNorm
              Q X rho coefficient (phase c) ^ (2 * w))) := by
        ac_rfl
    _ = outerWeight c *
        ‖vinogradovResidueWeightedSum
          Q X rho coefficient (phase c)‖₊ ^ (2 * w) := by
      rw [vinogradovResidueMass_pow_mul_normalizedMoment_eq_norm_pow
        Q X w rho coefficient (phase c) hw]

/-- The affine tail phase indexed by the common Fourier coefficient vector. -/
noncomputable def vinogradovMixedTailPhaseTerm
    (p B b k Y : ℕ) [NeZero (p ^ B)] (eta : ℤ)
    (c : Fin k → ZMod (p ^ B)) (m : Fin Y) : ℂ :=
  ZMod.stdAddChar
    (vinogradovIntPhaseMod (p ^ B) c
      (vinogradovMixedTailValue p b Y eta m))

/-- The main Weyl block supplies the nonnegative outer weight retained while
the tail coefficient sequence is conditioned. -/
noncomputable def vinogradovMixedMainOuterWeight
    (p B a k r X : ℕ) [NeZero (p ^ B)] (xi : ℤ)
    (c : Fin k → ZMod (p ^ B)) : ℝ≥0 :=
  ‖vinogradovMixedMainWeylSum p a (p ^ B) k X xi c‖₊ ^ (2 * r)

/-- Main-weighted normalized residue moment for an arbitrary complex tail
coefficient sequence.  The common Fourier average is normalized exactly as
in `normalizedVinogradovMixedModConditionedMoment`. -/
noncomputable def vinogradovMixedNormalizedResidueMoment
    (p B a b k r t X Y Q : ℕ)
    [NeZero (p ^ B)] [NeZero Q]
    (xi eta : ℤ) (rho : ZMod Q) (coefficient : Fin Y → ℂ) : ℝ≥0 :=
  (((p ^ B : ℕ) : ℝ≥0)⁻¹ ^ k) *
    vinogradovOuterWeightedNormalizedConditionedMoment
      Q Y t rho coefficient
        (fun c : Fin k → ZMod (p ^ B) ↦
          vinogradovMixedTailPhaseTerm p B b k Y eta c)
        (vinogradovMixedMainOuterWeight p B a k r X xi)

/-- Prime-power conditioning of the tail preserves the main Weyl weight and
supports arbitrary complex tail coefficients.  The exact normalized loss is
`p^((v-u)t)`, before any conversion back to raw unnormalized residue sums. -/
theorem vinogradovMixedNormalizedResidueMoment_le_refinement
    (p B a b k r t X Y u v : ℕ) [Fact p.Prime]
    [NeZero (p ^ B)] [NeZero (p ^ u)] [NeZero (p ^ v)]
    (huv : u ≤ v) (xi eta : ℤ) (rho : ZMod (p ^ u))
    (coefficient : Fin Y → ℂ) (ht : 1 ≤ t) :
    vinogradovMixedNormalizedResidueMoment
        p B a b k r t X Y (p ^ u) xi eta rho coefficient ≤
      (((p ^ (v - u) : ℕ) : ℝ≥0) ^ t) *
        ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ v) ↦
          ZMod.castHom (pow_dvd_pow p huv) (ZMod (p ^ u)) z = rho),
          vinogradovMixedNormalizedResidueMoment
            p B a b k r t X Y (p ^ v) xi eta z coefficient := by
  let q : ℝ≥0 := (((p ^ B : ℕ) : ℝ≥0)⁻¹ ^ k)
  let K : ℝ≥0 := (((p ^ (v - u) : ℕ) : ℝ≥0) ^ t)
  let S : Finset (ZMod (p ^ v)) :=
    Finset.univ.filter fun z : ZMod (p ^ v) ↦
      ZMod.castHom (pow_dvd_pow p huv) (ZMod (p ^ u)) z = rho
  have hrefine :=
    vinogradovOuterWeightedNormalizedConditionedMoment_le_refinement
      (C := Fin k → ZMod (p ^ B))
      p u v Y t (Fact.out : p.Prime).pos huv rho coefficient
        (fun c : Fin k → ZMod (p ^ B) ↦
          vinogradovMixedTailPhaseTerm p B b k Y eta c)
        (vinogradovMixedMainOuterWeight p B a k r X xi) ht
  unfold vinogradovMixedNormalizedResidueMoment
  change q *
      vinogradovOuterWeightedNormalizedConditionedMoment
        (p ^ u) Y t rho coefficient
          (fun c : Fin k → ZMod (p ^ B) ↦
            vinogradovMixedTailPhaseTerm p B b k Y eta c)
          (vinogradovMixedMainOuterWeight p B a k r X xi) ≤
    K * ∑ z ∈ S, q *
      vinogradovOuterWeightedNormalizedConditionedMoment
        (p ^ v) Y t z coefficient
          (fun c : Fin k → ZMod (p ^ B) ↦
            vinogradovMixedTailPhaseTerm p B b k Y eta c)
          (vinogradovMixedMainOuterWeight p B a k r X xi)
  calc
    q *
        vinogradovOuterWeightedNormalizedConditionedMoment
          (p ^ u) Y t rho coefficient
            (fun c : Fin k → ZMod (p ^ B) ↦
              vinogradovMixedTailPhaseTerm p B b k Y eta c)
            (vinogradovMixedMainOuterWeight p B a k r X xi) ≤
      q * (K * ∑ z ∈ S,
        vinogradovOuterWeightedNormalizedConditionedMoment
          (p ^ v) Y t z coefficient
            (fun c : Fin k → ZMod (p ^ B) ↦
              vinogradovMixedTailPhaseTerm p B b k Y eta c)
            (vinogradovMixedMainOuterWeight p B a k r X xi)) :=
      mul_le_mul_right hrefine q
    _ = K * ∑ z ∈ S, q *
        vinogradovOuterWeightedNormalizedConditionedMoment
          (p ^ v) Y t z coefficient
            (fun c : Fin k → ZMod (p ^ B) ↦
              vinogradovMixedTailPhaseTerm p B b k Y eta c)
            (vinogradovMixedMainOuterWeight p B a k r X xi) := by
      simp_rw [Finset.mul_sum]
      simp [mul_left_comm]

/-- Raw main-weighted norm moment of a tail coefficient sequence in one
internal-index residue class. -/
noncomputable def vinogradovMixedRawResidueNormMoment
    (p B a b k r t X Y Q : ℕ)
    [NeZero (p ^ B)] [NeZero Q]
    (xi eta : ℤ) (rho : ZMod Q) (coefficient : Fin Y → ℂ) : ℝ≥0 :=
  (((p ^ B : ℕ) : ℝ≥0)⁻¹ ^ k) *
    ∑ c : Fin k → ZMod (p ^ B),
      vinogradovMixedMainOuterWeight p B a k r X xi c *
        ‖vinogradovResidueWeightedSum Q Y rho coefficient
          (vinogradovMixedTailPhaseTerm p B b k Y eta c)‖₊ ^ (2 * t)

/-- Exact bridge from the normalized mixed residue moment back to the raw
main-weighted residue moment.  The conversion cost is precisely the
coefficient-mass power `rho_Q(rho)^(2t-2)`. -/
theorem vinogradovMixedNormalizedResidueMoment_to_raw
    (p B a b k r t X Y Q : ℕ)
    [NeZero (p ^ B)] [NeZero Q]
    (xi eta : ℤ) (rho : ZMod Q) (coefficient : Fin Y → ℂ)
    (ht : 1 ≤ t) :
    vinogradovResidueMass Q Y rho coefficient ^ (2 * t - 2) *
        vinogradovMixedNormalizedResidueMoment
          p B a b k r t X Y Q xi eta rho coefficient =
      vinogradovMixedRawResidueNormMoment
        p B a b k r t X Y Q xi eta rho coefficient := by
  unfold vinogradovMixedNormalizedResidueMoment
  unfold vinogradovMixedRawResidueNormMoment
  let q : ℝ≥0 := (((p ^ B : ℕ) : ℝ≥0)⁻¹ ^ k)
  change
    vinogradovResidueMass Q Y rho coefficient ^ (2 * t - 2) *
        (q *
          vinogradovOuterWeightedNormalizedConditionedMoment
            Q Y t rho coefficient
              (fun c : Fin k → ZMod (p ^ B) ↦
                vinogradovMixedTailPhaseTerm p B b k Y eta c)
              (vinogradovMixedMainOuterWeight p B a k r X xi)) =
      q * ∑ c : Fin k → ZMod (p ^ B),
        vinogradovMixedMainOuterWeight p B a k r X xi c *
          ‖vinogradovResidueWeightedSum Q Y rho coefficient
            (vinogradovMixedTailPhaseTerm p B b k Y eta c)‖₊ ^ (2 * t)
  calc
    vinogradovResidueMass Q Y rho coefficient ^ (2 * t - 2) *
        (q *
          vinogradovOuterWeightedNormalizedConditionedMoment
            Q Y t rho coefficient
              (fun c : Fin k → ZMod (p ^ B) ↦
                vinogradovMixedTailPhaseTerm p B b k Y eta c)
              (vinogradovMixedMainOuterWeight p B a k r X xi)) =
      q * (vinogradovResidueMass Q Y rho coefficient ^ (2 * t - 2) *
        vinogradovOuterWeightedNormalizedConditionedMoment
          Q Y t rho coefficient
            (fun c : Fin k → ZMod (p ^ B) ↦
              vinogradovMixedTailPhaseTerm p B b k Y eta c)
            (vinogradovMixedMainOuterWeight p B a k r X xi)) := by
        ac_rfl
    _ = q * ∑ c : Fin k → ZMod (p ^ B),
        vinogradovMixedMainOuterWeight p B a k r X xi c *
          ‖vinogradovResidueWeightedSum Q Y rho coefficient
            (vinogradovMixedTailPhaseTerm p B b k Y eta c)‖₊ ^
              (2 * t) := by
      rw [vinogradovOuterWeightedNormalizedConditionedMoment_to_raw
        Q Y t rho coefficient
          (fun c : Fin k → ZMod (p ^ B) ↦
            vinogradovMixedTailPhaseTerm p B b k Y eta c)
          (vinogradovMixedMainOuterWeight p B a k r X xi) ht]

end

end ZeroFreeRegion.VinogradovKorobov
