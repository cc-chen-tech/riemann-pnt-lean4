import ZeroFreeRegion.VinogradovKorobov.VinogradovPrimePowerMultiBlock
import ZeroFreeRegion.VinogradovKorobov.VinogradovMultiBlockCollisionFiber

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance vinogradovPrimePowerCollisionFiberPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-- Prime-power tuple pairs whose left tuple realizes one prescribed
collision in every selected block after reduction modulo `p`. -/
noncomputable def vinogradovPrimePowerFixedCollisionAmbientSet
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    Finset (vinogradovPrimePowerBasePair p 0 (b * k + r) n) :=
  Finset.univ.filter fun xy ↦
    ∀ q : Fin b,
      (((xy.1 (Fin.natAdd 0
          (vinogradovCollisionKeptIndex k r b w q))).val + 1 : ℕ) : ZMod p) =
        (((xy.1 (Fin.natAdd 0
          (vinogradovCollisionDeletedIndex k r b w q))).val + 1 : ℕ) : ZMod p)

theorem mem_vinogradovPrimePowerFixedCollisionAmbientSet_iff
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k)
    (xy : vinogradovPrimePowerBasePair p 0 (b * k + r) n) :
    xy ∈ vinogradovPrimePowerFixedCollisionAmbientSet p k r b n w ↔
      ∀ q : Fin b,
        (((xy.1 (Fin.natAdd 0
            (vinogradovCollisionKeptIndex k r b w q))).val + 1 : ℕ) : ZMod p) =
          (((xy.1 (Fin.natAdd 0
            (vinogradovCollisionDeletedIndex k r b w q))).val + 1 : ℕ) : ZMod p) := by
  simp [vinogradovPrimePowerFixedCollisionAmbientSet]

/-- At the first prime level, a fixed collision choice removes one free left
residue coordinate per selected block; the right tuple remains unrestricted. -/
theorem card_vinogradovPrimePowerFixedCollisionAmbientSet_zero
    (p k r b : ℕ) [Fact p.Prime] (hk : 0 < k)
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionAmbientSet p k r b 0 w).card =
      p ^ (b * (k - 1) + r) * p ^ (b * k + r) := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let e := vinogradovPrimePowerMultiBlockBaseZeroEquiv p k r b
  let target :=
    (vinogradovFixedMultiBlockCollisionTupleSet p k r b hk w).product
      (Finset.univ : Finset (Fin (b * k + r) → ZMod p))
  have hcard :
      (vinogradovPrimePowerFixedCollisionAmbientSet
        p k r b 0 w).card = target.card := by
    apply Finset.card_equiv e
    intro xy
    have hxencode : (e xy).1 =
        (fun i ↦ (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p)) := by
      funext i
      simpa [e, vinogradovPrimePowerMultiBlockBaseZeroEquiv,
        vinogradovFirstStratumCompleteResiduePairEquiv,
        vinogradovFirstStratumCompleteResidueEquiv_apply]
    rw [mem_vinogradovPrimePowerFixedCollisionAmbientSet_iff]
    dsimp [target]
    rw [Finset.mem_product]
    simp only [Finset.mem_univ, and_true]
    rw [mem_vinogradovFixedMultiBlockCollisionTupleSet_iff, hxencode]
  calc
    (vinogradovPrimePowerFixedCollisionAmbientSet
        p k r b 0 w).card = target.card := hcard
    _ = p ^ (b * (k - 1) + r) * p ^ (b * k + r) := by
      dsimp [target]
      rw [Finset.card_product,
        card_vinogradovFixedMultiBlockCollisionTupleSet]
      congr 1
      simp [ZMod.card]

/-- A one-digit lift preserves a prescribed collision after reduction modulo
`p`; the new digit is invisible at the base prime level. -/
theorem vinogradovPrimePowerLiftAmbientEquiv_fixedCollision_iff
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k)
    (xy : vinogradovPrimePowerBasePair p 0 (b * k + r) n)
    (z : vinogradovPrimePowerSplitCorrection p 0 (b * k + r)) :
    (∀ q : Fin b,
      (((((vinogradovPrimePowerLiftAmbientEquiv p 0
          (b * k + r) n ⟨xy, z⟩).1
            (Fin.natAdd 0
              (vinogradovCollisionKeptIndex k r b w q))).val + 1 : ℕ)) :
          ZMod p) =
        (((((vinogradovPrimePowerLiftAmbientEquiv p 0
          (b * k + r) n ⟨xy, z⟩).1
            (Fin.natAdd 0
              (vinogradovCollisionDeletedIndex k r b w q))).val + 1 : ℕ)) :
          ZMod p)) ↔
      (∀ q : Fin b,
        (((xy.1 (Fin.natAdd 0
            (vinogradovCollisionKeptIndex k r b w q))).val + 1 : ℕ) :
          ZMod p) =
        (((xy.1 (Fin.natAdd 0
            (vinogradovCollisionDeletedIndex k r b w q))).val + 1 : ℕ) :
          ZMod p)) := by
  simp only [vinogradovPrimePowerLiftAmbientEquiv_fst_mod]

/-- A fixed-collision base pair together with arbitrary next residue digits. -/
noncomputable def vinogradovPrimePowerFixedCollisionAmbientLiftSet
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    Finset
      (Σ _ : vinogradovPrimePowerBasePair p 0 (b * k + r) n,
        vinogradovPrimePowerSplitCorrection p 0 (b * k + r)) :=
  (vinogradovPrimePowerFixedCollisionAmbientSet p k r b n w).sigma
    fun _ ↦ Finset.univ

theorem card_vinogradovPrimePowerFixedCollisionAmbientLiftSet
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionAmbientLiftSet p k r b n w).card =
      (vinogradovPrimePowerFixedCollisionAmbientSet p k r b n w).card *
        p ^ (2 * (b * k + r)) := by
  rw [vinogradovPrimePowerFixedCollisionAmbientLiftSet,
    Finset.card_sigma]
  simp only [Finset.card_univ, Finset.sum_const_nat]
  rw [card_vinogradovPrimePowerSplitCorrection]
  simp only [Nat.zero_add]

/-- Membership in a fixed-collision lift set transports exactly to the same
collision branch at the next prime-power level. -/
theorem
    mem_vinogradovPrimePowerFixedCollisionAmbientLiftSet_iff_image_mem
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k)
    (u : Σ _ : vinogradovPrimePowerBasePair p 0 (b * k + r) n,
      vinogradovPrimePowerSplitCorrection p 0 (b * k + r)) :
    u ∈ vinogradovPrimePowerFixedCollisionAmbientLiftSet p k r b n w ↔
      vinogradovPrimePowerLiftAmbientEquiv p 0 (b * k + r) n u ∈
        vinogradovPrimePowerFixedCollisionAmbientSet p k r b (n + 1) w := by
  rcases u with ⟨xy, z⟩
  simp only [vinogradovPrimePowerFixedCollisionAmbientLiftSet,
    Finset.mem_sigma, Finset.mem_univ, and_true]
  rw [mem_vinogradovPrimePowerFixedCollisionAmbientSet_iff,
    mem_vinogradovPrimePowerFixedCollisionAmbientSet_iff]
  exact
    (vinogradovPrimePowerLiftAmbientEquiv_fixedCollision_iff
      p k r b n w xy z).symm

/-- The digit-lift equivalence maps the complete fixed-collision lift space
onto the next-level fixed-collision ambient set. -/
theorem map_vinogradovPrimePowerFixedCollisionAmbientLiftSet_eq
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionAmbientLiftSet p k r b n w).map
        (vinogradovPrimePowerLiftAmbientEquiv p 0
          (b * k + r) n).toEmbedding =
      vinogradovPrimePowerFixedCollisionAmbientSet p k r b (n + 1) w := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_map.mp hv with ⟨u, hu, rfl⟩
    exact
      (mem_vinogradovPrimePowerFixedCollisionAmbientLiftSet_iff_image_mem
        p k r b n w u).mp hu
  · intro hv
    let e := vinogradovPrimePowerLiftAmbientEquiv p 0 (b * k + r) n
    let u := e.symm v
    have heu : e u = v := e.apply_symm_apply v
    apply Finset.mem_map.mpr
    refine ⟨u, ?_, heu⟩
    apply
      (mem_vinogradovPrimePowerFixedCollisionAmbientLiftSet_iff_image_mem
        p k r b n w u).mpr
    simpa [e, u] using hv

/-- Exact one-step recurrence for a fixed prime-power collision branch. -/
theorem card_vinogradovPrimePowerFixedCollisionAmbientSet_succ
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionAmbientSet
      p k r b (n + 1) w).card =
      (vinogradovPrimePowerFixedCollisionAmbientSet p k r b n w).card *
        p ^ (2 * (b * k + r)) := by
  rw [← map_vinogradovPrimePowerFixedCollisionAmbientLiftSet_eq
      p k r b n w,
    Finset.card_map,
    card_vinogradovPrimePowerFixedCollisionAmbientLiftSet]

/-- Every prime-power level reduces to the first fixed-collision fiber and
unrestricted higher digits. -/
theorem card_vinogradovPrimePowerFixedCollisionAmbientSet_eq_base_mul_pow
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionAmbientSet p k r b n w).card =
      (vinogradovPrimePowerFixedCollisionAmbientSet p k r b 0 w).card *
        (p ^ (2 * (b * k + r))) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [card_vinogradovPrimePowerFixedCollisionAmbientSet_succ,
        ih, pow_succ, mul_assoc]

/-- Exact ambient cardinality of one fixed collision pattern at every
prime-power level. -/
theorem card_vinogradovPrimePowerFixedCollisionAmbientSet
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k)
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionAmbientSet p k r b n w).card =
      (p ^ (b * (k - 1) + r) * p ^ (b * k + r)) *
        (p ^ (2 * (b * k + r))) ^ n := by
  rw [card_vinogradovPrimePowerFixedCollisionAmbientSet_eq_base_mul_pow,
    card_vinogradovPrimePowerFixedCollisionAmbientSet_zero p k r b hk w]

/-- Union of all fixed collision patterns at a prime-power level. -/
noncomputable def vinogradovPrimePowerFixedCollisionAmbientUnionSet
    (p k r b n : ℕ) [Fact p.Prime] :
    Finset (vinogradovPrimePowerBasePair p 0 (b * k + r) n) :=
  (Finset.univ : Finset (Fin b → VinogradovCollisionWitness k)).biUnion
    (vinogradovPrimePowerFixedCollisionAmbientSet p k r b n)

theorem mem_vinogradovPrimePowerFixedCollisionAmbientUnionSet_iff
    (p k r b n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 (b * k + r) n) :
    xy ∈ vinogradovPrimePowerFixedCollisionAmbientUnionSet p k r b n ↔
      VinogradovAllBlocksSingular p k r b
        (fun i ↦ (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p)) := by
  let x : Fin (b * k + r) → ZMod p :=
    fun i ↦ (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p)
  rw [← vinogradovMultiBlockCollisionWitnessSet_nonempty_iff p k r b x]
  constructor
  · intro hxy
    obtain ⟨w, _hw, hfixed⟩ := Finset.mem_biUnion.mp hxy
    refine ⟨w, ?_⟩
    apply (mem_vinogradovMultiBlockCollisionWitnessSet_iff
      p k r b x w).mpr
    simpa [x, vinogradovCollisionKeptIndex,
      vinogradovCollisionDeletedIndex] using
      (mem_vinogradovPrimePowerFixedCollisionAmbientSet_iff
        p k r b n w xy).mp hfixed
  · rintro ⟨w, hw⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨w, Finset.mem_univ w, ?_⟩
    apply (mem_vinogradovPrimePowerFixedCollisionAmbientSet_iff
      p k r b n w xy).mpr
    simpa [x, vinogradovCollisionKeptIndex,
      vinogradovCollisionDeletedIndex] using
      (mem_vinogradovMultiBlockCollisionWitnessSet_iff
        p k r b x w).mp hw

/-- The union of fixed collision branches is exactly the existing all-singular
prime-power ambient stratum. -/
theorem vinogradovPrimePowerFixedCollisionAmbientUnionSet_eq_singular
    (p k r b n : ℕ) [Fact p.Prime] :
    vinogradovPrimePowerFixedCollisionAmbientUnionSet p k r b n =
      vinogradovPrimePowerMultiBlockSingularAmbientSet p k r b n := by
  ext xy
  rw [mem_vinogradovPrimePowerFixedCollisionAmbientUnionSet_iff,
    mem_vinogradovPrimePowerMultiBlockSingularAmbientSet_iff]

/-- Summing the exact prime-power collision fibers gives an explicit
branchwise all-singular bound. -/
theorem card_vinogradovPrimePowerFixedCollisionAmbientUnionSet_le
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k) :
    (vinogradovPrimePowerFixedCollisionAmbientUnionSet p k r b n).card ≤
      (Fintype.card (VinogradovCollisionWitness k)) ^ b *
        ((p ^ (b * (k - 1) + r) * p ^ (b * k + r)) *
          (p ^ (2 * (b * k + r))) ^ n) := by
  calc
    (vinogradovPrimePowerFixedCollisionAmbientUnionSet
        p k r b n).card ≤
      ∑ w : Fin b → VinogradovCollisionWitness k,
        (vinogradovPrimePowerFixedCollisionAmbientSet p k r b n w).card :=
      Finset.card_biUnion_le
    _ = ∑ _w : Fin b → VinogradovCollisionWitness k,
        ((p ^ (b * (k - 1) + r) * p ^ (b * k + r)) *
          (p ^ (2 * (b * k + r))) ^ n) := by
      apply Finset.sum_congr rfl
      intro w _hw
      exact card_vinogradovPrimePowerFixedCollisionAmbientSet
        p k r b n hk w
    _ = (Fintype.card (VinogradovCollisionWitness k)) ^ b *
        ((p ^ (b * (k - 1) + r) * p ^ (b * k + r)) *
          (p ^ (2 * (b * k + r))) ^ n) := by
      simp

/-- The existing all-singular ambient stratum inherits the explicit
collision-pattern decomposition bound. -/
theorem card_vinogradovPrimePowerMultiBlockSingularAmbientSet_le_collision
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k) :
    (vinogradovPrimePowerMultiBlockSingularAmbientSet p k r b n).card ≤
      (Fintype.card (VinogradovCollisionWitness k)) ^ b *
        ((p ^ (b * (k - 1) + r) * p ^ (b * k + r)) *
          (p ^ (2 * (b * k + r))) ^ n) := by
  rw [← vinogradovPrimePowerFixedCollisionAmbientUnionSet_eq_singular]
  exact card_vinogradovPrimePowerFixedCollisionAmbientUnionSet_le
    p k r b n hk

/-- A solution at level `p^(n+2)` transported by the unrestricted digit
equivalence always reduces to a solution at level `p^(n+1)`, for an arbitrary
equation degree and tuple length. -/
theorem vinogradovPrimePowerLiftAmbientEquiv_solution_to_base_general
    (p d s n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n)
    (z : vinogradovPrimePowerSplitCorrection p 0 s)
    (h : IsVinogradovSolutionMod (p ^ (n + 2)) d s (p ^ (n + 2))
      (fun i ↦
        (vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩).1
          (Fin.natAdd 0 i))
      (fun i ↦
        (vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩).2
          (Fin.natAdd 0 i))) :
    IsVinogradovSolutionMod (p ^ (n + 1)) d s (p ^ (n + 1))
      (fun i ↦ xy.1 (Fin.natAdd 0 i))
      (fun i ↦ xy.2 (Fin.natAdd 0 i)) := by
  apply (isVinogradovSolutionMod_iff_powerSumInt_modEq
    (p ^ (n + 1)) d s (p ^ (n + 1))
    (fun i ↦ xy.1 (Fin.natAdd 0 i))
    (fun i ↦ xy.2 (Fin.natAdd 0 i))).mpr
  intro j
  have hhigh :=
    (isVinogradovSolutionMod_iff_powerSumInt_modEq
      (p ^ (n + 2)) d s (p ^ (n + 2))
      (fun i ↦
        (vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩).1
          (Fin.natAdd 0 i))
      (fun i ↦
        (vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩).2
          (Fin.natAdd 0 i))).mp h j
  have hdiv : (p : ℤ) ^ (n + 1) ∣ (p : ℤ) ^ (n + 2) := by
    refine ⟨p, ?_⟩
    rw [pow_succ]
  have hxcoord : ∀ i : Fin s,
      (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ℤ) ≡
        (((((vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩).1
          (Fin.natAdd 0 i)).val + 1 : ℕ)) : ℤ)
        [ZMOD (p : ℤ) ^ (n + 1)] := by
    intro i
    rw [vinogradovPrimePowerLiftAmbientEquiv_apply_fst_val]
    push_cast
    simpa [add_assoc, add_comm, add_left_comm] using
      (Int.modEq_add_fac_self
        (a := ((xy.1 (Fin.natAdd 0 i)).val : ℤ) + 1)
        (t := (((vinogradovSplitCorrectionEquiv p 0 s z).1
          (Fin.natAdd 0 i)).val : ℤ))
        (n := (p : ℤ) ^ (n + 1))).symm
  have hycoord : ∀ i : Fin s,
      (((xy.2 (Fin.natAdd 0 i)).val + 1 : ℕ) : ℤ) ≡
        (((((vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩).2
          (Fin.natAdd 0 i)).val + 1 : ℕ)) : ℤ)
        [ZMOD (p : ℤ) ^ (n + 1)] := by
    intro i
    rw [vinogradovPrimePowerLiftAmbientEquiv_apply_snd_val]
    push_cast
    simpa [add_assoc, add_comm, add_left_comm] using
      (Int.modEq_add_fac_self
        (a := ((xy.2 (Fin.natAdd 0 i)).val : ℤ) + 1)
        (t := (((vinogradovSplitCorrectionEquiv p 0 s z).2
          (Fin.natAdd 0 i)).val : ℤ))
        (n := (p : ℤ) ^ (n + 1))).symm
  have hxpower := vinogradovPowerSumInt_modEq
    ((p : ℤ) ^ (n + 1)) hxcoord j
  have hypower := vinogradovPowerSumInt_modEq
    ((p : ℤ) ^ (n + 1)) hycoord j
  have hhigh' :
      vinogradovPowerSumInt
          (fun i ↦ (((((vinogradovPrimePowerLiftAmbientEquiv p 0 s n
            ⟨xy, z⟩).1 (Fin.natAdd 0 i)).val + 1 : ℕ)) : ℤ)) j ≡
        vinogradovPowerSumInt
          (fun i ↦ (((((vinogradovPrimePowerLiftAmbientEquiv p 0 s n
            ⟨xy, z⟩).2 (Fin.natAdd 0 i)).val + 1 : ℕ)) : ℤ)) j
        [ZMOD (p : ℤ) ^ (n + 1)] := by
    apply (show
      vinogradovPowerSumInt
          (fun i ↦ (((((vinogradovPrimePowerLiftAmbientEquiv p 0 s n
            ⟨xy, z⟩).1 (Fin.natAdd 0 i)).val + 1 : ℕ)) : ℤ)) j ≡
        vinogradovPowerSumInt
          (fun i ↦ (((((vinogradovPrimePowerLiftAmbientEquiv p 0 s n
            ⟨xy, z⟩).2 (Fin.natAdd 0 i)).val + 1 : ℕ)) : ℤ)) j
        [ZMOD (p : ℤ) ^ (n + 2)] from by simpa using hhigh).of_dvd
    exact hdiv
  exact hxpower.trans (hhigh'.trans hypower.symm)

/-- Solutions in one fixed collision branch. -/
noncomputable def vinogradovPrimePowerFixedCollisionSolutionSet
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    Finset (vinogradovPrimePowerBasePair p 0 (b * k + r) n) :=
  (vinogradovPrimePowerFixedCollisionAmbientSet p k r b n w).filter
    fun xy ↦
      IsVinogradovSolutionMod (p ^ (n + 1)) k (b * k + r)
        (p ^ (n + 1))
        (fun i ↦ xy.1 (Fin.natAdd 0 i))
        (fun i ↦ xy.2 (Fin.natAdd 0 i))

theorem mem_vinogradovPrimePowerFixedCollisionSolutionSet_iff
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k)
    (xy : vinogradovPrimePowerBasePair p 0 (b * k + r) n) :
    xy ∈ vinogradovPrimePowerFixedCollisionSolutionSet p k r b n w ↔
      (∀ q : Fin b,
        (((xy.1 (Fin.natAdd 0
            (vinogradovCollisionKeptIndex k r b w q))).val + 1 : ℕ) :
          ZMod p) =
        (((xy.1 (Fin.natAdd 0
            (vinogradovCollisionDeletedIndex k r b w q))).val + 1 : ℕ) :
          ZMod p)) ∧
      IsVinogradovSolutionMod (p ^ (n + 1)) k (b * k + r)
        (p ^ (n + 1))
        (fun i ↦ xy.1 (Fin.natAdd 0 i))
        (fun i ↦ xy.2 (Fin.natAdd 0 i)) := by
  simp [vinogradovPrimePowerFixedCollisionSolutionSet,
    mem_vinogradovPrimePowerFixedCollisionAmbientSet_iff]

/-- Exact one-step correction space above the solutions in one fixed
collision branch.  No estimate on the correction fibers is asserted here. -/
noncomputable def vinogradovPrimePowerFixedCollisionSolutionLiftSet
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    Finset
      (Σ _ : vinogradovPrimePowerBasePair p 0 (b * k + r) n,
        vinogradovPrimePowerSplitCorrection p 0 (b * k + r)) :=
  (vinogradovPrimePowerFixedCollisionSolutionSet p k r b n w).sigma
    fun xy ↦
      (Finset.univ :
        Finset (vinogradovPrimePowerSplitCorrection p 0 (b * k + r))).filter
          fun z ↦
            IsVinogradovSolutionMod (p ^ (n + 2)) k (b * k + r)
              (p ^ (n + 2))
              (fun i ↦
                (vinogradovPrimePowerLiftAmbientEquiv p 0
                  (b * k + r) n ⟨xy, z⟩).1 (Fin.natAdd 0 i))
              (fun i ↦
                (vinogradovPrimePowerLiftAmbientEquiv p 0
                  (b * k + r) n ⟨xy, z⟩).2 (Fin.natAdd 0 i))

/-- The fixed-collision solution lift space transports exactly to the same
solution branch one prime-power level higher. -/
theorem
    mem_vinogradovPrimePowerFixedCollisionSolutionLiftSet_iff_image_mem
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k)
    (u : Σ _ : vinogradovPrimePowerBasePair p 0 (b * k + r) n,
      vinogradovPrimePowerSplitCorrection p 0 (b * k + r)) :
    u ∈ vinogradovPrimePowerFixedCollisionSolutionLiftSet p k r b n w ↔
      vinogradovPrimePowerLiftAmbientEquiv p 0 (b * k + r) n u ∈
        vinogradovPrimePowerFixedCollisionSolutionSet
          p k r b (n + 1) w := by
  rcases u with ⟨xy, z⟩
  rw [vinogradovPrimePowerFixedCollisionSolutionLiftSet,
    Finset.mem_sigma,
    mem_vinogradovPrimePowerFixedCollisionSolutionSet_iff,
    Finset.mem_filter,
    mem_vinogradovPrimePowerFixedCollisionSolutionSet_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hcollision, _hbase⟩, hhigh⟩
    refine ⟨?_, hhigh⟩
    exact
      (vinogradovPrimePowerLiftAmbientEquiv_fixedCollision_iff
        p k r b n w xy z).mpr hcollision
  · rintro ⟨hcollision, hhigh⟩
    refine ⟨⟨?_, ?_⟩, hhigh⟩
    · exact
        (vinogradovPrimePowerLiftAmbientEquiv_fixedCollision_iff
          p k r b n w xy z).mp hcollision
    · exact vinogradovPrimePowerLiftAmbientEquiv_solution_to_base_general
        p k (b * k + r) n xy z hhigh

/-- Mapping the exact correction space through the digit equivalence gives
the next fixed-collision solution branch. -/
theorem map_vinogradovPrimePowerFixedCollisionSolutionLiftSet_eq
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionSolutionLiftSet
      p k r b n w).map
        (vinogradovPrimePowerLiftAmbientEquiv p 0
          (b * k + r) n).toEmbedding =
      vinogradovPrimePowerFixedCollisionSolutionSet
        p k r b (n + 1) w := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_map.mp hv with ⟨u, hu, rfl⟩
    exact
      (mem_vinogradovPrimePowerFixedCollisionSolutionLiftSet_iff_image_mem
        p k r b n w u).mp hu
  · intro hv
    let e := vinogradovPrimePowerLiftAmbientEquiv p 0 (b * k + r) n
    let u := e.symm v
    have heu : e u = v := e.apply_symm_apply v
    apply Finset.mem_map.mpr
    refine ⟨u, ?_, heu⟩
    apply
      (mem_vinogradovPrimePowerFixedCollisionSolutionLiftSet_iff_image_mem
        p k r b n w u).mpr
    simpa [e, u] using hv

/-- Exact cardinal recurrence before estimating the correction fibers. -/
theorem card_vinogradovPrimePowerFixedCollisionSolutionSet_succ
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionSolutionSet
      p k r b (n + 1) w).card =
      (vinogradovPrimePowerFixedCollisionSolutionLiftSet
        p k r b n w).card := by
  rw [← map_vinogradovPrimePowerFixedCollisionSolutionLiftSet_eq,
    Finset.card_map]

/-- Union of all fixed collision solution branches. -/
noncomputable def vinogradovPrimePowerFixedCollisionSolutionUnionSet
    (p k r b n : ℕ) [Fact p.Prime] :
    Finset (vinogradovPrimePowerBasePair p 0 (b * k + r) n) :=
  (Finset.univ : Finset (Fin b → VinogradovCollisionWitness k)).biUnion
    (vinogradovPrimePowerFixedCollisionSolutionSet p k r b n)

theorem mem_vinogradovPrimePowerFixedCollisionSolutionUnionSet_iff
    (p k r b n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 (b * k + r) n) :
    xy ∈ vinogradovPrimePowerFixedCollisionSolutionUnionSet p k r b n ↔
      VinogradovAllBlocksSingular p k r b
          (fun i ↦ (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p)) ∧
        IsVinogradovSolutionMod (p ^ (n + 1)) k (b * k + r)
          (p ^ (n + 1))
          (fun i ↦ xy.1 (Fin.natAdd 0 i))
          (fun i ↦ xy.2 (Fin.natAdd 0 i)) := by
  let x : Fin (b * k + r) → ZMod p :=
    fun i ↦ (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p)
  constructor
  · intro hxy
    obtain ⟨w, _hw, hfixed⟩ := Finset.mem_biUnion.mp hxy
    have hparts :=
      (mem_vinogradovPrimePowerFixedCollisionSolutionSet_iff
        p k r b n w xy).mp hfixed
    refine ⟨?_, hparts.2⟩
    apply (vinogradovMultiBlockCollisionWitnessSet_nonempty_iff
      p k r b x).mp
    refine ⟨w, ?_⟩
    apply (mem_vinogradovMultiBlockCollisionWitnessSet_iff
      p k r b x w).mpr
    simpa [x, vinogradovCollisionKeptIndex,
      vinogradovCollisionDeletedIndex] using hparts.1
  · rintro ⟨hsingular, hsolution⟩
    obtain ⟨w, hw⟩ :=
      (vinogradovMultiBlockCollisionWitnessSet_nonempty_iff
        p k r b x).mpr hsingular
    apply Finset.mem_biUnion.mpr
    refine ⟨w, Finset.mem_univ w, ?_⟩
    apply (mem_vinogradovPrimePowerFixedCollisionSolutionSet_iff
      p k r b n w xy).mpr
    refine ⟨?_, hsolution⟩
    simpa [x, vinogradovCollisionKeptIndex,
      vinogradovCollisionDeletedIndex] using
      (mem_vinogradovMultiBlockCollisionWitnessSet_iff
        p k r b x w).mp hw

/-- The fixed-collision solution union is exactly the existing all-singular
prime-power solution stratum. -/
theorem vinogradovPrimePowerFixedCollisionSolutionUnionSet_eq_singular
    (p k r b n : ℕ) [Fact p.Prime] :
    vinogradovPrimePowerFixedCollisionSolutionUnionSet p k r b n =
      vinogradovPrimePowerMultiBlockSingularSolutionSet p k r b n := by
  ext xy
  rw [mem_vinogradovPrimePowerFixedCollisionSolutionUnionSet_iff,
    mem_vinogradovPrimePowerMultiBlockSingularSolutionSet_iff]

/-- A fixed-collision solution branch is bounded by its exact ambient
collision fiber. -/
theorem card_vinogradovPrimePowerFixedCollisionSolutionSet_le
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k)
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionSolutionSet p k r b n w).card ≤
      (p ^ (b * (k - 1) + r) * p ^ (b * k + r)) *
        (p ^ (2 * (b * k + r))) ^ n := by
  calc
    (vinogradovPrimePowerFixedCollisionSolutionSet
        p k r b n w).card ≤
      (vinogradovPrimePowerFixedCollisionAmbientSet p k r b n w).card := by
        exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = (p ^ (b * (k - 1) + r) * p ^ (b * k + r)) *
        (p ^ (2 * (b * k + r))) ^ n :=
      card_vinogradovPrimePowerFixedCollisionAmbientSet p k r b n hk w

/-- The all-singular solution stratum is an explicit finite sum of fixed
collision branches. -/
theorem card_vinogradovPrimePowerMultiBlockSingularSolutionSet_le_collision
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k) :
    (vinogradovPrimePowerMultiBlockSingularSolutionSet p k r b n).card ≤
      (Fintype.card (VinogradovCollisionWitness k)) ^ b *
        ((p ^ (b * (k - 1) + r) * p ^ (b * k + r)) *
          (p ^ (2 * (b * k + r))) ^ n) := by
  rw [← vinogradovPrimePowerFixedCollisionSolutionUnionSet_eq_singular]
  calc
    (vinogradovPrimePowerFixedCollisionSolutionUnionSet
        p k r b n).card ≤
      ∑ w : Fin b → VinogradovCollisionWitness k,
        (vinogradovPrimePowerFixedCollisionSolutionSet
          p k r b n w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w : Fin b → VinogradovCollisionWitness k,
        ((p ^ (b * (k - 1) + r) * p ^ (b * k + r)) *
          (p ^ (2 * (b * k + r))) ^ n) := by
      apply Finset.sum_le_sum
      intro w _hw
      exact card_vinogradovPrimePowerFixedCollisionSolutionSet_le
        p k r b n hk w
    _ = (Fintype.card (VinogradovCollisionWitness k)) ^ b *
        ((p ^ (b * (k - 1) + r) * p ^ (b * k + r)) *
          (p ^ (2 * (b * k + r))) ^ n) := by
      simp

end

end ZeroFreeRegion.VinogradovKorobov
