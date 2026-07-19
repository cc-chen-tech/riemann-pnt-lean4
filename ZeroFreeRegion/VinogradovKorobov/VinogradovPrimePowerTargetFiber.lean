import ZeroFreeRegion.VinogradovKorobov.VinogradovFiniteFieldNewton
import ZeroFreeRegion.VinogradovKorobov.VinogradovSolutionLifting

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance vinogradovPrimePowerTargetFiberPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-- Nonsingular tuples modulo `p^(n+1)` whose first `k` power sums equal a
fixed integer target modulo the same prime power. -/
noncomputable def vinogradovPrimePowerTargetFiberSet
    (p k n : ℕ) [Fact p.Prime] (target : Fin k → ℤ) :
    Finset (Fin k → Fin (p ^ (n + 1))) :=
  Finset.univ.filter fun x ↦
    Function.Injective (fun i : Fin k ↦
      (((x i).val + 1 : ℕ) : ZMod p)) ∧
    ∀ j : Fin k,
      vinogradovPowerSumInt
          (fun i ↦ (((x i).val + 1 : ℕ) : ℤ)) j ≡
        target j [ZMOD (p : ℤ) ^ (n + 1)]

theorem mem_vinogradovPrimePowerTargetFiberSet_iff
    (p k n : ℕ) [Fact p.Prime] (target : Fin k → ℤ)
    (x : Fin k → Fin (p ^ (n + 1))) :
    x ∈ vinogradovPrimePowerTargetFiberSet p k n target ↔
      Function.Injective (fun i : Fin k ↦
        (((x i).val + 1 : ℕ) : ZMod p)) ∧
      ∀ j : Fin k,
        vinogradovPowerSumInt
            (fun i ↦ (((x i).val + 1 : ℕ) : ℤ)) j ≡
          target j [ZMOD (p : ℤ) ^ (n + 1)] := by
  simp [vinogradovPrimePowerTargetFiberSet]

/-- The one-based equivalence between a complete residue interval and
`ZMod p`. -/
noncomputable def vinogradovPrimeTargetCompleteResidueEquiv
    (p : ℕ) [NeZero p] : Fin p ≃ ZMod p :=
  (ZMod.finEquiv p).toEquiv.trans (Equiv.addRight 1)

theorem vinogradovPrimeTargetCompleteResidueEquiv_apply
    (p : ℕ) [NeZero p] (x : Fin p) :
    vinogradovPrimeTargetCompleteResidueEquiv p x =
      (x.val : ZMod p) + 1 := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p =>
      change (x + (1 : Fin (p + 1)) : Fin (p + 1)) =
        (⟨x.val % (p + 1), Nat.mod_lt _ (Nat.succ_pos p)⟩ :
          Fin (p + 1)) + 1
      congr 1
      apply Fin.ext
      simp [Nat.mod_eq_of_lt x.isLt]

/-- Coordinatewise transport from the first prime-power level to the
residue field, using the same one-based representatives as the Vinogradov
system. -/
noncomputable def vinogradovPrimeTargetCompleteResidueTupleEquiv
    (p k : ℕ) [NeZero p] :
    (Fin k → Fin (p ^ (0 + 1))) ≃ (Fin k → ZMod p) :=
  Equiv.piCongrRight fun _ ↦
    (finCongr (by simp)).trans
      (vinogradovPrimeTargetCompleteResidueEquiv p)

private theorem vinogradovPrimeTargetCompleteResidueTupleEquiv_apply
    (p k : ℕ) [NeZero p] (x : Fin k → Fin (p ^ (0 + 1))) :
    vinogradovPrimeTargetCompleteResidueTupleEquiv p k x =
      fun i ↦ (((x i).val + 1 : ℕ) : ZMod p) := by
  funext i
  change vinogradovPrimeTargetCompleteResidueEquiv p
    (Fin.cast (by simp) (x i)) = _
  simpa only [Nat.cast_add, Nat.cast_one] using
    vinogradovPrimeTargetCompleteResidueEquiv_apply p
      (Fin.cast (by simp) (x i))

/-- At the first prime level, every nonsingular fixed-target fiber has at
most `k!` ordered tuples. -/
theorem card_vinogradovPrimePowerTargetFiberSet_zero_le_factorial
    (p k : ℕ) [Fact p.Prime] (hkp : k < p)
    (target : Fin k → ℤ) :
    (vinogradovPrimePowerTargetFiberSet p k 0 target).card ≤
      k.factorial := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let e := vinogradovPrimeTargetCompleteResidueTupleEquiv p k
  calc
    (vinogradovPrimePowerTargetFiberSet p k 0 target).card =
        ((vinogradovPrimePowerTargetFiberSet p k 0 target).map
          e.toEmbedding).card := by
      rw [Finset.card_map]
    _ ≤ (vinogradovResidueTargetFiberSet p k
          (fun j ↦ (target j : ZMod p))).card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
      apply (mem_vinogradovResidueTargetFiberSet_iff p k
        (fun j ↦ (target j : ZMod p)) (e x)).mpr
      intro j
      have htarget :=
        (mem_vinogradovPrimePowerTargetFiberSet_iff
          p k 0 target x).mp hx |>.2 j
      have hcast := (ZMod.intCast_eq_intCast_iff
        (vinogradovPowerSumInt
          (fun i ↦ (((x i).val + 1 : ℕ) : ℤ)) j)
        (target j) p).mpr (by simpa using htarget)
      simpa [vinogradovResiduePowerSum, vinogradovPowerSumInt, e,
        vinogradovPrimeTargetCompleteResidueTupleEquiv_apply] using hcast
    _ ≤ k.factorial :=
      card_vinogradovResidueTargetFiberSet_le_factorial p k hkp
        (fun j ↦ (target j : ZMod p))

/-- A base fixed-target tuple together with its one-step correction digit. -/
noncomputable def vinogradovPrimePowerTargetFiberLiftSet
    (p k n : ℕ) [Fact p.Prime] (target : Fin k → ℤ) :
    Finset (Σ _ : Fin k → Fin (p ^ (n + 1)), Fin k → ZMod p) :=
  (vinogradovPrimePowerTargetFiberSet p k n target).sigma fun x ↦
    vinogradovHeadCorrectionSet p k n
      (fun i ↦ (((x i).val + 1 : ℕ) : ℤ)) target

/-- Nonsingularity makes every one-step correction fiber have cardinality at
most one. -/
theorem card_vinogradovPrimePowerTargetFiberLiftSet_le
    (p k n : ℕ) [Fact p.Prime] (hkp : k < p)
    (target : Fin k → ℤ) :
    (vinogradovPrimePowerTargetFiberLiftSet p k n target).card ≤
      (vinogradovPrimePowerTargetFiberSet p k n target).card := by
  rw [vinogradovPrimePowerTargetFiberLiftSet, Finset.card_sigma]
  calc
    (∑ x ∈ vinogradovPrimePowerTargetFiberSet p k n target,
        (vinogradovHeadCorrectionSet p k n
          (fun i ↦ (((x i).val + 1 : ℕ) : ℤ)) target).card) ≤
        ∑ _x ∈ vinogradovPrimePowerTargetFiberSet p k n target, 1 := by
      apply Finset.sum_le_sum
      intro x hx
      have hinjective :=
        (mem_vinogradovPrimePowerTargetFiberSet_iff
          p k n target x).mp hx |>.1
      have hcast : Function.Injective (fun i : Fin k ↦
          ((((x i).val + 1 : ℕ) : ℤ) : ZMod p)) := by
        intro i j hij
        apply hinjective
        simpa using hij
      exact card_vinogradovHeadCorrectionSet_le_one p k n hkp
        (fun i ↦ (((x i).val + 1 : ℕ) : ℤ)) target hcast
    _ = (vinogradovPrimePowerTargetFiberSet p k n target).card := by
      simp

/-- The ambient digit decomposition for a fixed-target tuple lift. -/
noncomputable def vinogradovPrimePowerTargetFiberLiftAmbientEquiv
    (p k n : ℕ) [Fact p.Prime] :
    (Σ _ : Fin k → Fin (p ^ (n + 1)), Fin k → ZMod p) ≃
      (Fin k → Fin (p ^ (n + 2))) :=
  (Equiv.sigmaEquivProd
      (Fin k → Fin (p ^ (n + 1))) (Fin k → ZMod p)).trans
    (vinogradovPrimePowerTupleDigitEquiv p k n)

theorem vinogradovPrimePowerTargetFiberLiftAmbientEquiv_apply_val
    (p k n : ℕ) [Fact p.Prime]
    (x : Fin k → Fin (p ^ (n + 1))) (u : Fin k → ZMod p)
    (i : Fin k) :
    (vinogradovPrimePowerTargetFiberLiftAmbientEquiv p k n ⟨x, u⟩ i).val =
      (x i).val + p ^ (n + 1) * (u i).val :=
  vinogradovPrimePowerTupleDigitEquiv_apply_val p k n x u i

private theorem vinogradovPrimePowerTargetFiberLiftAmbientEquiv_mod
    (p k n : ℕ) [Fact p.Prime]
    (x : Fin k → Fin (p ^ (n + 1))) (u : Fin k → ZMod p)
    (i : Fin k) :
    (((vinogradovPrimePowerTargetFiberLiftAmbientEquiv p k n
        ⟨x, u⟩ i).val + 1 : ℕ) : ZMod p) =
      (((x i).val + 1 : ℕ) : ZMod p) := by
  rw [vinogradovPrimePowerTargetFiberLiftAmbientEquiv_apply_val]
  push_cast
  simp [pow_succ]

private theorem
    vinogradovPrimePowerTargetFiberLiftAmbientEquiv_injective_iff
    (p k n : ℕ) [Fact p.Prime]
    (x : Fin k → Fin (p ^ (n + 1))) (u : Fin k → ZMod p) :
    Function.Injective (fun i : Fin k ↦
        (((vinogradovPrimePowerTargetFiberLiftAmbientEquiv p k n
          ⟨x, u⟩ i).val + 1 : ℕ) : ZMod p)) ↔
      Function.Injective (fun i : Fin k ↦
        (((x i).val + 1 : ℕ) : ZMod p)) := by
  constructor
  · intro h i j hij
    apply h
    simpa only [vinogradovPrimePowerTargetFiberLiftAmbientEquiv_mod] using hij
  · intro h i j hij
    apply h
    simpa only [vinogradovPrimePowerTargetFiberLiftAmbientEquiv_mod] using hij

private theorem mem_vinogradovHeadCorrectionSet_iff_lifted_target
    (p k n : ℕ) [Fact p.Prime] (target : Fin k → ℤ)
    (x : Fin k → Fin (p ^ (n + 1))) (u : Fin k → ZMod p) :
    u ∈ vinogradovHeadCorrectionSet p k n
        (fun i ↦ (((x i).val + 1 : ℕ) : ℤ)) target ↔
      ∀ j : Fin k,
        vinogradovPowerSumInt
            (fun i ↦ (((vinogradovPrimePowerTargetFiberLiftAmbientEquiv
              p k n ⟨x, u⟩ i).val + 1 : ℕ) : ℤ)) j ≡
          target j [ZMOD (p : ℤ) ^ (n + 2)] := by
  rw [mem_vinogradovHeadCorrectionSet_iff]
  have hmod : (p : ℤ) ^ (n + 1) * p = (p : ℤ) ^ (n + 2) := by
    calc
      (p : ℤ) ^ (n + 1) * p = (p : ℤ) ^ ((n + 1) + 1) :=
        (pow_succ (p : ℤ) (n + 1)).symm
      _ = (p : ℤ) ^ (n + 2) := by
        congr 1
  have htuple :
      (fun i ↦ (((vinogradovPrimePowerTargetFiberLiftAmbientEquiv
          p k n ⟨x, u⟩ i).val + 1 : ℕ) : ℤ)) =
        fun i ↦ (((x i).val + 1 : ℕ) : ℤ) +
          (p : ℤ) ^ (n + 1) * (u i).val := by
    funext i
    rw [vinogradovPrimePowerTargetFiberLiftAmbientEquiv_apply_val]
    push_cast
    ring
  rw [htuple, hmod]

private theorem vinogradovPrimePowerTargetFiber_lift_to_base
    (p k n : ℕ) [Fact p.Prime] (target : Fin k → ℤ)
    (x : Fin k → Fin (p ^ (n + 1))) (u : Fin k → ZMod p)
    (hhigh : ∀ j : Fin k,
      vinogradovPowerSumInt
          (fun i ↦ (((vinogradovPrimePowerTargetFiberLiftAmbientEquiv
            p k n ⟨x, u⟩ i).val + 1 : ℕ) : ℤ)) j ≡
        target j [ZMOD (p : ℤ) ^ (n + 2)]) :
    ∀ j : Fin k,
      vinogradovPowerSumInt
          (fun i ↦ (((x i).val + 1 : ℕ) : ℤ)) j ≡
        target j [ZMOD (p : ℤ) ^ (n + 1)] := by
  intro j
  have hdiv : (p : ℤ) ^ (n + 1) ∣ (p : ℤ) ^ (n + 2) := by
    refine ⟨p, ?_⟩
    rw [pow_succ]
  have hcoord : ∀ i : Fin k,
      (((x i).val + 1 : ℕ) : ℤ) ≡
        (((vinogradovPrimePowerTargetFiberLiftAmbientEquiv p k n
          ⟨x, u⟩ i).val + 1 : ℕ) : ℤ)
        [ZMOD (p : ℤ) ^ (n + 1)] := by
    intro i
    rw [vinogradovPrimePowerTargetFiberLiftAmbientEquiv_apply_val]
    push_cast
    simpa [add_assoc, add_comm, add_left_comm] using
      (Int.modEq_add_fac_self
        (a := ((x i).val : ℤ) + 1)
        (t := ((u i).val : ℤ))
        (n := (p : ℤ) ^ (n + 1))).symm
  exact (vinogradovPowerSumInt_modEq
    ((p : ℤ) ^ (n + 1)) hcoord j).trans ((hhigh j).of_dvd hdiv)

/-- Membership in the sigma lift is exactly membership of its ambient image
in the next fixed-target fiber. -/
theorem mem_vinogradovPrimePowerTargetFiberLiftSet_iff_image_mem
    (p k n : ℕ) [Fact p.Prime] (target : Fin k → ℤ)
    (w : Σ _ : Fin k → Fin (p ^ (n + 1)), Fin k → ZMod p) :
    w ∈ vinogradovPrimePowerTargetFiberLiftSet p k n target ↔
      vinogradovPrimePowerTargetFiberLiftAmbientEquiv p k n w ∈
        vinogradovPrimePowerTargetFiberSet p k (n + 1) target := by
  rcases w with ⟨x, u⟩
  rw [vinogradovPrimePowerTargetFiberLiftSet, Finset.mem_sigma,
    mem_vinogradovPrimePowerTargetFiberSet_iff,
    mem_vinogradovPrimePowerTargetFiberSet_iff]
  constructor
  · rintro ⟨⟨hinjective, _hbase⟩, hcorrection⟩
    exact ⟨
      (vinogradovPrimePowerTargetFiberLiftAmbientEquiv_injective_iff
        p k n x u).mpr hinjective,
      (mem_vinogradovHeadCorrectionSet_iff_lifted_target
        p k n target x u).mp hcorrection⟩
  · rintro ⟨hhighInjective, hhighTarget⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact
        (vinogradovPrimePowerTargetFiberLiftAmbientEquiv_injective_iff
          p k n x u).mp hhighInjective
    · exact vinogradovPrimePowerTargetFiber_lift_to_base
        p k n target x u hhighTarget
    · exact
        (mem_vinogradovHeadCorrectionSet_iff_lifted_target
          p k n target x u).mpr hhighTarget

/-- The ambient digit equivalence maps the complete one-step lift set onto
the next fixed-target fiber. -/
theorem map_vinogradovPrimePowerTargetFiberLiftSet_eq
    (p k n : ℕ) [Fact p.Prime] (target : Fin k → ℤ) :
    (vinogradovPrimePowerTargetFiberLiftSet p k n target).map
        (vinogradovPrimePowerTargetFiberLiftAmbientEquiv p k n).toEmbedding =
      vinogradovPrimePowerTargetFiberSet p k (n + 1) target := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_map.mp hz with ⟨w, hw, rfl⟩
    exact (mem_vinogradovPrimePowerTargetFiberLiftSet_iff_image_mem
      p k n target w).mp hw
  · intro hz
    let e := vinogradovPrimePowerTargetFiberLiftAmbientEquiv p k n
    let w := e.symm z
    have hew : e w = z := e.apply_symm_apply z
    apply Finset.mem_map.mpr
    refine ⟨w, ?_, hew⟩
    apply (mem_vinogradovPrimePowerTargetFiberLiftSet_iff_image_mem
      p k n target w).mpr
    simpa [e, w] using hz

/-- Nonsingular fixed-target fibers do not grow under one prime-power lift. -/
theorem card_vinogradovPrimePowerTargetFiberSet_succ_le
    (p k n : ℕ) [Fact p.Prime] (hkp : k < p)
    (target : Fin k → ℤ) :
    (vinogradovPrimePowerTargetFiberSet p k (n + 1) target).card ≤
      (vinogradovPrimePowerTargetFiberSet p k n target).card := by
  rw [← map_vinogradovPrimePowerTargetFiberLiftSet_eq p k n target,
    Finset.card_map]
  exact card_vinogradovPrimePowerTargetFiberLiftSet_le p k n hkp target

/-- Uniformly over every prime-power level, a nonsingular prescribed vector
of the first `k` power sums has at most `k!` ordered preimages. -/
theorem card_vinogradovPrimePowerTargetFiberSet_le_factorial
    (p k n : ℕ) [Fact p.Prime] (hkp : k < p)
    (target : Fin k → ℤ) :
    (vinogradovPrimePowerTargetFiberSet p k n target).card ≤
      k.factorial := by
  induction n with
  | zero =>
      exact card_vinogradovPrimePowerTargetFiberSet_zero_le_factorial
        p k hkp target
  | succ n ih =>
      exact (card_vinogradovPrimePowerTargetFiberSet_succ_le
        p k n hkp target).trans ih

end

end ZeroFreeRegion.VinogradovKorobov
