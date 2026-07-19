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

end

end ZeroFreeRegion.VinogradovKorobov
