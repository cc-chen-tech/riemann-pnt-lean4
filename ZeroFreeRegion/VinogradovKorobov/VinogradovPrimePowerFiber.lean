import ZeroFreeRegion.VinogradovKorobov.VinogradovHensel

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Coordinatewise congruent integer tuples have congruent power sums. -/
theorem vinogradovPowerSumInt_modEq
    {k s : ℕ} (m : ℤ) {x y : Fin s → ℤ}
    (hxy : ∀ i : Fin s, x i ≡ y i [ZMOD m]) (j : Fin k) :
    vinogradovPowerSumInt x j ≡ vinogradovPowerSumInt y j [ZMOD m] := by
  unfold vinogradovPowerSumInt
  apply Int.ModEq.sum
  intro i _
  exact (hxy i).pow (j.val + 1)

/-- The finite set of residue correction vectors that realize a prescribed
first-order power-sum change at prime-power level `p^(n+2)`. -/
noncomputable def vinogradovPrimePowerCorrectionSet
    (p k n : ℕ) [Fact p.Prime] (x b : Fin k → ℤ) :
    Finset (Fin k → ZMod p) := by
  classical
  exact Finset.univ.filter fun u : Fin k → ZMod p ↦
    ∀ j : Fin k,
      vinogradovPowerSumInt
          (fun i ↦ x i + (p : ℤ) ^ (n + 1) * (u i).val) j ≡
        vinogradovPowerSumInt x j + (p : ℤ) ^ (n + 1) * b j
          [ZMOD (p : ℤ) ^ (n + 2)]

/-- At a nonsingular residue vector, every prime-power correction fiber has
exactly one residue class. -/
theorem card_vinogradovPrimePowerCorrectionSet_eq_one
    (p k n : ℕ) [Fact p.Prime] (hkp : k < p) (x b : Fin k → ℤ)
    (hx : Function.Injective (fun i : Fin k ↦ (x i : ZMod p))) :
    (vinogradovPrimePowerCorrectionSet p k n x b).card = 1 := by
  classical
  obtain ⟨h, hh, hunique⟩ :=
    exists_unique_mod_vinogradovPowerSumInt_affine_lift_mod_prime_pow_succ
      p k n hkp x b hx
  let u : Fin k → ZMod p := fun i ↦ (h i : ZMod p)
  have hhu : ∀ i : Fin k, h i ≡ ((u i).val : ℤ) [ZMOD (p : ℤ)] := by
    intro i
    apply (ZMod.intCast_eq_intCast_iff (h i) ((u i).val : ℤ) p).mp
    simp [u]
  have hcoord : ∀ i : Fin k,
      x i + (p : ℤ) ^ (n + 1) * h i ≡
        x i + (p : ℤ) ^ (n + 1) * (u i).val
          [ZMOD (p : ℤ) ^ (n + 2)] := by
    intro i
    simpa [pow_succ] using
      ((hhu i).mul_left'.add_left (x i))
  have huPower : ∀ j : Fin k,
      vinogradovPowerSumInt
          (fun i ↦ x i + (p : ℤ) ^ (n + 1) * (u i).val) j ≡
        vinogradovPowerSumInt x j + (p : ℤ) ^ (n + 1) * b j
          [ZMOD (p : ℤ) ^ (n + 2)] := by
    intro j
    exact (vinogradovPowerSumInt_modEq
      ((p : ℤ) ^ (n + 2)) hcoord j).symm.trans (hh j)
  have hu : u ∈ vinogradovPrimePowerCorrectionSet p k n x b := by
    simpa [vinogradovPrimePowerCorrectionSet] using huPower
  have hset : vinogradovPrimePowerCorrectionSet p k n x b = {u} := by
    ext v
    simp only [Finset.mem_singleton]
    constructor
    · intro hv
      have hvPower : ∀ j : Fin k,
          vinogradovPowerSumInt
              (fun i ↦ x i + (p : ℤ) ^ (n + 1) * (v i).val) j ≡
            vinogradovPowerSumInt x j + (p : ℤ) ^ (n + 1) * b j
              [ZMOD (p : ℤ) ^ (n + 2)] := by
        simpa [vinogradovPrimePowerCorrectionSet] using hv
      apply funext
      intro i
      have hi := hunique (fun i : Fin k ↦ ((v i).val : ℤ)) hvPower i
      have hiz :=
        (ZMod.intCast_eq_intCast_iff ((v i).val : ℤ) (h i) p).mpr hi
      simpa [u] using hiz
    · intro hv
      simpa [hv] using hu
  rw [hset, Finset.card_singleton]

end

end ZeroFreeRegion.VinogradovKorobov
