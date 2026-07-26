import ZeroFreeRegion.VinogradovKorobov.VinogradovSymmetry
import Mathlib.Algebra.BigOperators.ModEq

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

open scoped BigOperators

/-- The unrestricted integer Vinogradov system reduced modulo one common
integer modulus. -/
def IsVinogradovSolutionIntMod (M k s : ℕ)
    (x y : Fin s → ℤ) : Prop :=
  ∀ j : Fin k, Int.ModEq (M : ℤ)
    (vinogradovPowerSumInt x j) (vinogradovPowerSumInt y j)

/-- A modular Vinogradov system controls every power sum whose degree is at
most the number of equations, including the automatic degree-zero row. -/
theorem IsVinogradovSolutionIntMod.powerSum_modEq
    {M k s : ℕ} {x y : Fin s → ℤ}
    (h : IsVinogradovSolutionIntMod M k s x y)
    {m : ℕ} (hm : m ≤ k) :
    Int.ModEq (M : ℤ) (∑ i, x i ^ m) (∑ i, y i ^ m) := by
  by_cases hm0 : m = 0
  · subst m
    simp
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hlt : m - 1 < k := by omega
    have hp := h (⟨m - 1, hlt⟩ : Fin k)
    change Int.ModEq (M : ℤ)
      (∑ i, x i ^ (m - 1 + 1)) (∑ i, y i ^ (m - 1 + 1)) at hp
    simpa only [Nat.sub_add_cancel hmpos] using hp

/-- Translating every coordinate by the same integer preserves the modular
Vinogradov system. -/
theorem IsVinogradovSolutionIntMod.translate
    {M k s : ℕ} {x y : Fin s → ℤ}
    (h : IsVinogradovSolutionIntMod M k s x y) (c : ℤ) :
    IsVinogradovSolutionIntMod M k s
      (fun i ↦ x i + c) (fun i ↦ y i + c) := by
  intro j
  unfold vinogradovPowerSumInt
  simp_rw [add_pow]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Int.ModEq.sum
  intro m hm
  simp only [Finset.mem_range] at hm
  have hmk : m ≤ k := by omega
  have hpower := h.powerSum_modEq hmk
  have hscaled := hpower.mul_right
    (c ^ (j.val + 1 - m) * (j.val + 1).choose m)
  simpa only [Finset.sum_mul, mul_assoc] using hscaled

/-- Translation is an equivalence for the common-modulus integer Vinogradov
system. -/
theorem isVinogradovSolutionIntMod_translate_iff
    (M k s : ℕ) (x y : Fin s → ℤ) (c : ℤ) :
    IsVinogradovSolutionIntMod M k s
        (fun i ↦ x i + c) (fun i ↦ y i + c) ↔
      IsVinogradovSolutionIntMod M k s x y := by
  constructor
  · intro h
    have hback := h.translate (-c)
    simpa only [add_neg_cancel_right] using hback
  · exact fun h ↦ h.translate c

end

end ZeroFreeRegion.VinogradovKorobov
