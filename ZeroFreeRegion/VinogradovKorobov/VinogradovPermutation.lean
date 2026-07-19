import ZeroFreeRegion.VinogradovKorobov.VinogradovMultiBlock

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Reindexing the coordinates by a permutation preserves every integer power
sum. -/
theorem vinogradovPowerSumInt_comp_perm {k s : ℕ}
    (e : Equiv.Perm (Fin s)) (x : Fin s → ℤ) (j : Fin k) :
    vinogradovPowerSumInt (fun i ↦ x (e i)) j =
      vinogradovPowerSumInt x j := by
  unfold vinogradovPowerSumInt
  exact _root_.Equiv.sum_comp e (fun i ↦ x i ^ (j.val + 1))

/-- Simultaneously permuting both tuples preserves the integer Vinogradov
system. -/
theorem IsVinogradovSolutionInt.comp_perm {k s : ℕ}
    {x y : Fin s → ℤ} (h : IsVinogradovSolutionInt k s x y)
    (e : Equiv.Perm (Fin s)) :
    IsVinogradovSolutionInt k s (fun i ↦ x (e i)) (fun i ↦ y (e i)) := by
  intro j
  rw [vinogradovPowerSumInt_comp_perm,
    vinogradovPowerSumInt_comp_perm, h j]

theorem isVinogradovSolutionInt_comp_perm_iff {k s : ℕ}
    (e : Equiv.Perm (Fin s)) (x y : Fin s → ℤ) :
    IsVinogradovSolutionInt k s (fun i ↦ x (e i)) (fun i ↦ y (e i)) ↔
      IsVinogradovSolutionInt k s x y := by
  constructor
  · intro h
    simpa using h.comp_perm e.symm
  · intro h
    exact h.comp_perm e

/-- Reindexing residue coordinates by a permutation preserves every residue
power sum. -/
theorem vinogradovResiduePowerSum_comp_perm {p d s : ℕ}
    (e : Equiv.Perm (Fin s)) (x : Fin s → ZMod p) (j : Fin d) :
    vinogradovResiduePowerSum p (fun i ↦ x (e i)) j =
      vinogradovResiduePowerSum p x j := by
  unfold vinogradovResiduePowerSum
  exact _root_.Equiv.sum_comp e (fun i ↦ x i ^ (j.val + 1))

/-- Simultaneously permuting both residue tuples preserves the residue-field
Vinogradov system. -/
theorem IsVinogradovResidueSolution.comp_perm {p d s : ℕ}
    {x y : Fin s → ZMod p} (h : IsVinogradovResidueSolution p d s x y)
    (e : Equiv.Perm (Fin s)) :
    IsVinogradovResidueSolution p d s
      (fun i ↦ x (e i)) (fun i ↦ y (e i)) := by
  intro j
  rw [vinogradovResiduePowerSum_comp_perm,
    vinogradovResiduePowerSum_comp_perm, h j]

theorem isVinogradovResidueSolution_comp_perm_iff {p d s : ℕ}
    (e : Equiv.Perm (Fin s)) (x y : Fin s → ZMod p) :
    IsVinogradovResidueSolution p d s
        (fun i ↦ x (e i)) (fun i ↦ y (e i)) ↔
      IsVinogradovResidueSolution p d s x y := by
  constructor
  · intro h
    simpa using h.comp_perm e.symm
  · intro h
    exact h.comp_perm e

/-- The bounded modular power sums are also invariant under coordinate
permutation. -/
theorem vinogradovPowerSumMod_comp_perm {Q k s X : ℕ}
    (e : Equiv.Perm (Fin s)) (x : Fin s → Fin X) (j : Fin k) :
    vinogradovPowerSumMod Q (fun i ↦ x (e i)) j =
      vinogradovPowerSumMod Q x j := by
  unfold vinogradovPowerSumMod
  exact _root_.Equiv.sum_comp e
    (fun i ↦ ((x i).val + 1 : ZMod Q) ^ (j.val + 1))

theorem IsVinogradovSolutionMod.comp_perm {Q k s X : ℕ}
    {x y : Fin s → Fin X} (h : IsVinogradovSolutionMod Q k s X x y)
    (e : Equiv.Perm (Fin s)) :
    IsVinogradovSolutionMod Q k s X
      (fun i ↦ x (e i)) (fun i ↦ y (e i)) := by
  intro j
  rw [vinogradovPowerSumMod_comp_perm,
    vinogradovPowerSumMod_comp_perm, h j]

theorem isVinogradovSolutionMod_comp_perm_iff {Q k s X : ℕ}
    (e : Equiv.Perm (Fin s)) (x y : Fin s → Fin X) :
    IsVinogradovSolutionMod Q k s X
        (fun i ↦ x (e i)) (fun i ↦ y (e i)) ↔
      IsVinogradovSolutionMod Q k s X x y := by
  constructor
  · intro h
    simpa using h.comp_perm e.symm
  · intro h
    exact h.comp_perm e

end

end ZeroFreeRegion.VinogradovKorobov
