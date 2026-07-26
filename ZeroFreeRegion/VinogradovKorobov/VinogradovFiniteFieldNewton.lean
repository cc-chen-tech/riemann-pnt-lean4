import ZeroFreeRegion.VinogradovKorobov.VinogradovPrimePowerFiber
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Data.List.Permutation

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

open scoped BigOperators

local instance vinogradovFiniteFieldNewtonPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

private def zmodSequencePowerSum {p s : ℕ}
    (x : Fin s → ZMod p) (n : ℕ) : ZMod p :=
  ∑ i, x i ^ n

private def zmodSequenceEsymm {p s : ℕ}
    (x : Fin s → ZMod p) (n : ℕ) : ZMod p :=
  (Finset.univ.val.map x).esymm n

private theorem zmodSequenceEsymm_newton {p s : ℕ}
    (x : Fin s → ZMod p) (n : ℕ) :
    (n : ZMod p) * zmodSequenceEsymm x n =
      (-1 : ZMod p) ^ (n + 1) *
        ∑ a ∈ Finset.antidiagonal n with a.1 < n,
          (-1 : ZMod p) ^ a.1 * zmodSequenceEsymm x a.1 *
            zmodSequencePowerSum x a.2 := by
  have h := congrArg (MvPolynomial.aeval x)
    (MvPolynomial.mul_esymm_eq_sum (Fin s) (ZMod p) n)
  simpa only [map_mul, map_pow, map_sum, map_natCast, map_neg, map_one,
    MvPolynomial.aeval_esymm_eq_multiset_esymm,
    MvPolynomial.psum, MvPolynomial.aeval_X,
    zmodSequenceEsymm, zmodSequencePowerSum] using h

/-- Over `ZMod p`, when the tuple length is smaller than the prime, its first
`s` power sums determine its underlying multiset. -/
theorem multiset_eq_of_powerSums_eq_zmod
    (p s : ℕ) [Fact p.Prime] (x y : Fin s → ZMod p) (hsp : s < p)
    (hpower : ∀ n, 1 ≤ n → n ≤ s →
      (∑ i, x i ^ n) = ∑ i, y i ^ n) :
    Finset.univ.val.map x = Finset.univ.val.map y := by
  have hesymm : ∀ n, n ≤ s →
      zmodSequenceEsymm x n = zmodSequenceEsymm y n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn
        by_cases hn0 : n = 0
        · subst n
          simp [zmodSequenceEsymm, Multiset.esymm]
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
          have hnltp : n < p := hn.trans_lt hsp
          have hncast : (n : ZMod p) ≠ 0 := by
            intro hzero
            exact (Nat.not_dvd_of_pos_of_lt hnpos hnltp)
              ((ZMod.natCast_eq_zero_iff n p).mp hzero)
          have hnewtonX := zmodSequenceEsymm_newton x n
          have hnewtonY := zmodSequenceEsymm_newton y n
          have hsums :
              (∑ a ∈ Finset.antidiagonal n with a.1 < n,
                (-1 : ZMod p) ^ a.1 * zmodSequenceEsymm x a.1 *
                  zmodSequencePowerSum x a.2) =
              ∑ a ∈ Finset.antidiagonal n with a.1 < n,
                (-1 : ZMod p) ^ a.1 * zmodSequenceEsymm y a.1 *
                  zmodSequencePowerSum y a.2 := by
            apply Finset.sum_congr rfl
            intro a ha
            simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha
            have ha2pos : 0 < a.2 := by omega
            have ha2le : a.2 ≤ s := by omega
            rw [ih a.1 ha.2 (by omega)]
            rw [show zmodSequencePowerSum x a.2 =
                zmodSequencePowerSum y a.2 by
              simpa only [zmodSequencePowerSum] using
                hpower a.2 ha2pos ha2le]
          rw [hsums] at hnewtonX
          exact mul_left_cancel₀ hncast (hnewtonX.trans hnewtonY.symm)
  let px : Polynomial (ZMod p) :=
    (Finset.univ.val.map x |>.map fun r ↦
      Polynomial.X - Polynomial.C r).prod
  let py : Polynomial (ZMod p) :=
    (Finset.univ.val.map y |>.map fun r ↦
      Polynomial.X - Polynomial.C r).prod
  have hpoly : px = py := by
    dsimp [px, py]
    rw [Multiset.prod_X_sub_X_eq_sum_esymm,
      Multiset.prod_X_sub_X_eq_sum_esymm]
    simp only [Multiset.card_map, ← Finset.card_def, Finset.card_univ,
      Fintype.card_fin]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have he := hesymm j (Nat.le_of_lt_succ hj)
    change (Finset.univ.val.map x).esymm j =
      (Finset.univ.val.map y).esymm j at he
    rw [he]
  have hroots := congrArg Polynomial.roots hpoly
  have hxroots : Polynomial.roots px = Finset.univ.val.map x := by
    dsimp [px]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  have hyroots : Polynomial.roots py = Finset.univ.val.map y := by
    dsimp [py]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  exact hxroots.symm.trans (hroots.trans hyroots)

/-- A residue-field Vinogradov solution containing the first `s` equations
has the same coordinate multiset on both sides when `s < p`. -/
theorem IsVinogradovResidueSolution.multiset_eq
    (p k s : ℕ) [Fact p.Prime] (hsk : s ≤ k) (hsp : s < p)
    {x y : Fin s → ZMod p}
    (h : IsVinogradovResidueSolution p k s x y) :
    Finset.univ.val.map x = Finset.univ.val.map y := by
  apply multiset_eq_of_powerSums_eq_zmod p s x y hsp
  intro n hn hns
  have hnk : n ≤ k := hns.trans hsk
  obtain ⟨j, hj⟩ : ∃ j : Fin k, j.val + 1 = n := by
    have hlt : n - 1 < k := by omega
    exact ⟨⟨n - 1, hlt⟩, Nat.sub_add_cancel hn⟩
  have hp := h j
  simpa [vinogradovResiduePowerSum, hj] using hp

/-- For a fixed residue tuple, at most `s!` right tuples solve the first `s`
power-sum equations over `ZMod p`. -/
theorem fixed_left_residue_solution_count_le_factorial
    (p k s : ℕ) [Fact p.Prime] (hsk : s ≤ k) (hsp : s < p)
    (x : Fin s → ZMod p) :
    (Finset.univ.filter fun y : Fin s → ZMod p ↦
      IsVinogradovResidueSolution p k s x y).card ≤ s.factorial := by
  let solutions := Finset.univ.filter fun y : Fin s → ZMod p ↦
    IsVinogradovResidueSolution p k s x y
  let toList : (Fin s → ZMod p) ↪ List (ZMod p) :=
    ⟨List.ofFn, fun _ _ hxy ↦ List.ofFn_inj.mp hxy⟩
  calc
    solutions.card = (solutions.map toList).card := by
      rw [Finset.card_map]
    _ ≤ (List.ofFn x).permutations.toFinset.card := by
      apply Finset.card_le_card
      intro ys hys
      simp only [Finset.mem_map] at hys
      obtain ⟨y, hy, rfl⟩ := hys
      simp only [List.mem_toFinset, List.mem_permutations]
      apply Multiset.coe_eq_coe.mp
      have hsol : IsVinogradovResidueSolution p k s x y :=
        (Finset.mem_filter.mp hy).2
      simpa using (hsol.multiset_eq p k s hsk hsp).symm
    _ ≤ (List.ofFn x).permutations.length :=
      List.toFinset_card_le (List.ofFn x).permutations
    _ = s.factorial := by
      rw [List.length_permutations, List.length_ofFn]

/-- Residue tuples whose first `k` power sums equal a prescribed target. -/
noncomputable def vinogradovResidueTargetFiberSet
    (p k : ℕ) [Fact p.Prime] (target : Fin k → ZMod p) :
    Finset (Fin k → ZMod p) :=
  Finset.univ.filter fun x ↦
    ∀ j : Fin k, vinogradovResiduePowerSum p x j = target j

theorem mem_vinogradovResidueTargetFiberSet_iff
    (p k : ℕ) [Fact p.Prime] (target : Fin k → ZMod p)
    (x : Fin k → ZMod p) :
    x ∈ vinogradovResidueTargetFiberSet p k target ↔
      ∀ j : Fin k, vinogradovResiduePowerSum p x j = target j := by
  simp [vinogradovResidueTargetFiberSet]

/-- When `k < p`, every prescribed vector of the first `k` power sums has at
most `k!` ordered residue-tuple preimages. -/
theorem card_vinogradovResidueTargetFiberSet_le_factorial
    (p k : ℕ) [Fact p.Prime] (hkp : k < p)
    (target : Fin k → ZMod p) :
    (vinogradovResidueTargetFiberSet p k target).card ≤ k.factorial := by
  by_cases hempty : vinogradovResidueTargetFiberSet p k target = ∅
  · simp [hempty]
  · have hnonempty : (vinogradovResidueTargetFiberSet p k target).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨x₀, hx₀⟩ := hnonempty
    calc
      (vinogradovResidueTargetFiberSet p k target).card ≤
          (Finset.univ.filter fun y : Fin k → ZMod p ↦
            IsVinogradovResidueSolution p k k x₀ y).card := by
        apply Finset.card_le_card
        intro y hy
        have hx₀' :=
          (mem_vinogradovResidueTargetFiberSet_iff p k target x₀).mp hx₀
        have hy' :=
          (mem_vinogradovResidueTargetFiberSet_iff p k target y).mp hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro j
        exact (hx₀' j).trans (hy' j).symm
      _ ≤ k.factorial :=
        fixed_left_residue_solution_count_le_factorial p k k le_rfl hkp x₀

end

end ZeroFreeRegion.VinogradovKorobov
