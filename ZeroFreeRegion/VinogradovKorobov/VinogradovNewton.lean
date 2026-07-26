import ZeroFreeRegion.VinogradovKorobov.VinogradovMonotonicity
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

open scoped BigOperators

private def sequencePowerSum {s : ℕ} (x : Fin s → ℚ) (n : ℕ) : ℚ :=
  ∑ i, x i ^ n

private def sequenceEsymm {s : ℕ} (x : Fin s → ℚ) (n : ℕ) : ℚ :=
  (Finset.univ.val.map x).esymm n

private theorem sequenceEsymm_newton {s : ℕ} (x : Fin s → ℚ) (n : ℕ) :
    (n : ℚ) * sequenceEsymm x n =
      (-1 : ℚ) ^ (n + 1) *
        ∑ a ∈ Finset.antidiagonal n with a.1 < n,
          (-1 : ℚ) ^ a.1 * sequenceEsymm x a.1 * sequencePowerSum x a.2 := by
  have h := congrArg (MvPolynomial.aeval x)
    (MvPolynomial.mul_esymm_eq_sum (Fin s) ℚ n)
  simpa only [map_mul, map_pow, map_sum, map_natCast, map_neg, map_one,
    MvPolynomial.aeval_esymm_eq_multiset_esymm,
    MvPolynomial.psum, MvPolynomial.aeval_X,
    sequenceEsymm, sequencePowerSum] using h

/-- Newton's identities determine a finite multiset from its first `s` power
sums.  This form is specialized to rational sequences so that the positive
integer coefficients in Newton's recurrence can be cancelled. -/
theorem multiset_eq_of_powerSums_eq {s : ℕ} (x y : Fin s → ℚ)
    (hpower : ∀ n, 1 ≤ n → n ≤ s →
      (∑ i, x i ^ n) = ∑ i, y i ^ n) :
    Finset.univ.val.map x = Finset.univ.val.map y := by
  have hesymm : ∀ n, n ≤ s → sequenceEsymm x n = sequenceEsymm y n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn
        by_cases hn0 : n = 0
        · subst n
          simp [sequenceEsymm, Multiset.esymm]
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
          have hnewtonX := sequenceEsymm_newton x n
          have hnewtonY := sequenceEsymm_newton y n
          have hsums :
              (∑ a ∈ Finset.antidiagonal n with a.1 < n,
                (-1 : ℚ) ^ a.1 * sequenceEsymm x a.1 * sequencePowerSum x a.2) =
              ∑ a ∈ Finset.antidiagonal n with a.1 < n,
                (-1 : ℚ) ^ a.1 * sequenceEsymm y a.1 * sequencePowerSum y a.2 := by
            apply Finset.sum_congr rfl
            intro a ha
            simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha
            have ha2pos : 0 < a.2 := by omega
            have ha2le : a.2 ≤ s := by omega
            rw [ih a.1 ha.2 (by omega)]
            rw [show sequencePowerSum x a.2 = sequencePowerSum y a.2 by
              simpa only [sequencePowerSum] using hpower a.2 ha2pos ha2le]
          rw [hsums] at hnewtonX
          exact mul_left_cancel₀ (by exact_mod_cast hn0)
            (hnewtonX.trans hnewtonY.symm)
  let px : Polynomial ℚ :=
    (Finset.univ.val.map x |>.map fun r => Polynomial.X - Polynomial.C r).prod
  let py : Polynomial ℚ :=
    (Finset.univ.val.map y |>.map fun r => Polynomial.X - Polynomial.C r).prod
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

/-- Once a Vinogradov system contains the first `s` power-sum equations, every
solution has the same underlying multiset on the two sides. -/
theorem IsVinogradovSolutionNat.multiset_eq {k s X : ℕ} (hsk : s ≤ k)
    {x y : Fin s → Fin X} (h : IsVinogradovSolutionNat k s X x y) :
    Finset.univ.val.map x = Finset.univ.val.map y := by
  let embed : Fin X → ℚ := fun z => (z.val + 1 : ℕ)
  have hinj : Function.Injective embed := by
    intro a b hab
    apply Fin.ext
    have hab' : a.val + 1 = b.val + 1 := Nat.cast_injective hab
    omega
  apply Multiset.map_injective hinj
  simp only [Multiset.map_map, Function.comp_apply]
  change Finset.univ.val.map (fun i => embed (x i)) =
    Finset.univ.val.map (fun i => embed (y i))
  apply multiset_eq_of_powerSums_eq
  intro n hn hns
  have hnk : n ≤ k := hns.trans hsk
  obtain ⟨j, hj⟩ : ∃ j : Fin k, j.val + 1 = n := by
    have hlt : n - 1 < k := by omega
    refine ⟨⟨n - 1, hlt⟩, ?_⟩
    · change n - 1 + 1 = n
      omega
  have hp := h j
  simpa only [vinogradovPowerSumNat, hj, Nat.cast_sum,
    Nat.cast_pow, embed] using congrArg (fun z : ℕ => (z : ℚ)) hp

end

end ZeroFreeRegion.VinogradovKorobov
