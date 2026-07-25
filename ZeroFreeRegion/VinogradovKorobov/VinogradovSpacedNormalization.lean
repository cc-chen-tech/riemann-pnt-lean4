import ZeroFreeRegion.VinogradovKorobov.VinogradovTranslatedCongruence

open scoped BigOperators Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Common column-aligned low-degree main polynomial after complementary
row scaling. -/
def vinogradovAlignedSpacedMain {r : ℕ}
    (ξ : ℤ) (k : ℕ) (Ω : Fin r → ℤ) : Polynomial ℤ :=
  ∑ j : Fin r,
    Polynomial.C (ξ ^ (k - (j.val + 1)) * Ω j) *
      Polynomial.X ^ (j.val + 1)

/-- Exact normal form behind Wooley's row scaling. The low-degree failure of
literal center-power alignment is a `p^c X` correction, while the original
Taylor tail remains divisible by `X^(r+1)`. -/
theorem exists_vinogradovRowScaledSpacedNormalForm {r : ℕ}
    (p c k n : ℕ) (hnk : n ≤ k) (ξ : ℤ)
    (Ω : Fin r → ℤ) (P θ : Polynomial ℤ)
    (hΩ : ∀ j, Ω j ≡ (n.choose (j.val + 1) : ℤ)
      [ZMOD (p : ℤ) ^ c])
    (hP : P =
      (∑ j : Fin r,
        Polynomial.C (ξ ^ (n - (j.val + 1)) * Ω j) *
          Polynomial.X ^ (j.val + 1)) +
        Polynomial.X ^ (r + 1) * θ)
    (hrk : r ≤ k) :
    ∃ χ θ' : Polynomial ℤ,
      Polynomial.C (ξ ^ (k - n)) * P =
        vinogradovAlignedSpacedMain ξ k Ω +
          Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ +
          Polynomial.X ^ (r + 1) * θ' := by
  have halign (j : Fin r) :
      ξ ^ (k - n) * (ξ ^ (n - (j.val + 1)) * Ω j) ≡
        ξ ^ (k - (j.val + 1)) * Ω j [ZMOD (p : ℤ) ^ c] :=
    vinogradovRowAlignedFactor_modEq p c k n (j.val + 1)
      hnk (by omega) ξ (Ω j) (hΩ j)
  choose e he using fun j : Fin r ↦
    Int.modEq_iff_add_fac.mp (halign j).symm
  let χ : Polynomial ℤ :=
    ∑ j : Fin r, Polynomial.C (e j) * Polynomial.X ^ j.val
  have hterm (j : Fin r) :
      Polynomial.C (ξ ^ (k - n)) *
          (Polynomial.C (ξ ^ (n - (j.val + 1)) * Ω j) *
            Polynomial.X ^ (j.val + 1)) =
        Polynomial.C (ξ ^ (k - (j.val + 1)) * Ω j) *
            Polynomial.X ^ (j.val + 1) +
          Polynomial.C ((p : ℤ) ^ c) * Polynomial.X *
            (Polynomial.C (e j) * Polynomial.X ^ j.val) := by
    rw [← mul_assoc, ← Polynomial.C_mul, he j]
    simp only [map_add, map_mul]
    rw [pow_succ]
    ring
  have hlow :
      Polynomial.C (ξ ^ (k - n)) *
          (∑ j : Fin r,
            Polynomial.C (ξ ^ (n - (j.val + 1)) * Ω j) *
              Polynomial.X ^ (j.val + 1)) =
        vinogradovAlignedSpacedMain ξ k Ω +
          Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ := by
    rw [Finset.mul_sum]
    calc
      (∑ j : Fin r,
          Polynomial.C (ξ ^ (k - n)) *
            (Polynomial.C (ξ ^ (n - (j.val + 1)) * Ω j) *
              Polynomial.X ^ (j.val + 1))) =
          ∑ j : Fin r,
            (Polynomial.C (ξ ^ (k - (j.val + 1)) * Ω j) *
                Polynomial.X ^ (j.val + 1) +
              Polynomial.C ((p : ℤ) ^ c) * Polynomial.X *
                (Polynomial.C (e j) * Polynomial.X ^ j.val)) := by
            apply Finset.sum_congr rfl
            intro j _
            exact hterm j
      _ = vinogradovAlignedSpacedMain ξ k Ω +
          Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ := by
            rw [Finset.sum_add_distrib]
            simp only [vinogradovAlignedSpacedMain, χ, Finset.mul_sum]
  refine ⟨χ, Polynomial.C (ξ ^ (k - n)) * θ, ?_⟩
  rw [hP, mul_add, hlow]
  ring

/-- Simultaneous row-scaled normal form for the consecutive high-degree
translated system. It retains both the full `p^c` coefficient congruences
and their weaker modulo-`p` matrix invertibility interface. -/
theorem exists_vinogradovTranslatedSpacedSystem_normalForm
    (p c k r : ℕ) (hc : 0 < c) (hrk : r ≤ k)
    (ψ : Fin r → Polynomial ℤ) (ξ : ℤ) :
    ∃ Ω : Matrix (Fin r) (Fin r) ℤ,
      ∃ χ θ : Fin r → Polynomial ℤ,
      (∀ i j, Ω i j ≡
        (Nat.choose (vinogradovBinomialPoint k r i) (j.val + 1) : ℤ)
          [ZMOD (p : ℤ) ^ c]) ∧
      IsVinogradovBinomialCoefficientMatrix p k r Ω ∧
      ∀ i,
        Polynomial.C
            (ξ ^ (k - vinogradovBinomialPoint k r i)) *
            vinogradovCenteredTaylor ξ
              (vinogradovSpacedPolynomial p c k
                (vinogradovBinomialPoint k r i) (ψ i)) =
          vinogradovAlignedSpacedMain ξ k (Ω i) +
            Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ i +
            Polynomial.X ^ (r + 1) * θ i := by
  have hpoint (i : Fin r) : vinogradovBinomialPoint k r i ≤ k := by
    simp only [vinogradovBinomialPoint]
    omega
  choose Ω θ hΩ hexp using fun i : Fin r ↦
    exists_vinogradovCenteredTaylor_spaced_expansion_all
      p c k (vinogradovBinomialPoint k r i) r (hpoint i) (ψ i) ξ
  choose χ θ' hnormal using fun i : Fin r ↦
    exists_vinogradovRowScaledSpacedNormalForm
      p c k (vinogradovBinomialPoint k r i) (hpoint i) ξ (Ω i)
        (vinogradovCenteredTaylor ξ
          (vinogradovSpacedPolynomial p c k
            (vinogradovBinomialPoint k r i) (ψ i)))
        (θ i) (hΩ i) (hexp i) hrk
  let A : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j ↦ Ω i j
  have hAc : ∀ i j, A i j ≡
      (Nat.choose (vinogradovBinomialPoint k r i) (j.val + 1) : ℤ)
        [ZMOD (p : ℤ) ^ c] := by
    intro i j
    simpa only [A, Matrix.of_apply] using hΩ i j
  have hA : IsVinogradovBinomialCoefficientMatrix p k r A := by
    intro i j
    exact (hAc i j).of_dvd
      (show (p : ℤ) ∣ (p : ℤ) ^ c by exact dvd_pow_self _ hc.ne')
  refine ⟨A, χ, θ', hAc, hA, ?_⟩
  intro i
  simpa only [A, Matrix.of_apply] using hnormal i

end


end ZeroFreeRegion.VinogradovKorobov
