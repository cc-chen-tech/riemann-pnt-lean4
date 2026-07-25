import ZeroFreeRegion.VinogradovKorobov.VinogradovMatrixNormalization

open scoped BigOperators Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

example {r : ℕ} (B Ω : Matrix (Fin r) (Fin r) ℤ)
    (ξ : ℤ) (k : ℕ) (i : Fin r) :
    vinogradovPolynomialMatrixCombination B
        (fun row ↦ vinogradovAlignedSpacedMain ξ k (Ω row)) i =
      vinogradovAlignedSpacedMain ξ k ((B * Ω) i) :=
  vinogradovPolynomialMatrixCombination_alignedSpacedMain B Ω ξ k i

example {r : ℕ} (p c k : ℕ) (ξ : ℤ)
    (B Ω : Matrix (Fin r) (Fin r) ℤ)
    (F χ θ : Fin r → Polynomial ℤ)
    (hF : ∀ i,
      F i = vinogradovAlignedSpacedMain ξ k (Ω i) +
        Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ i +
        Polynomial.X ^ (r + 1) * θ i)
    (i : Fin r) :
    vinogradovPolynomialMatrixCombination B F i =
      vinogradovAlignedSpacedMain ξ k ((B * Ω) i) +
        Polynomial.C ((p : ℤ) ^ c) * Polynomial.X *
          vinogradovPolynomialMatrixCombination B χ i +
        Polynomial.X ^ (r + 1) *
          vinogradovPolynomialMatrixCombination B θ i :=
  vinogradovPolynomialMatrixCombination_spacedNormalForm
    p c k ξ B Ω F χ θ hF i

example {r : ℕ} (p c k : ℕ) (ξ : ℤ)
    (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r)
    (hA : ∀ j, A i j ≡ (if i = j then 1 else 0)
      [ZMOD (p : ℤ) ^ c]) :
    ∃ χ : Polynomial ℤ,
      vinogradovAlignedSpacedMain ξ k (A i) =
        Polynomial.C (ξ ^ (k - (i.val + 1))) *
            Polynomial.X ^ (i.val + 1) +
          Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ :=
  exists_vinogradovAlignedSpacedMain_eq_identity_add_spacing
    p c k ξ A i hA

example (p M r : ℕ) (B Ω : Matrix (Fin r) (Fin r) ℤ)
    (hprod :
      Matrix.of (fun i j ↦ (B i j : ZMod (p ^ M))) *
          Matrix.of (fun i j ↦ (Ω i j : ZMod (p ^ M))) = 1) :
    ∀ i j, (B * Ω) i j ≡ (if i = j then 1 else 0)
      [ZMOD (p : ℤ) ^ M] :=
  intMatrix_mul_modEq_identity_of_cast_mul_eq_one p M r B Ω hprod

example (p k r c M : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hM : 0 < M) (hcM : c ≤ M)
    (Ω : Matrix (Fin r) (Fin r) ℤ)
    (hΩ : IsVinogradovBinomialCoefficientMatrix p k r Ω) :
    ∃ B : Matrix (Fin r) (Fin r) ℤ,
      (∀ i j, (B * Ω) i j ≡ (if i = j then 1 else 0)
        [ZMOD (p : ℤ) ^ c]) ∧
      IsUnit
        (Matrix.of (fun i j ↦ (B i j : ZMod (p ^ M)))).det :=
  exists_vinogradovBinomial_leftInverse_mod_spacing
    p k r c M hrk hkp hM hcM Ω hΩ

example (p c k r M : ℕ) [Fact p.Prime]
    (hc : 0 < c) (hrk : r ≤ k) (hkp : k < p)
    (hM : 0 < M) (hcM : c ≤ M)
    (ψ : Fin r → Polynomial ℤ) (ξ : ℤ) :
    ∃ B : Matrix (Fin r) (Fin r) ℤ,
      ∃ χ θ : Fin r → Polynomial ℤ,
      IsUnit
          (Matrix.of (fun i j ↦ (B i j : ZMod (p ^ M)))).det ∧
      (∀ i,
        vinogradovPolynomialMatrixCombination B
            (fun row ↦
              Polynomial.C
                  (ξ ^ (k - vinogradovBinomialPoint k r row)) *
                vinogradovCenteredTaylor ξ
                  (vinogradovSpacedPolynomial p c k
                    (vinogradovBinomialPoint k r row) (ψ row))) i =
          Polynomial.C (ξ ^ (k - (i.val + 1))) *
              Polynomial.X ^ (i.val + 1) +
            Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ i +
            Polynomial.X ^ (r + 1) * θ i) ∧
      ∀ {s : ℕ} (x y : Fin s → ℤ),
        IsVinogradovPolynomialCongruenceSystem p M
            (vinogradovPolynomialMatrixCombination B
              (fun row ↦
                Polynomial.C
                    (ξ ^ (k - vinogradovBinomialPoint k r row)) *
                  vinogradovCenteredTaylor ξ
                    (vinogradovSpacedPolynomial p c k
                      (vinogradovBinomialPoint k r row) (ψ row)))) x y ↔
          IsVinogradovPolynomialCongruenceSystem p M
            (fun row ↦
              Polynomial.C
                  (ξ ^ (k - vinogradovBinomialPoint k r row)) *
                vinogradovCenteredTaylor ξ
                  (vinogradovSpacedPolynomial p c k
                    (vinogradovBinomialPoint k r row) (ψ row))) x y :=
  exists_vinogradovTranslatedSpacedSystem_identityNormalForm
    p c k r M hc hrk hkp hM hcM ψ ξ

end ZeroFreeRegion.VinogradovKorobov
