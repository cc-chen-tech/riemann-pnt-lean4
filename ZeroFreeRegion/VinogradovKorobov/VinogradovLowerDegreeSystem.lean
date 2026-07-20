import ZeroFreeRegion.VinogradovKorobov.VinogradovScaleCancellation
import ZeroFreeRegion.VinogradovKorobov.VinogradovNormalFormEvaluation

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Polynomial dilation `X ↦ qX`. -/
def vinogradovPolynomialDilation (q : ℤ)
    (φ : Polynomial ℤ) : Polynomial ℤ :=
  φ.comp (Polynomial.C q * Polynomial.X)

@[simp] theorem eval_vinogradovPolynomialDilation
    (q z : ℤ) (φ : Polynomial ℤ) :
    (vinogradovPolynomialDilation q φ).eval z = φ.eval (q * z) := by
  simp [vinogradovPolynomialDilation, Polynomial.eval_comp]

/-- Balanced polynomial sums commute with polynomial dilation. -/
theorem vinogradovPolynomialSumDifference_dilation {s : ℕ}
    (q : ℤ) (φ : Polynomial ℤ) (x y : Fin s → ℤ) :
    vinogradovPolynomialSumDifference φ
        (fun i ↦ q * x i) (fun i ↦ q * y i) =
      vinogradovPolynomialSumDifference
        (vinogradovPolynomialDilation q φ) x y := by
  unfold vinogradovPolynomialSumDifference
  simp

/-- A factorization after polynomial dilation automatically gives the
corresponding factorization of every balanced finite sum. -/
theorem vinogradovPolynomialSumDifference_of_dilation_factor {s : ℕ}
    (q A : ℤ) (H Ψ : Polynomial ℤ)
    (hfactor : vinogradovPolynomialDilation q H = Polynomial.C A * Ψ)
    (x y : Fin s → ℤ) :
    vinogradovPolynomialSumDifference H
        (fun i ↦ q * x i) (fun i ↦ q * y i) =
      A * vinogradovPolynomialSumDifference Ψ x y := by
  rw [vinogradovPolynomialSumDifference_dilation, hfactor,
    vinogradovPolynomialSumDifference_C_mul]

/-- Once the translated high-degree rows factor through a lower-degree
polynomial system with the common center scale from (7.11), prime-power
cancellation yields that lower-degree system at one uniform residual scale.

The hypothesis `hfactor` isolates the remaining constructive step: producing
the spaced polynomials `Ψ`. -/
theorem vinogradovCommonFactorSystem_to_uniformCongruences
    {s : ℕ} (p k r a γ M : ℕ) (hp : p ≠ 0)
    (hbudget : γ * (k - r) + a * r ≤ M)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (H Ψ : Fin r → Polynomial ℤ) (x y : Fin s → ℤ)
    (hfactor : ∀ i : Fin r,
      vinogradovPolynomialSumDifference (H i)
          (fun j ↦ (p : ℤ) ^ a * x j)
          (fun j ↦ (p : ℤ) ^ a * y j) =
        ω ^ (k - r) *
          (p : ℤ) ^ (γ * (k - r) + a * (i.val + 1)) *
            vinogradovPolynomialSumDifference (Ψ i) x y)
    (hsystem :
      IsVinogradovPolynomialCongruenceSystem p M H
        (fun j ↦ (p : ℤ) ^ a * x j)
        (fun j ↦ (p : ℤ) ^ a * y j)) :
    IsVinogradovPolynomialCongruenceSystem p
      (M - (γ * (k - r) + a * r)) Ψ x y := by
  apply vinogradovScaledCongruences_to_uniform
    p k r M a γ hp hbudget ω hω
      (fun i ↦ vinogradovPolynomialSumDifference (Ψ i) x y)
  intro i
  rw [← hfactor i]
  exact hsystem i

/-- Paper-facing form of common-factor cancellation, with ambient exponent
`(k-r+1)b` and lower-degree modulus `vinogradovFarScale`. -/
theorem vinogradovCommonFactorSystem_to_farScale
    {s : ℕ} (p k r a b γ : ℕ) (hp : p ≠ 0)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (H Ψ : Fin r → Polynomial ℤ) (x y : Fin s → ℤ)
    (hfactor : ∀ i : Fin r,
      vinogradovPolynomialSumDifference (H i)
          (fun j ↦ (p : ℤ) ^ a * x j)
          (fun j ↦ (p : ℤ) ^ a * y j) =
        ω ^ (k - r) *
          (p : ℤ) ^ (γ * (k - r) + a * (i.val + 1)) *
            vinogradovPolynomialSumDifference (Ψ i) x y)
    (hsystem :
      IsVinogradovPolynomialCongruenceSystem p ((k - r + 1) * b) H
        (fun j ↦ (p : ℤ) ^ a * x j)
        (fun j ↦ (p : ℤ) ^ a * y j)) :
    IsVinogradovPolynomialCongruenceSystem p
      (vinogradovFarScale k r a b γ) Ψ x y := by
  simpa only [vinogradovFarScale, Nat.sub_sub, Nat.mul_comm,
    Nat.add_comm] using
      vinogradovCommonFactorSystem_to_uniformCongruences
        p k r a γ ((k - r + 1) * b) hp hbudget
          ω hω H Ψ x y hfactor hsystem

/-- Polynomial-factorization entry point for the lower-degree system. It is
enough to construct each dilated row as the expected scalar multiple of a
polynomial `Ψ i`; the finite-sum factorization and far-scale cancellation are
then automatic. -/
theorem vinogradovDilationFactorSystem_to_farScale
    {s : ℕ} (p k r a b γ : ℕ) (hp : p ≠ 0)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (H Ψ : Fin r → Polynomial ℤ) (x y : Fin s → ℤ)
    (hfactor : ∀ i : Fin r,
      vinogradovPolynomialDilation ((p : ℤ) ^ a) (H i) =
        Polynomial.C
            (ω ^ (k - r) *
              (p : ℤ) ^ (γ * (k - r) + a * (i.val + 1))) *
          Ψ i)
    (hsystem :
      IsVinogradovPolynomialCongruenceSystem p ((k - r + 1) * b) H
        (fun j ↦ (p : ℤ) ^ a * x j)
        (fun j ↦ (p : ℤ) ^ a * y j)) :
    IsVinogradovPolynomialCongruenceSystem p
      (vinogradovFarScale k r a b γ) Ψ x y := by
  apply vinogradovCommonFactorSystem_to_farScale
    p k r a b γ hp hbudget ω hω H Ψ x y _ hsystem
  intro i
  exact vinogradovPolynomialSumDifference_of_dilation_factor
    ((p : ℤ) ^ a)
      (ω ^ (k - r) *
        (p : ℤ) ^ (γ * (k - r) + a * (i.val + 1)))
      (H i) (Ψ i) (hfactor i) x y

end


end ZeroFreeRegion.VinogradovKorobov
