import ZeroFreeRegion.VinogradovKorobov.VinogradovMatrixNormalization

open scoped BigOperators Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

theorem vinogradovPolynomialSumDifference_C_mul {s : ℕ}
    (A : ℤ) (φ : Polynomial ℤ) (x y : Fin s → ℤ) :
    vinogradovPolynomialSumDifference (Polynomial.C A * φ) x y =
      A * vinogradovPolynomialSumDifference φ x y := by
  unfold vinogradovPolynomialSumDifference
  simp_rw [Polynomial.eval_mul, Polynomial.eval_C]
  simp only [← Finset.mul_sum]
  ring

/-- Exact scaled monomial contribution to a balanced polynomial sum. -/
theorem vinogradovPolynomialSumDifference_monomial_scaled {s : ℕ}
    (A q : ℤ) (d : ℕ) (x y : Fin s → ℤ) :
    vinogradovPolynomialSumDifference
        (Polynomial.C A * Polynomial.X ^ d)
        (fun i ↦ q * x i) (fun i ↦ q * y i) =
      A * q ^ d * vinogradovPowerSumDifferenceInt x y d := by
  unfold vinogradovPolynomialSumDifference vinogradovPowerSumDifferenceInt
  simp_rw [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, mul_pow]
  simp only [← Finset.mul_sum]
  ring

/-- The `p^c X` correction in a spaced normal form gains the additional
dilation factor `p^a`. -/
theorem dvd_vinogradovPolynomialSumDifference_spacingTerm {s : ℕ}
    (p c a : ℕ) (χ : Polynomial ℤ) (x y : Fin s → ℤ) :
    (p : ℤ) ^ (c + a) ∣
      vinogradovPolynomialSumDifference
        (Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ)
        (fun i ↦ (p : ℤ) ^ a * x i)
        (fun i ↦ (p : ℤ) ^ a * y i) := by
  have hscale := dvd_vinogradovPolynomialSumDifference_scaledTail
    ((p : ℤ) ^ a) 1 χ x y
  rw [mul_assoc, vinogradovPolynomialSumDifference_C_mul]
  simp only [pow_one] at hscale
  rw [pow_add]
  exact mul_dvd_mul_left ((p : ℤ) ^ c) hscale

/-- Evaluation of one identity-normalized row. The main monomial and the two
error mechanisms expose their exact prime-power scales separately. -/
theorem exists_vinogradovPolynomialSumDifference_normalForm_evaluation
    {s : ℕ} (p c k r a γ d : ℕ) (_hdk : d ≤ k)
    (ω : ℤ) (H χ θ : Polynomial ℤ)
    (hH : H =
      Polynomial.C ((ω * (p : ℤ) ^ γ) ^ (k - d)) *
          Polynomial.X ^ d +
        Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ +
        Polynomial.X ^ (r + 1) * θ)
    (x y : Fin s → ℤ) :
    ∃ E₁ E₂ : ℤ,
      vinogradovPolynomialSumDifference H
          (fun i ↦ (p : ℤ) ^ a * x i)
          (fun i ↦ (p : ℤ) ^ a * y i) =
        ω ^ (k - d) *
            (p : ℤ) ^ (γ * (k - d) + a * d) *
              vinogradovPowerSumDifferenceInt x y d +
          (p : ℤ) ^ (c + a) * E₁ +
          (p : ℤ) ^ (a * (r + 1)) * E₂ := by
  obtain ⟨E₁, hE₁⟩ :=
    dvd_vinogradovPolynomialSumDifference_spacingTerm p c a χ x y
  obtain ⟨E₂, hE₂⟩ :=
    dvd_vinogradovPolynomialSumDifference_scaledTail
      ((p : ℤ) ^ a) (r + 1) θ x y
  refine ⟨E₁, E₂, ?_⟩
  rw [hH, vinogradovPolynomialSumDifference_add,
    vinogradovPolynomialSumDifference_add,
    vinogradovPolynomialSumDifference_monomial_scaled, hE₁, hE₂]
  simp only [mul_pow]
  have hpMain :
      ((p : ℤ) ^ γ) ^ (k - d) * ((p : ℤ) ^ a) ^ d =
        (p : ℤ) ^ (γ * (k - d) + a * d) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
  have hpTail : ((p : ℤ) ^ a) ^ (r + 1) =
      (p : ℤ) ^ (a * (r + 1)) := by
    rw [← pow_mul]
  have hmainFull :
      ω ^ (k - d) * ((p : ℤ) ^ γ) ^ (k - d) *
          ((p : ℤ) ^ a) ^ d =
        ω ^ (k - d) * (p : ℤ) ^ (γ * (k - d) + a * d) := by
    rw [mul_assoc, hpMain]
  rw [hmainFull, hpTail]

end


end ZeroFreeRegion.VinogradovKorobov
