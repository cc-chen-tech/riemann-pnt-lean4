import ZeroFreeRegion.VinogradovKorobov.VinogradovNormalFormEvaluation
import ZeroFreeRegion.VinogradovKorobov.VinogradovScaleCancellation

open scoped Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- A row in identity normal form forces the corresponding power-sum
difference after the spacing and Taylor errors vanish at the ambient scale.
The distinguished prime-power factor and the factor coprime to `p` are then
cancelled from the congruence. -/
theorem vinogradovPowerSumDifferenceInt_modEq_of_normalForm
    {s : ℕ} (p c k r a γ d M : ℕ) (hp : p ≠ 0) (hdk : d ≤ k)
    (hmain : γ * (k - d) + a * d ≤ M)
    (hspacing : M ≤ c + a) (htail : M ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (H χ θ : Polynomial ℤ)
    (hH : H =
      Polynomial.C ((ω * (p : ℤ) ^ γ) ^ (k - d)) *
          Polynomial.X ^ d +
        Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ +
        Polynomial.X ^ (r + 1) * θ)
    (x y : Fin s → ℤ)
    (hcong :
      vinogradovPolynomialSumDifference H
          (fun i ↦ (p : ℤ) ^ a * x i)
          (fun i ↦ (p : ℤ) ^ a * y i) ≡ 0
        [ZMOD (p : ℤ) ^ M]) :
    vinogradovPowerSumDifferenceInt x y d ≡ 0
      [ZMOD (p : ℤ) ^ (M - (γ * (k - d) + a * d))] := by
  obtain ⟨E₁, E₂, hEval⟩ :=
    exists_vinogradovPolynomialSumDifference_normalForm_evaluation
      p c k r a γ d hdk ω H χ θ hH x y
  rw [hEval] at hcong
  have herror₁ : (p : ℤ) ^ (c + a) * E₁ ≡ 0
      [ZMOD (p : ℤ) ^ M] := by
    rw [Int.modEq_zero_iff_dvd]
    exact (pow_dvd_pow (p : ℤ) hspacing).trans (dvd_mul_right _ _)
  have herror₂ : (p : ℤ) ^ (a * (r + 1)) * E₂ ≡ 0
      [ZMOD (p : ℤ) ^ M] := by
    rw [Int.modEq_zero_iff_dvd]
    exact (pow_dvd_pow (p : ℤ) htail).trans (dvd_mul_right _ _)
  have hmainCong :
      ω ^ (k - d) * (p : ℤ) ^ (γ * (k - d) + a * d) *
            vinogradovPowerSumDifferenceInt x y d +
          (p : ℤ) ^ (c + a) * E₁ +
          (p : ℤ) ^ (a * (r + 1)) * E₂ ≡
        ω ^ (k - d) * (p : ℤ) ^ (γ * (k - d) + a * d) *
            vinogradovPowerSumDifferenceInt x y d
        [ZMOD (p : ℤ) ^ M] := by
    simpa only [add_zero] using
      ((Int.ModEq.rfl :
          ω ^ (k - d) * (p : ℤ) ^ (γ * (k - d) + a * d) *
                vinogradovPowerSumDifferenceInt x y d ≡
            ω ^ (k - d) * (p : ℤ) ^ (γ * (k - d) + a * d) *
                vinogradovPowerSumDifferenceInt x y d
            [ZMOD (p : ℤ) ^ M]).add herror₁).add herror₂
  have hscaled :
      ω ^ (k - d) * (p : ℤ) ^ (γ * (k - d) + a * d) *
          vinogradovPowerSumDifferenceInt x y d ≡ 0
        [ZMOD (p : ℤ) ^ M] :=
    hmainCong.symm.trans hcong
  exact modEq_zero_cancel_coprime_primePower_scale
    p (k - d) (γ * (k - d) + a * d) M hp hmain
      ω (vinogradovPowerSumDifferenceInt x y d) hω hscaled

end

end ZeroFreeRegion.VinogradovKorobov
