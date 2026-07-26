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

/-- Simultaneous version of normal-form cancellation. Under `γ ≤ a`, the
largest degree-dependent scale occurs in degree `r`, so all rows retain the
same residual prime-power modulus. -/
theorem vinogradovNormalFormSystem_to_uniformPowerSumCongruences
    {s : ℕ} (p c k r a γ M : ℕ) (hp : p ≠ 0)
    (hrk : r ≤ k) (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ M)
    (hspacing : M ≤ c + a) (htail : M ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (H χ θ : Fin r → Polynomial ℤ)
    (hH : ∀ i : Fin r,
      H i =
        Polynomial.C
              ((ω * (p : ℤ) ^ γ) ^ (k - (i.val + 1))) *
            Polynomial.X ^ (i.val + 1) +
          Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ i +
          Polynomial.X ^ (r + 1) * θ i)
    (x y : Fin s → ℤ)
    (hsystem :
      IsVinogradovPolynomialCongruenceSystem p M H
        (fun i ↦ (p : ℤ) ^ a * x i)
        (fun i ↦ (p : ℤ) ^ a * y i)) :
    ∀ i : Fin r, vinogradovPowerSumDifferenceInt x y (i.val + 1) ≡ 0
      [ZMOD (p : ℤ) ^ (M - (γ * (k - r) + a * r))] := by
  intro i
  let d := i.val + 1
  have hdr : d ≤ r := Nat.succ_le_iff.mpr i.isLt
  have hdk : d ≤ k := hdr.trans hrk
  have hk_split : k - d = (k - r) + (r - d) := by omega
  have hscale :
      γ * (k - d) + a * d ≤ γ * (k - r) + a * r := by
    calc
      γ * (k - d) + a * d =
          γ * (k - r) + γ * (r - d) + a * d := by
            rw [hk_split, Nat.mul_add]
      _ ≤ γ * (k - r) + a * (r - d) + a * d := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_left (Nat.mul_le_mul_right (r - d) hγa) _) _
      _ = γ * (k - r) + a * r := by
            have har : a * (r - d) + a * d = a * r := by
              rw [← Nat.mul_add, Nat.sub_add_cancel hdr]
            rw [Nat.add_assoc, har]
  have hrow := vinogradovPowerSumDifferenceInt_modEq_of_normalForm
    p c k r a γ d M hp hdk (hscale.trans hbudget)
      hspacing htail ω hω (H i) (χ i) (θ i) (hH i) x y (hsystem i)
  exact hrow.of_dvd
    (pow_dvd_pow (p : ℤ) (Nat.sub_le_sub_left hscale M))

/-- Paper-facing system form with Wooley's ambient exponent
`(k-r+1)b` and residual exponent `vinogradovFarScale`. -/
theorem vinogradovNormalFormSystem_to_farScale
    {s : ℕ} (p c k r a b γ : ℕ) (hp : p ≠ 0)
    (hrk : r ≤ k) (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (hspacing : (k - r + 1) * b ≤ c + a)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (H χ θ : Fin r → Polynomial ℤ)
    (hH : ∀ i : Fin r,
      H i =
        Polynomial.C
              ((ω * (p : ℤ) ^ γ) ^ (k - (i.val + 1))) *
            Polynomial.X ^ (i.val + 1) +
          Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ i +
          Polynomial.X ^ (r + 1) * θ i)
    (x y : Fin s → ℤ)
    (hsystem :
      IsVinogradovPolynomialCongruenceSystem p ((k - r + 1) * b) H
        (fun i ↦ (p : ℤ) ^ a * x i)
        (fun i ↦ (p : ℤ) ^ a * y i)) :
    ∀ i : Fin r, vinogradovPowerSumDifferenceInt x y (i.val + 1) ≡ 0
      [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] := by
  simpa only [vinogradovFarScale, Nat.sub_sub, Nat.mul_comm,
    Nat.add_comm] using
      vinogradovNormalFormSystem_to_uniformPowerSumCongruences
        p c k r a γ ((k - r + 1) * b) hp hrk hγa hbudget
          hspacing htail ω hω H χ θ hH x y hsystem

end

end ZeroFreeRegion.VinogradovKorobov
