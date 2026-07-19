import ZeroFreeRegion.VinogradovKorobov.VinogradovHighDegreeExpansion
import Mathlib.Algebra.Polynomial.Div

open scoped BigOperators Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Difference of two sums of evaluations of an integer polynomial. -/
def vinogradovPolynomialSumDifference {s : ℕ}
    (φ : Polynomial ℤ) (x y : Fin s → ℤ) : ℤ :=
  (∑ i, φ.eval (x i)) - ∑ i, φ.eval (y i)

/-- Polynomial evaluation differences on a common affine residue class are
divisible by the affine scale. -/
theorem dvd_vinogradovPolynomialSumDifference_affine {s : ℕ}
    (q ξ : ℤ) (φ : Polynomial ℤ) (x y : Fin s → ℤ) :
    q ∣ vinogradovPolynomialSumDifference φ
      (fun i ↦ ξ + q * x i) (fun i ↦ ξ + q * y i) := by
  unfold vinogradovPolynomialSumDifference
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro i _
  have hpoint : q ∣ (ξ + q * x i) - (ξ + q * y i) := by
    refine ⟨x i - y i, ?_⟩
    ring
  exact hpoint.trans
    (Polynomial.sub_dvd_eval_sub
      (ξ + q * x i) (ξ + q * y i) φ)

/-- Normal form for one member of a `p^c`-spaced polynomial system. -/
def vinogradovSpacedPolynomial
    (p c k n : ℕ) (ψ : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.X ^ n +
    Polynomial.C ((p : ℤ) ^ c) * Polynomial.X ^ (k + 1) * ψ

@[simp] theorem eval_vinogradovSpacedPolynomial
    (p c k n : ℕ) (ψ : Polynomial ℤ) (t : ℤ) :
    (vinogradovSpacedPolynomial p c k n ψ).eval t =
      t ^ n + (p : ℤ) ^ c * t ^ (k + 1) * ψ.eval t := by
  simp [vinogradovSpacedPolynomial]

/-- A spaced-polynomial sum difference is a monomial power-sum difference
plus `p^c` times a polynomial correction. -/
theorem vinogradovPolynomialSumDifference_spaced_eq {s : ℕ}
    (p c k n : ℕ) (ψ : Polynomial ℤ) (x y : Fin s → ℤ) :
    vinogradovPolynomialSumDifference
        (vinogradovSpacedPolynomial p c k n ψ) x y =
      vinogradovPowerSumDifferenceInt x y n +
        (p : ℤ) ^ c * vinogradovPolynomialSumDifference
          (Polynomial.X ^ (k + 1) * ψ) x y := by
  let correction := Polynomial.X ^ (k + 1) * ψ
  have heval (t : ℤ) :
      (vinogradovSpacedPolynomial p c k n ψ).eval t =
        t ^ n + (p : ℤ) ^ c * correction.eval t := by
    simp [correction]
    ring
  unfold vinogradovPolynomialSumDifference vinogradovPowerSumDifferenceInt
  simp_rw [heval]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  dsimp only [correction]
  ring

/-- After affine substitution at scale `p^a`, the perturbation in a
`p^c`-spaced polynomial contributes only modulo `p^(c+a)`. -/
theorem vinogradovPolynomialSumDifference_spaced_affine_modEq_monomial
    {s : ℕ} (p c a k n : ℕ) (ψ : Polynomial ℤ) (ξ : ℤ)
    (x y : Fin s → ℤ) :
    vinogradovPolynomialSumDifference
        (vinogradovSpacedPolynomial p c k n ψ)
        (fun i ↦ ξ + (p : ℤ) ^ a * x i)
        (fun i ↦ ξ + (p : ℤ) ^ a * y i) ≡
      vinogradovPowerSumDifferenceInt
        (fun i ↦ ξ + (p : ℤ) ^ a * x i)
        (fun i ↦ ξ + (p : ℤ) ^ a * y i) n
      [ZMOD (p : ℤ) ^ (c + a)] := by
  let correction := Polynomial.X ^ (k + 1) * ψ
  let correctionDifference := vinogradovPolynomialSumDifference correction
    (fun i ↦ ξ + (p : ℤ) ^ a * x i)
    (fun i ↦ ξ + (p : ℤ) ^ a * y i)
  obtain ⟨z, hz⟩ := dvd_vinogradovPolynomialSumDifference_affine
    ((p : ℤ) ^ a) ξ correction x y
  have hcorrection :
      (p : ℤ) ^ c * correctionDifference ≡ 0
        [ZMOD (p : ℤ) ^ (c + a)] := by
    rw [Int.modEq_zero_iff_dvd]
    refine ⟨z, ?_⟩
    dsimp only [correctionDifference, correction] at hz ⊢
    rw [hz, pow_add]
    ring
  rw [vinogradovPolynomialSumDifference_spaced_eq]
  have hadd := (Int.ModEq.refl
    (vinogradovPowerSumDifferenceInt
      (fun i ↦ ξ + (p : ℤ) ^ a * x i)
      (fun i ↦ ξ + (p : ℤ) ^ a * y i) n)).add hcorrection
  simpa only [correctionDifference, correction, add_zero] using hadd

/-- A spaced-polynomial congruence at exponent `M ≤ c+a` therefore implies
the corresponding monomial congruence at exponent `M`. -/
theorem monomial_modEq_zero_of_spaced_affine_modEq_zero {s : ℕ}
    (p c a k n M : ℕ) (hM : M ≤ c + a) (ψ : Polynomial ℤ) (ξ : ℤ)
    (x y : Fin s → ℤ)
    (hspaced :
      vinogradovPolynomialSumDifference
          (vinogradovSpacedPolynomial p c k n ψ)
          (fun i ↦ ξ + (p : ℤ) ^ a * x i)
          (fun i ↦ ξ + (p : ℤ) ^ a * y i) ≡ 0
        [ZMOD (p : ℤ) ^ M]) :
    vinogradovPowerSumDifferenceInt
        (fun i ↦ ξ + (p : ℤ) ^ a * x i)
        (fun i ↦ ξ + (p : ℤ) ^ a * y i) n ≡ 0
      [ZMOD (p : ℤ) ^ M] := by
  have hcompare :=
    vinogradovPolynomialSumDifference_spaced_affine_modEq_monomial
      p c a k n ψ ξ x y
  have hcompareM := hcompare.of_dvd (pow_dvd_pow (p : ℤ) hM)
  exact hcompareM.symm.trans hspaced

/-- In the range where both the spaced perturbation and the affine binomial
tail are absorbed by the ambient modulus, raw high-degree congruences for a
`p^c`-spaced system imply the common lower-degree far-scale congruences. -/
theorem vinogradovSpaced_highDegree_to_farScale_of_scales {s : ℕ}
    (p c k r a b γ : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b) (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (hspacedScale : (k - r + 1) * b ≤ c + a)
    (htailScale : (k - r + 1) * b ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (ψ : Fin r → Polynomial ℤ) (x y : Fin s → ℤ)
    (hraw : ∀ i : Fin r,
      vinogradovPolynomialSumDifference
          (vinogradovSpacedPolynomial p c k
            (vinogradovBinomialPoint k r i) (ψ i))
          (fun z ↦ ω * (p : ℤ) ^ γ + (p : ℤ) ^ a * x z)
          (fun z ↦ ω * (p : ℤ) ^ γ + (p : ℤ) ^ a * y z) ≡ 0
        [ZMOD (p : ℤ) ^ ((k - r + 1) * b)]) :
    ∀ j : Fin r,
      vinogradovPowerSumDifferenceInt x y (j.val + 1) ≡ 0
        [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] := by
  apply vinogradovMonomial_highDegree_to_farScale_of_tailScale
    p k r a b γ hrk hkp hb hγa hbudget htailScale ω hω x y
  intro i
  exact monomial_modEq_zero_of_spaced_affine_modEq_zero
    p c a k (vinogradovBinomialPoint k r i) ((k - r + 1) * b)
      hspacedScale (ψ i) (ω * (p : ℤ) ^ γ) x y (hraw i)

end

end ZeroFreeRegion.VinogradovKorobov
