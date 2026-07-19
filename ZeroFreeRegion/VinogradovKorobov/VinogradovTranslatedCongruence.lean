import ZeroFreeRegion.VinogradovKorobov.VinogradovPolynomialTranslation

open scoped BigOperators Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

@[simp] theorem eval_vinogradovCenteredTaylor
    (ξ : ℤ) (φ : Polynomial ℤ) (t : ℤ) :
    (vinogradovCenteredTaylor ξ φ).eval t =
      φ.eval (t + ξ) - φ.eval ξ := by
  simp [vinogradovCenteredTaylor, Polynomial.taylor_apply,
    add_comm]

/-- Centering a polynomial before evaluating a balanced sum difference is
the same as translating both variable tuples. -/
theorem vinogradovPolynomialSumDifference_centeredTaylor {s : ℕ}
    (ξ : ℤ) (φ : Polynomial ℤ) (x y : Fin s → ℤ) :
    vinogradovPolynomialSumDifference (vinogradovCenteredTaylor ξ φ) x y =
      vinogradovPolynomialSumDifference φ
        (fun i ↦ x i + ξ) (fun i ↦ y i + ξ) := by
  unfold vinogradovPolynomialSumDifference
  simp_rw [eval_vinogradovCenteredTaylor]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

/-- A polynomial tail beginning in degree `D` contributes a factor `q^D`
after dilation by `q`. -/
theorem dvd_vinogradovPolynomialSumDifference_scaledTail {s : ℕ}
    (q : ℤ) (D : ℕ) (θ : Polynomial ℤ) (x y : Fin s → ℤ) :
    q ^ D ∣ vinogradovPolynomialSumDifference
      (Polynomial.X ^ D * θ) (fun i ↦ q * x i) (fun i ↦ q * y i) := by
  unfold vinogradovPolynomialSumDifference
  apply dvd_sub
  · apply Finset.dvd_sum
    intro i _
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, mul_pow]
    exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  · apply Finset.dvd_sum
    intro i _
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, mul_pow]
    exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)

/-- The retained Taylor terms become the corresponding scaled power-sum
differences after evaluating at `q*x` and `q*y`. -/
theorem vinogradovPolynomialSumDifference_taylorMain {s r : ℕ}
    (ξ q : ℤ) (n : ℕ) (Ω : Fin r → ℤ) (x y : Fin s → ℤ) :
    vinogradovPolynomialSumDifference
        (∑ j : Fin r,
          Polynomial.C (ξ ^ (n - (j.val + 1)) * Ω j) *
            Polynomial.X ^ (j.val + 1))
        (fun i ↦ q * x i) (fun i ↦ q * y i) =
      ∑ j : Fin r,
        ξ ^ (n - (j.val + 1)) * Ω j * q ^ (j.val + 1) *
          vinogradovPowerSumDifferenceInt x y (j.val + 1) := by
  unfold vinogradovPolynomialSumDifference vinogradovPowerSumDifferenceInt
  simp_rw [Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_pow]
  rw [Finset.sum_comm]
  conv_lhs =>
    rhs
    rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [← Finset.mul_sum]
  ring

theorem vinogradovPolynomialSumDifference_add {s : ℕ}
    (φ ψ : Polynomial ℤ) (x y : Fin s → ℤ) :
    vinogradovPolynomialSumDifference (φ + ψ) x y =
      vinogradovPolynomialSumDifference φ x y +
        vinogradovPolynomialSumDifference ψ x y := by
  unfold vinogradovPolynomialSumDifference
  simp_rw [Polynomial.eval_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- Evaluating a centered Taylor expansion on a dilated tuple gives the
scaled power-sum main terms plus an integer multiple of the tail scale. -/
theorem exists_vinogradovPolynomialSumDifference_of_taylorExpansion
    {s r : ℕ} (ξ q : ℤ) (n : ℕ) (Ω : Fin r → ℤ)
    (P θ : Polynomial ℤ)
    (hP : P =
      (∑ j : Fin r,
        Polynomial.C (ξ ^ (n - (j.val + 1)) * Ω j) *
          Polynomial.X ^ (j.val + 1)) +
        Polynomial.X ^ (r + 1) * θ)
    (x y : Fin s → ℤ) :
    ∃ E : ℤ,
      vinogradovPolynomialSumDifference P
          (fun i ↦ q * x i) (fun i ↦ q * y i) =
        (∑ j : Fin r,
          ξ ^ (n - (j.val + 1)) * Ω j * q ^ (j.val + 1) *
            vinogradovPowerSumDifferenceInt x y (j.val + 1)) +
          q ^ (r + 1) * E := by
  obtain ⟨E, hE⟩ := dvd_vinogradovPolynomialSumDifference_scaledTail
    q (r + 1) θ x y
  refine ⟨E, ?_⟩
  rw [hP, vinogradovPolynomialSumDifference_add,
    vinogradovPolynomialSumDifference_taylorMain, hE]

/-- Equation (7.10) after exact Taylor expansion: every translated row is a
perturbed binomial combination of scaled power-sum differences, up to a tail
carrying the full factor `q^(r+1)`. -/
theorem exists_vinogradovTranslatedSpacedSystem_sumDifference
    {s r : ℕ} (p c k : ℕ) (hc : 0 < c) (hrk : r ≤ k)
    (ψ : Fin r → Polynomial ℤ) (ξ q : ℤ) (x y : Fin s → ℤ) :
    ∃ Ω : Matrix (Fin r) (Fin r) ℤ, ∃ E : Fin r → ℤ,
      IsVinogradovBinomialCoefficientMatrix p k r Ω ∧
      ∀ i,
        vinogradovPolynomialSumDifference
            (vinogradovSpacedPolynomial p c k
              (vinogradovBinomialPoint k r i) (ψ i))
            (fun z ↦ ξ + q * x z) (fun z ↦ ξ + q * y z) =
          (∑ j : Fin r,
            ξ ^ (vinogradovBinomialPoint k r i - (j.val + 1)) *
              Ω i j * q ^ (j.val + 1) *
                vinogradovPowerSumDifferenceInt x y (j.val + 1)) +
            q ^ (r + 1) * E i := by
  obtain ⟨Ω, θ, hΩ, hexp⟩ :=
    exists_vinogradovTranslatedSpacedSystemExpansion
      p c k r hc hrk ψ ξ
  choose E hE using fun i : Fin r ↦
    exists_vinogradovPolynomialSumDifference_of_taylorExpansion
      ξ q (vinogradovBinomialPoint k r i) (Ω i)
        (vinogradovCenteredTaylor ξ
          (vinogradovSpacedPolynomial p c k
            (vinogradovBinomialPoint k r i) (ψ i)))
        (θ i) (hexp i) x y
  refine ⟨Ω, E, hΩ, ?_⟩
  intro i
  calc
    vinogradovPolynomialSumDifference
          (vinogradovSpacedPolynomial p c k
            (vinogradovBinomialPoint k r i) (ψ i))
          (fun z ↦ ξ + q * x z) (fun z ↦ ξ + q * y z) =
        vinogradovPolynomialSumDifference
          (vinogradovCenteredTaylor ξ
            (vinogradovSpacedPolynomial p c k
              (vinogradovBinomialPoint k r i) (ψ i)))
          (fun z ↦ q * x z) (fun z ↦ q * y z) := by
            rw [vinogradovPolynomialSumDifference_centeredTaylor]
            congr 1 <;> funext z <;> ring
    _ = _ := hE i

end


end ZeroFreeRegion.VinogradovKorobov
