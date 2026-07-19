import ZeroFreeRegion.VinogradovKorobov.VinogradovIntegralMatrixTransform
import Mathlib.Algebra.Polynomial.Taylor

open scoped BigOperators Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Taylor expansion at an integer center with its constant term removed. -/
def vinogradovCenteredTaylor (ξ : ℤ)
    (φ : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.taylor ξ φ - Polynomial.C (φ.eval ξ)

@[simp] theorem coeff_zero_vinogradovCenteredTaylor
    (ξ : ℤ) (φ : Polynomial ℤ) :
    (vinogradovCenteredTaylor ξ φ).coeff 0 = 0 := by
  simp [vinogradovCenteredTaylor]

/-- A coefficient below the initial degree of `X^D * ψ` retains the
corresponding power of the translation center. -/
theorem pow_sub_dvd_coeff_taylor_X_pow_mul
    (D m : ℕ) (hmD : m ≤ D) (ψ : Polynomial ℤ) (ξ : ℤ) :
    ξ ^ (D - m) ∣
      (Polynomial.taylor ξ (Polynomial.X ^ D * ψ)).coeff m := by
  rw [Polynomial.taylor_mul, Polynomial.taylor_X_pow,
    Polynomial.coeff_mul]
  apply Finset.dvd_sum
  intro ij hij
  rw [Polynomial.coeff_X_add_C_pow]
  have him : ij.1 ≤ m := by
    have hij' := Finset.mem_antidiagonal.mp hij
    omega
  have hpow : ξ ^ (D - m) ∣ ξ ^ (D - ij.1) :=
    pow_dvd_pow ξ (by omega)
  exact hpow.trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _))

/-- Exact positive-degree coefficient formula before reducing modulo the
spacing modulus. -/
theorem coeff_vinogradovCenteredTaylor_spaced_eq
    (p c k n m : ℕ) (hm : 0 < m) (ψ : Polynomial ℤ) (ξ : ℤ) :
    (vinogradovCenteredTaylor ξ
      (vinogradovSpacedPolynomial p c k n ψ)).coeff m =
      ξ ^ (n - m) * (n.choose m : ℤ) +
        (p : ℤ) ^ c *
          (Polynomial.taylor ξ (Polynomial.X ^ (k + 1) * ψ)).coeff m := by
  rw [vinogradovCenteredTaylor, Polynomial.coeff_sub,
    Polynomial.coeff_C_ne_zero hm.ne', sub_zero]
  simp only [vinogradovSpacedPolynomial, map_add,
    Polynomial.taylor_X_pow, Polynomial.taylor_mul,
    Polynomial.taylor_C, Polynomial.coeff_add]
  rw [mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]

/-- Every positive-degree coefficient of a translated `p^c`-spaced
polynomial agrees modulo `p^c` with the corresponding translated monomial
coefficient. -/
theorem coeff_vinogradovCenteredTaylor_spaced_modEq
    (p c k n m : ℕ) (hm : 0 < m) (ψ : Polynomial ℤ) (ξ : ℤ) :
    (vinogradovCenteredTaylor ξ
      (vinogradovSpacedPolynomial p c k n ψ)).coeff m ≡
      ξ ^ (n - m) * (n.choose m : ℤ) [ZMOD (p : ℤ) ^ c] := by
  rw [coeff_vinogradovCenteredTaylor_spaced_eq p c k n m hm ψ ξ]
  have hcorrection :
      (p : ℤ) ^ c *
          (Polynomial.taylor ξ (Polynomial.X ^ (k + 1) * ψ)).coeff m ≡ 0
        [ZMOD (p : ℤ) ^ c] := by
    rw [Int.modEq_zero_iff_dvd]
    exact dvd_mul_right _ _
  simpa only [add_zero] using
    (Int.ModEq.refl (ξ ^ (n - m) * (n.choose m : ℤ))).add hcorrection

/-- In the degree range used by Wooley's translated system, each retained
coefficient factors by the monomial center power. The residual coefficient
matrix is congruent modulo `p^c` to the binomial coefficient matrix. -/
theorem exists_vinogradovCenteredTaylor_spaced_coeff_factor
    (p c k n m : ℕ) (hnk : n ≤ k) (hm0 : 0 < m) (hmn : m ≤ n)
    (ψ : Polynomial ℤ) (ξ : ℤ) :
    ∃ Ω : ℤ,
      (vinogradovCenteredTaylor ξ
        (vinogradovSpacedPolynomial p c k n ψ)).coeff m =
          ξ ^ (n - m) * Ω ∧
        Ω ≡ (n.choose m : ℤ) [ZMOD (p : ℤ) ^ c] := by
  have hmD : m ≤ k + 1 := by omega
  obtain ⟨E, hE⟩ := pow_sub_dvd_coeff_taylor_X_pow_mul
    (k + 1) m hmD ψ ξ
  let Ω : ℤ := (n.choose m : ℤ) +
    (p : ℤ) ^ c * ξ ^ (k + 1 - n) * E
  refine ⟨Ω, ?_, ?_⟩
  · rw [coeff_vinogradovCenteredTaylor_spaced_eq p c k n m hm0 ψ ξ,
      hE]
    dsimp only [Ω]
    have hexp : k + 1 - m = (n - m) + (k + 1 - n) := by omega
    rw [hexp, pow_add]
    ring
  · dsimp only [Ω]
    have hzero :
        (p : ℤ) ^ c * ξ ^ (k + 1 - n) * E ≡ 0
          [ZMOD (p : ℤ) ^ c] := by
      rw [Int.modEq_zero_iff_dvd]
      exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)
    simpa only [add_zero] using
      (Int.ModEq.refl (n.choose m : ℤ)).add hzero

/-- Full coefficient range. Above the monomial degree, the truncated natural
exponent is zero and the binomial coefficient vanishes, so the spacing
congruence supplies the required coefficient directly. -/
theorem exists_vinogradovCenteredTaylor_spaced_coeff_factor_all
    (p c k n m : ℕ) (hnk : n ≤ k) (hm0 : 0 < m)
    (ψ : Polynomial ℤ) (ξ : ℤ) :
    ∃ Ω : ℤ,
      (vinogradovCenteredTaylor ξ
        (vinogradovSpacedPolynomial p c k n ψ)).coeff m =
          ξ ^ (n - m) * Ω ∧
        Ω ≡ (n.choose m : ℤ) [ZMOD (p : ℤ) ^ c] := by
  by_cases hmn : m ≤ n
  · exact exists_vinogradovCenteredTaylor_spaced_coeff_factor
      p c k n m hnk hm0 hmn ψ ξ
  · refine ⟨(vinogradovCenteredTaylor ξ
        (vinogradovSpacedPolynomial p c k n ψ)).coeff m, ?_, ?_⟩
    · simp only [Nat.sub_eq_zero_of_le (Nat.le_of_lt (lt_of_not_ge hmn)),
        pow_zero, one_mul]
    · simpa only [Nat.sub_eq_zero_of_le
          (Nat.le_of_lt (lt_of_not_ge hmn)), pow_zero, one_mul] using
        coeff_vinogradovCenteredTaylor_spaced_modEq
          p c k n m hm0 ψ ξ

/-- Numeric row/column alignment underlying the translated coefficient
matrix. Above the monomial degree, the coefficient itself is a spacing
error because the corresponding binomial coefficient is zero. -/
theorem vinogradovRowAlignedFactor_modEq
    (p c k n m : ℕ) (hnk : n ≤ k) (hmk : m ≤ k)
    (ξ Ω : ℤ)
    (hΩ : Ω ≡ (n.choose m : ℤ) [ZMOD (p : ℤ) ^ c]) :
    ξ ^ (k - n) * (ξ ^ (n - m) * Ω) ≡
      ξ ^ (k - m) * Ω [ZMOD (p : ℤ) ^ c] := by
  by_cases hmn : m ≤ n
  · have hexp : k - n + (n - m) = k - m := by omega
    rw [← mul_assoc, ← pow_add, hexp]
  · have hnm : n < m := lt_of_not_ge hmn
    have hΩ0 : Ω ≡ 0 [ZMOD (p : ℤ) ^ c] := by
      simpa only [Nat.choose_eq_zero_of_lt hnm, Nat.cast_zero] using hΩ
    have hleft :
        ξ ^ (k - n) * (ξ ^ (n - m) * Ω) ≡ 0
          [ZMOD (p : ℤ) ^ c] := by
      simpa only [mul_assoc, mul_zero] using
        hΩ0.mul_left (ξ ^ (k - n) * ξ ^ (n - m))
    have hright : ξ ^ (k - m) * Ω ≡ 0 [ZMOD (p : ℤ) ^ c] := by
      simpa only [mul_zero] using hΩ0.mul_left (ξ ^ (k - m))
    exact hleft.trans hright.symm

/-- Multiplying row degree `n` by the complementary center power aligns its
retained coefficients with the common column factor `ξ^(k-m)` modulo the
spacing modulus. Entries above the monomial degree are absorbed because their
binomial coefficient is zero. -/
theorem exists_vinogradovCenteredTaylor_spaced_aligned_coeff
    (p c k n m : ℕ) (hnk : n ≤ k) (hm0 : 0 < m) (hmk : m ≤ k)
    (ψ : Polynomial ℤ) (ξ : ℤ) :
    ∃ Ω : ℤ,
      Ω ≡ (n.choose m : ℤ) [ZMOD (p : ℤ) ^ c] ∧
      ξ ^ (k - n) *
          (vinogradovCenteredTaylor ξ
            (vinogradovSpacedPolynomial p c k n ψ)).coeff m ≡
        ξ ^ (k - m) * Ω [ZMOD (p : ℤ) ^ c] := by
  obtain ⟨Ω, hcoeff, hΩ⟩ :=
    exists_vinogradovCenteredTaylor_spaced_coeff_factor_all
      p c k n m hnk hm0 ψ ξ
  refine ⟨Ω, hΩ, ?_⟩
  rw [hcoeff]
  exact vinogradovRowAlignedFactor_modEq p c k n m hnk hmk ξ Ω hΩ

/-- The first `r` nonconstant Taylor terms. -/
def vinogradovCenteredTaylorTruncation (r : ℕ) (ξ : ℤ)
    (φ : Polynomial ℤ) : Polynomial ℤ :=
  ∑ i : Fin r,
    Polynomial.C ((vinogradovCenteredTaylor ξ φ).coeff (i.val + 1)) *
      Polynomial.X ^ (i.val + 1)

theorem coeff_vinogradovCenteredTaylorTruncation_of_pos_le
    (r d : ℕ) (ξ : ℤ) (φ : Polynomial ℤ)
    (hd0 : 0 < d) (hdr : d ≤ r) :
    (vinogradovCenteredTaylorTruncation r ξ φ).coeff d =
      (vinogradovCenteredTaylor ξ φ).coeff d := by
  let j : Fin r := ⟨d - 1, by omega⟩
  rw [vinogradovCenteredTaylorTruncation, Polynomial.finset_sum_coeff,
    Finset.sum_eq_single j]
  · simp [j, Nat.sub_add_cancel hd0]
  · intro i _ hij
    have hne : d ≠ i.val + 1 := by
      intro hi
      apply hij
      apply Fin.ext
      dsimp only [j]
      omega
    simp [hne]
  · simp

@[simp] theorem coeff_zero_vinogradovCenteredTaylorTruncation
    (r : ℕ) (ξ : ℤ) (φ : Polynomial ℤ) :
    (vinogradovCenteredTaylorTruncation r ξ φ).coeff 0 = 0 := by
  simp [vinogradovCenteredTaylorTruncation]

/-- Removing the first `r` nonconstant Taylor terms leaves a polynomial
divisible by `X^(r+1)`. -/
theorem exists_vinogradovCenteredTaylor_eq_truncation_add_tail
    (r : ℕ) (ξ : ℤ) (φ : Polynomial ℤ) :
    ∃ θ : Polynomial ℤ,
      vinogradovCenteredTaylor ξ φ =
        vinogradovCenteredTaylorTruncation r ξ φ +
          Polynomial.X ^ (r + 1) * θ := by
  have hdiv : Polynomial.X ^ (r + 1) ∣
      vinogradovCenteredTaylor ξ φ -
        vinogradovCenteredTaylorTruncation r ξ φ := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub]
    by_cases hd0 : d = 0
    · subst d
      simp
    · have hpos : 0 < d := Nat.pos_of_ne_zero hd0
      have hdr : d ≤ r := by omega
      rw [coeff_vinogradovCenteredTaylorTruncation_of_pos_le
        r d ξ φ hpos hdr, sub_self]
  obtain ⟨θ, hθ⟩ := hdiv
  refine ⟨θ, ?_⟩
  rw [sub_eq_iff_eq_add] at hθ
  simpa only [add_comm] using hθ

/-- Wooley's translated spaced-polynomial expansion: the first `r`
nonconstant terms have the prescribed center powers and a coefficient matrix
congruent to the binomial matrix, while all remaining terms enter through an
`X^(r+1)` tail. -/
theorem exists_vinogradovCenteredTaylor_spaced_expansion
    (p c k n r : ℕ) (hrn : r ≤ n) (hnk : n ≤ k)
    (ψ : Polynomial ℤ) (ξ : ℤ) :
    ∃ Ω : Fin r → ℤ, ∃ θ : Polynomial ℤ,
      (∀ i, Ω i ≡ (n.choose (i.val + 1) : ℤ)
        [ZMOD (p : ℤ) ^ c]) ∧
      vinogradovCenteredTaylor ξ
          (vinogradovSpacedPolynomial p c k n ψ) =
        (∑ i : Fin r,
          Polynomial.C (ξ ^ (n - (i.val + 1)) * Ω i) *
            Polynomial.X ^ (i.val + 1)) +
          Polynomial.X ^ (r + 1) * θ := by
  choose Ω hΩ using fun i : Fin r ↦
    exists_vinogradovCenteredTaylor_spaced_coeff_factor
      p c k n (i.val + 1) hnk (by omega) (by omega) ψ ξ
  obtain ⟨θ, hθ⟩ :=
    exists_vinogradovCenteredTaylor_eq_truncation_add_tail r ξ
      (vinogradovSpacedPolynomial p c k n ψ)
  refine ⟨Ω, θ, fun i ↦ (hΩ i).2, ?_⟩
  rw [hθ]
  congr 2
  unfold vinogradovCenteredTaylorTruncation
  apply Finset.sum_congr rfl
  intro i _
  rw [(hΩ i).1]

/-- The same translated expansion without requiring every retained degree to
lie below the monomial degree. Natural subtraction records the zero-exponent
case, while the associated binomial coefficient is then zero modulo the
spacing modulus. -/
theorem exists_vinogradovCenteredTaylor_spaced_expansion_all
    (p c k n r : ℕ) (hnk : n ≤ k)
    (ψ : Polynomial ℤ) (ξ : ℤ) :
    ∃ Ω : Fin r → ℤ, ∃ θ : Polynomial ℤ,
      (∀ i, Ω i ≡ (n.choose (i.val + 1) : ℤ)
        [ZMOD (p : ℤ) ^ c]) ∧
      vinogradovCenteredTaylor ξ
          (vinogradovSpacedPolynomial p c k n ψ) =
        (∑ i : Fin r,
          Polynomial.C (ξ ^ (n - (i.val + 1)) * Ω i) *
            Polynomial.X ^ (i.val + 1)) +
          Polynomial.X ^ (r + 1) * θ := by
  choose Ω hΩ using fun i : Fin r ↦
    exists_vinogradovCenteredTaylor_spaced_coeff_factor_all
      p c k n (i.val + 1) hnk (by omega) ψ ξ
  obtain ⟨θ, hθ⟩ :=
    exists_vinogradovCenteredTaylor_eq_truncation_add_tail r ξ
      (vinogradovSpacedPolynomial p c k n ψ)
  refine ⟨Ω, θ, fun i ↦ (hΩ i).2, ?_⟩
  rw [hθ]
  congr 2
  unfold vinogradovCenteredTaylorTruncation
  apply Finset.sum_congr rfl
  intro i _
  rw [(hΩ i).1]

/-- The row-wise translated high-degree spaced system from Wooley's equation
(7.10), packaged with its perturbed binomial coefficient matrix and common
`X^(r+1)` tails. -/
theorem exists_vinogradovTranslatedSpacedSystemExpansion
    (p c k r : ℕ) (hc : 0 < c) (hrk : r ≤ k)
    (ψ : Fin r → Polynomial ℤ) (ξ : ℤ) :
    ∃ Ω : Matrix (Fin r) (Fin r) ℤ, ∃ θ : Fin r → Polynomial ℤ,
      IsVinogradovBinomialCoefficientMatrix p k r Ω ∧
      ∀ i,
        vinogradovCenteredTaylor ξ
            (vinogradovSpacedPolynomial p c k
              (vinogradovBinomialPoint k r i) (ψ i)) =
          (∑ j : Fin r,
            Polynomial.C
                (ξ ^ (vinogradovBinomialPoint k r i - (j.val + 1)) *
                  Ω i j) * Polynomial.X ^ (j.val + 1)) +
            Polynomial.X ^ (r + 1) * θ i := by
  have hpoint (i : Fin r) : vinogradovBinomialPoint k r i ≤ k := by
    simp only [vinogradovBinomialPoint]
    omega
  choose Ω θ hΩ hexp using fun i : Fin r ↦
    exists_vinogradovCenteredTaylor_spaced_expansion_all
      p c k (vinogradovBinomialPoint k r i) r (hpoint i) (ψ i) ξ
  refine ⟨Matrix.of fun i j ↦ Ω i j, θ, ?_, ?_⟩
  · intro i j
    have hij := (hΩ i j).of_dvd
      (show (p : ℤ) ∣ (p : ℤ) ^ c by
        exact dvd_pow_self _ hc.ne')
    simpa only [Matrix.of_apply] using hij
  · intro i
    simpa only [Matrix.of_apply] using hexp i

end

end ZeroFreeRegion.VinogradovKorobov
