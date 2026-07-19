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

/-- Every positive-degree coefficient of a translated `p^c`-spaced
polynomial agrees modulo `p^c` with the corresponding translated monomial
coefficient. -/
theorem coeff_vinogradovCenteredTaylor_spaced_modEq
    (p c k n m : ℕ) (hm : 0 < m) (ψ : Polynomial ℤ) (ξ : ℤ) :
    (vinogradovCenteredTaylor ξ
      (vinogradovSpacedPolynomial p c k n ψ)).coeff m ≡
      ξ ^ (n - m) * (n.choose m : ℤ) [ZMOD (p : ℤ) ^ c] := by
  let correction : Polynomial ℤ := Polynomial.X ^ (k + 1) * ψ
  have hcoeff :
      (vinogradovCenteredTaylor ξ
        (vinogradovSpacedPolynomial p c k n ψ)).coeff m =
        ((Polynomial.X + Polynomial.C ξ) ^ n).coeff m +
          (p : ℤ) ^ c * (Polynomial.taylor ξ correction).coeff m := by
    rw [vinogradovCenteredTaylor, Polynomial.coeff_sub,
      Polynomial.coeff_C_ne_zero hm.ne', sub_zero]
    simp only [vinogradovSpacedPolynomial, map_add,
      Polynomial.taylor_X_pow, Polynomial.taylor_mul,
      Polynomial.taylor_C, Polynomial.coeff_add,
      correction]
    rw [mul_assoc, Polynomial.coeff_C_mul]
  rw [hcoeff, Polynomial.coeff_X_add_C_pow]
  have hcorrection :
      (p : ℤ) ^ c * (Polynomial.taylor ξ correction).coeff m ≡ 0
        [ZMOD (p : ℤ) ^ c] := by
    rw [Int.modEq_zero_iff_dvd]
    exact dvd_mul_right _ _
  simpa only [add_zero] using
    (Int.ModEq.refl (ξ ^ (n - m) * (n.choose m : ℤ))).add hcorrection

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

end

end ZeroFreeRegion.VinogradovKorobov
