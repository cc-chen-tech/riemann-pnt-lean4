import PrimeNumberTheorem.CarlsonZetaApproximation
import PrimeNumberTheorem.CarlsonMollifierCoefficients
import PrimeNumberTheorem.MobiusMollifier

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The finite zeta Dirichlet polynomial at real cutoff `x`. -/
noncomputable def truncatedZetaPolynomial (x : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x), 1 / (n : ℂ) ^ s

/-- Carlson's mollified zeta error. -/
noncomputable def mollifiedZetaError (X : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s * mobiusMollifier X s - 1

/-- The finite product in the mollified zeta approximation is exactly the
coefficient polynomial obtained from the truncated Dirichlet convolution. -/
theorem truncatedZetaPolynomial_mul_mobiusMollifier
    (X : ℕ) (x : ℝ) (s : ℂ) :
    truncatedZetaPolynomial x s * mobiusMollifier X s =
      mollifiedTruncatedPolynomial X (Nat.floor x) s := by
  unfold truncatedZetaPolynomial mobiusMollifier
  exact truncatedZeta_sum_mul_mobius_sum_eq_mollifiedTruncatedPolynomial
    X (Nat.floor x) s

/-- The Carlson-ready zeta approximation decomposes the mollified error into
a finite Dirichlet-polynomial product and a controlled remainder times the
mollifier.  The final inequality is the pointwise input for the second-moment
argument. -/
theorem exists_mollifiedZetaError_decomposition :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (s : ℂ) (x : ℝ),
      (1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 → s ≠ 1 → 2 ≤ x →
        |s.im| ≤ x / 2 → x ≤ 2 * |s.im| →
          ∃ R : ℂ,
            ‖R‖ ≤ C * x ^ (-s.re) ∧
            mollifiedZetaError X s =
              (truncatedZetaPolynomial x s * mobiusMollifier X s - 1) +
                R * mobiusMollifier X s ∧
            ‖mollifiedZetaError X s‖ ^ 2 ≤
              2 * ‖truncatedZetaPolynomial x s * mobiusMollifier X s - 1‖ ^ 2 +
                2 * ‖R * mobiusMollifier X s‖ ^ 2 := by
  obtain ⟨C, hC, happrox⟩ := exists_riemannZeta_carlson_approximation
  refine ⟨C, hC, ?_⟩
  intro X s x hs_lower hs_upper hs1 hx him_upper him_lower
  rcases happrox s x hs_lower hs_upper hs1 hx him_upper him_lower with
    ⟨R, hR_eq, hR_bound⟩
  refine ⟨R, hR_bound, ?_, ?_⟩
  · unfold mollifiedZetaError truncatedZetaPolynomial
    rw [hR_eq]
    ring
  · let A : ℂ :=
      truncatedZetaPolynomial x s * mobiusMollifier X s - 1
    let B : ℂ := R * mobiusMollifier X s
    have hdecomp : mollifiedZetaError X s = A + B := by
      dsimp [A, B]
      unfold mollifiedZetaError truncatedZetaPolynomial
      rw [hR_eq]
      ring
    rw [hdecomp]
    have htri : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le A B
    have hA : 0 ≤ ‖A‖ := norm_nonneg A
    have hB : 0 ≤ ‖B‖ := norm_nonneg B
    have hAB : 0 ≤ ‖A + B‖ := norm_nonneg (A + B)
    dsimp [A, B]
    nlinarith [sq_nonneg (‖A‖ - ‖B‖)]

/-- Carlson's pointwise decomposition with the finite product already
collected into its Dirichlet-convolution coefficients.  This is the form in
which Möbius cancellation can be fed into the eventual second-moment bound. -/
theorem exists_mollifiedZetaError_coefficient_decomposition :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (s : ℂ) (x : ℝ),
      (1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 → s ≠ 1 → 2 ≤ x →
        |s.im| ≤ x / 2 → x ≤ 2 * |s.im| →
          ∃ R : ℂ,
            ‖R‖ ≤ C * x ^ (-s.re) ∧
            mollifiedZetaError X s =
              (mollifiedTruncatedPolynomial X (Nat.floor x) s - 1) +
                R * mobiusMollifier X s ∧
            ‖mollifiedZetaError X s‖ ^ 2 ≤
              2 * ‖mollifiedTruncatedPolynomial X (Nat.floor x) s - 1‖ ^ 2 +
                2 * ‖R * mobiusMollifier X s‖ ^ 2 := by
  obtain ⟨C, hC, hdecomp⟩ := exists_mollifiedZetaError_decomposition
  refine ⟨C, hC, ?_⟩
  intro X s x hs_lower hs_upper hs1 hx him_upper him_lower
  rcases hdecomp X s x hs_lower hs_upper hs1 hx him_upper him_lower with
    ⟨R, hR, hEq, hnorm⟩
  rw [truncatedZetaPolynomial_mul_mobiusMollifier X x s] at hEq hnorm
  exact ⟨R, hR, hEq, hnorm⟩

/-- Once the mollifier cutoff is positive, exact Möbius inversion removes all
coefficients through `min X ⌊x⌋`.  This tail form isolates the finite
Dirichlet polynomial whose mean square remains to be estimated in Carlson's
argument. -/
theorem exists_mollifiedZetaError_tail_decomposition :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (s : ℂ) (x : ℝ),
      0 < X → (1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 → s ≠ 1 → 2 ≤ x →
        |s.im| ≤ x / 2 → x ≤ 2 * |s.im| →
          ∃ R : ℂ,
            ‖R‖ ≤ C * x ^ (-s.re) ∧
            mollifiedZetaError X s =
                (∑ n ∈ Finset.Icc (min X (Nat.floor x) + 1)
                    (Nat.floor x * X),
                  mollifiedTruncatedCoefficient X (Nat.floor x) n /
                    (n : ℂ) ^ s) + R * mobiusMollifier X s ∧
              ‖mollifiedZetaError X s‖ ^ 2 ≤
                2 * ‖∑ n ∈ Finset.Icc (min X (Nat.floor x) + 1)
                    (Nat.floor x * X),
                  mollifiedTruncatedCoefficient X (Nat.floor x) n /
                    (n : ℂ) ^ s‖ ^ 2 +
                  2 * ‖R * mobiusMollifier X s‖ ^ 2 := by
  obtain ⟨C, hC, hdecomp⟩ := exists_mollifiedZetaError_coefficient_decomposition
  refine ⟨C, hC, ?_⟩
  intro X s x hX hs_lower hs_upper hs1 hx him_upper him_lower
  rcases hdecomp X s x hs_lower hs_upper hs1 hx him_upper him_lower with
    ⟨R, hR, hEq, hnorm⟩
  have hfloor : 0 < Nat.floor x := Nat.floor_pos.mpr (by linarith)
  have htail := mollifiedTruncatedPolynomial_sub_one_eq_tail hX hfloor s
  rw [htail] at hEq hnorm
  exact ⟨R, hR, hEq, hnorm⟩

end CarlsonZeroDensity
end PrimeNumberTheorem
