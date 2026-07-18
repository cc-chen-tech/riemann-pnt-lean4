import PrimeNumberTheorem.CarlsonZetaApproximation
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

end CarlsonZeroDensity
end PrimeNumberTheorem
