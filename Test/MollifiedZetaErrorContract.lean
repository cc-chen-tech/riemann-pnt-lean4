import PrimeNumberTheorem.MollifiedZetaError

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example (X : ℕ) (s : ℂ) :
    mollifiedZetaError X s = riemannZeta s * mobiusMollifier X s - 1 :=
  rfl

example :
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
                2 * ‖R * mobiusMollifier X s‖ ^ 2 :=
  exists_mollifiedZetaError_decomposition

#print axioms exists_mollifiedZetaError_decomposition

end CarlsonZeroDensity
end PrimeNumberTheorem
