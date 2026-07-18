import PrimeNumberTheorem.CarlsonZetaApproximation

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℂ) (x : ℝ),
      (1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 → s ≠ 1 → 2 ≤ x →
        |s.im| ≤ x / 2 → x ≤ 2 * |s.im| →
          ∃ R : ℂ,
            riemannZeta s =
              (∑ n ∈ Finset.Icc 1 (Nat.floor x), 1 / (n : ℂ) ^ s) + R ∧
            ‖R‖ ≤ C * x ^ (-s.re) :=
  exists_riemannZeta_carlson_approximation

#print axioms exists_riemannZeta_carlson_approximation

end CarlsonZeroDensity
end PrimeNumberTheorem
