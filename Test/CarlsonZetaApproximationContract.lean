import PrimeNumberTheorem.CarlsonZetaApproximation

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

noncomputable example (s : ℂ) (x : ℝ) : ℂ :=
  carlsonZetaRemainder s x

example (s : ℂ) (x : ℝ) :
    riemannZeta s =
      (∑ n ∈ Finset.Icc 1 (Nat.floor x), 1 / (n : ℂ) ^ s) +
        carlsonZetaRemainder s x :=
  riemannZeta_eq_truncated_add_carlsonZetaRemainder s x

example (x sigma : ℝ) (hsigma1 : sigma ≠ 1) :
    Continuous (fun t : ℝ =>
      carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x) :=
  continuous_carlsonZetaRemainder_verticalLine x sigma hsigma1

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℂ) (x : ℝ),
      (1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 → s ≠ 1 → 2 ≤ x →
        |s.im| ≤ x / 2 → x ≤ 2 * |s.im| →
          ∃ R : ℂ,
            riemannZeta s =
              (∑ n ∈ Finset.Icc 1 (Nat.floor x), 1 / (n : ℂ) ^ s) + R ∧
            ‖R‖ ≤ C * x ^ (-s.re) :=
  exists_riemannZeta_carlson_approximation

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℂ) (x : ℝ),
      (1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 → s ≠ 1 → 2 ≤ x →
        |s.im| ≤ x / 2 → x ≤ 2 * |s.im| →
          ‖carlsonZetaRemainder s x‖ ≤ C * x ^ (-s.re) :=
  exists_norm_carlsonZetaRemainder_le

#print axioms exists_riemannZeta_carlson_approximation
#print axioms riemannZeta_eq_truncated_add_carlsonZetaRemainder
#print axioms continuous_carlsonZetaRemainder_verticalLine
#print axioms exists_norm_carlsonZetaRemainder_le

end CarlsonZeroDensity
end PrimeNumberTheorem
