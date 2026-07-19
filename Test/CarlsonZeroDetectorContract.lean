import PrimeNumberTheorem.CarlsonZeroDetector

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example (X : ℕ) (s : ℂ) :
    carlsonZeroDetector X s = 1 - mollifiedZetaError X s ^ 2 :=
  rfl

example (X : ℕ) (s : ℂ) :
    carlsonZeroDetector X s =
      (riemannZeta s * mobiusMollifier X s) *
        (2 - riemannZeta s * mobiusMollifier X s) :=
  carlsonZeroDetector_eq_zeta_mul_mollifier_factorization X s

example {X : ℕ} {s : ℂ} (hs : riemannZeta s = 0) :
    carlsonZeroDetector X s = 0 :=
  carlsonZeroDetector_eq_zero_of_riemannZeta_eq_zero hs

example {X : ℕ} {rho : ℂ} (hX : 1 ≤ X)
    (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    analyticOrderNatAt riemannZeta rho ≤
      analyticOrderNatAt (carlsonZeroDetector X) rho :=
  analyticOrderNatAt_riemannZeta_le_carlsonZeroDetector hX hrho

example (X : ℕ) (s : ℂ) :
    Real.log ‖carlsonZeroDetector X s‖ ≤
      ‖mollifiedZetaError X s‖ ^ 2 :=
  log_norm_carlsonZeroDetector_le_norm_mollifiedZetaError_sq X s

example (X : ℕ) (sigma : ℝ) (hsigma1 : sigma ≠ 1) :
    Continuous (fun t : ℝ =>
      mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)) :=
  continuous_mollifiedZetaError_verticalLine X sigma hsigma1

example (X : ℕ) (sigma : ℝ) (hsigma1 : sigma ≠ 1) :
    Continuous (fun t : ℝ =>
      carlsonZeroDetector X ((sigma : ℂ) + Complex.I * t)) :=
  continuous_carlsonZeroDetector_verticalLine X sigma hsigma1

example {X : ℕ} {sigma a b : ℝ} (hab : a ≤ b)
    (hsigma1 : sigma ≠ 1)
    (hboundary : ∀ t ∈ Set.Icc a b,
      carlsonZeroDetector X ((sigma : ℂ) + Complex.I * t) ≠ 0) :
    ∫ t in a..b,
        Real.log ‖carlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖ ≤
      ∫ t in a..b,
        ‖mollifiedZetaError X
          ((sigma : ℂ) + Complex.I * t)‖ ^ 2 :=
  integral_log_norm_carlsonZeroDetector_le_meanSquare
    hab hsigma1 hboundary

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (sigma a b x : ℝ),
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b, |t| ≤ x / 2 ∧ x ≤ 2 * |t|) →
      (∀ t ∈ Set.Icc a b,
        carlsonZeroDetector X ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in a..b,
            Real.log ‖carlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          2 * (((b - a) + 4 * Real.pi) *
            (2 * ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
                (1 - 2 * sigma) *
              ((((Nat.floor x) * X : ℕ) : ℝ) *
                (1 + Real.log (Nat.floor x * X)) ^ 3))) +
          2 * ((C * x ^ (-sigma)) ^ 2 *
            (((b - a) + 4 * Real.pi) *
              (2 * (1 +
                ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                  (2 - 2 * sigma))))) :=
  exists_integral_log_norm_carlsonZeroDetector_le_endpoint

#print axioms carlsonZeroDetector_eq_zeta_mul_mollifier_factorization
#print axioms carlsonZeroDetector_eq_zero_of_riemannZeta_eq_zero
#print axioms analyticOrderNatAt_riemannZeta_le_carlsonZeroDetector
#print axioms log_norm_carlsonZeroDetector_le_norm_mollifiedZetaError_sq
#print axioms continuous_mollifiedZetaError_verticalLine
#print axioms continuous_carlsonZeroDetector_verticalLine
#print axioms integral_log_norm_carlsonZeroDetector_le_meanSquare
#print axioms exists_integral_log_norm_carlsonZeroDetector_le_endpoint

end CarlsonZeroDensity
end PrimeNumberTheorem
