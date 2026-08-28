import PrimeNumberTheorem.MWKFCubicReciprocalAmplitude

namespace PrimeNumberTheorem.MWKFCubic

#check (@hasDerivAt_reciprocalAmplitude :
  ∀ {F G : ℝ → ℝ} {F' G' lam x : ℝ},
    x ≠ 0 → HasDerivAt F F' x → HasDerivAt G G' (lam / x) →
      HasDerivAt (fun y ↦ F y * G (lam / y))
        (F' * G (lam / x) - F x * G' * (lam / x ^ 2)) x)

#check (@normalized_reciprocalAmplitude_derivative :
  ∀ {F G : ℝ → ℝ} {F' G' lam x : ℝ},
    x ≠ 0 → HasDerivAt F F' x → HasDerivAt G G' (lam / x) →
      x * deriv (fun y ↦ F y * G (lam / y)) x =
        x * F' * G (lam / x) - F x * (lam / x) * G')

end PrimeNumberTheorem.MWKFCubic
