import PrimeNumberTheorem.MWKFCubicReciprocalAmplitude
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Basic

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

open PrimeNumberTheorem.MWKFCubic

-- General joint derivative: separate partial derivatives alone are not
-- enough to justify the chain rule without joint differentiability.
#check hasDerivAt_coupledReciprocalAmplitude
#check normalized_coupledReciprocalAmplitude_derivative

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ × ℝ → E} {D : (ℝ × ℝ) →L[ℝ] E} {W : ℝ → ℝ}
    {W' lam x : ℝ} (hx : x ≠ 0) (hW : HasDerivAt W W' x)
    (hΦ : HasFDerivAt Φ D (x, lam / x)) :
    x • deriv (fun y ↦ W y • Φ (y, lam / y)) x =
      (x * W') • Φ (x, lam / x) +
        W x • (x • D (1, 0) - (lam / x) • D (0, 1)) := by
  exact normalized_coupledReciprocalAmplitude_derivative hx hW hΦ

-- Φ(x, ξ) = x + ξ is not a single separated product. At x=2, λ=4,
-- its derivative on the reciprocal curve is 0, not the -1 obtained
-- by omitting the first-coordinate contribution.
example : HasDerivAt (fun y : ℝ ↦ (1 : ℝ) • (y + 4 / y)) 0 2 := by
  have hΦ : HasFDerivAt (fun p : ℝ × ℝ ↦ p.1 + p.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ) + (ContinuousLinearMap.snd ℝ ℝ ℝ))
      (2, (4 : ℝ) / 2) := hasFDerivAt_fst.add hasFDerivAt_snd
  convert! hasDerivAt_coupledReciprocalAmplitude
    (lam := 4) (x := 2) (by norm_num) (hasDerivAt_const (2 : ℝ) (1 : ℝ)) hΦ using 1
  norm_num
