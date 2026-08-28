import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# Reciprocal-amplitude derivative

The cubic route evaluates a separated physical amplitude on the reciprocal
curve `(x, λ/x)`.  The normalized derivative is the restriction of
`x∂x - ξ∂ξ`; the minus sign and the normalized second coordinate are
recorded exactly here.
-/

/-- Ordinary derivative of a separated amplitude restricted to the
reciprocal curve. -/
theorem hasDerivAt_reciprocalAmplitude
    {F G : ℝ → ℝ} {F' G' lam x : ℝ}
    (hx : x ≠ 0) (hF : HasDerivAt F F' x)
    (hG : HasDerivAt G G' (lam / x)) :
    HasDerivAt (fun y ↦ F y * G (lam / y))
      (F' * G (lam / x) - F x * G' * (lam / x ^ 2)) x := by
  have hrecip : HasDerivAt (fun y : ℝ ↦ lam / y) (-lam / x ^ 2) x := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv hx).const_mul lam
  have hcomp : HasDerivAt (fun y ↦ G (lam / y)) (G' * (-lam / x ^ 2)) x :=
    hG.comp x hrecip
  exact (hF.mul hcomp).congr_deriv (by ring)

/-- Multiplying the preceding derivative by `x` yields exactly the physical
operator `x∂x - ξ∂ξ` at `ξ = λ/x`. -/
theorem normalized_reciprocalAmplitude_derivative
    {F G : ℝ → ℝ} {F' G' lam x : ℝ}
    (hx : x ≠ 0) (hF : HasDerivAt F F' x)
    (hG : HasDerivAt G G' (lam / x)) :
    x * deriv (fun y ↦ F y * G (lam / y)) x =
      x * F' * G (lam / x) - F x * (lam / x) * G' := by
  rw [(hasDerivAt_reciprocalAmplitude hx hF hG).deriv]
  field_simp

end MWKFCubic
end PrimeNumberTheorem
