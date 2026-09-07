import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# Reciprocal-amplitude derivative

The first two lemmas apply only to separated amplitudes. The final two
handle a general jointly differentiable kernel on the reciprocal curve
`(x, λ/x)`, with values in any real normed space (including complex values).
Both coordinate derivatives are retained. These are local chain rules,
not uniform physical-kernel seminorm or Fourier-tail estimates.
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

/-- The normalized reciprocal-curve derivative for a separated amplitude.
For a general two-coordinate kernel use the coupled theorem below. -/
theorem normalized_reciprocalAmplitude_derivative
    {F G : ℝ → ℝ} {F' G' lam x : ℝ}
    (hx : x ≠ 0) (hF : HasDerivAt F F' x)
    (hG : HasDerivAt G G' (lam / x)) :
    x * deriv (fun y ↦ F y * G (lam / y)) x =
      x * F' * G (lam / x) - F x * (lam / x) * G' := by
  rw [(hasDerivAt_reciprocalAmplitude hx hF hG).deriv]
  field_simp

/-- Chain rule for a genuinely coupled kernel and a real physical weight.
Joint Frechet differentiability is required: existence of partial
derivatives alone would not justify this conclusion. The two partial
derivatives are D(1,0) and D(0,1), respectively. -/
theorem hasDerivAt_coupledReciprocalAmplitude
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ × ℝ → E} {D : (ℝ × ℝ) →L[ℝ] E} {W : ℝ → ℝ}
    {W' lam x : ℝ} (hx : x ≠ 0) (hW : HasDerivAt W W' x)
    (hΦ : HasFDerivAt Φ D (x, lam / x)) :
    HasDerivAt (fun y ↦ W y • Φ (y, lam / y))
      (W' • Φ (x, lam / x) + W x • (D (1, 0) - (lam / x ^ 2) • D (0, 1))) x := by
  have hrecip : HasDerivAt (fun y : ℝ ↦ lam / y) (-lam / x ^ 2) x := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv hx).const_mul lam
  have hc := hΦ.comp_hasDerivAt x ((hasDerivAt_id x).prodMk hrecip)
  have hv : ((1 : ℝ), -lam / x ^ 2) = (1, 0) - (lam / x ^ 2) • ((0 : ℝ), 1) := by
    ext <;> simp [neg_div]
  rw [hv, map_sub, map_smul] at hc
  simpa only [Function.comp_def, Pi.smul_def', id_eq, add_comm] using hW.smul hc

/-- General normalized operator, including both partial derivatives and
the derivative of the physical weight. No separation of Φ is assumed. -/
theorem normalized_coupledReciprocalAmplitude_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ × ℝ → E} {D : (ℝ × ℝ) →L[ℝ] E} {W : ℝ → ℝ}
    {W' lam x : ℝ} (hx : x ≠ 0) (hW : HasDerivAt W W' x)
    (hΦ : HasFDerivAt Φ D (x, lam / x)) :
    x • deriv (fun y ↦ W y • Φ (y, lam / y)) x =
      (x * W') • Φ (x, lam / x) +
        W x • (x • D (1, 0) - (lam / x) • D (0, 1)) := by
  have hscale : x * (W x * (lam / x ^ 2)) = W x * (lam / x) := by
    field_simp
  rw [(hasDerivAt_coupledReciprocalAmplitude hx hW hΦ).deriv]
  simp only [smul_add, smul_sub, smul_smul]
  rw [hscale, mul_comm x (W x)]

end MWKFCubic
end PrimeNumberTheorem
