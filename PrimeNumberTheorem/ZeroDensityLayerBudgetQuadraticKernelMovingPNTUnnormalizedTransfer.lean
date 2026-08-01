import PrimeNumberTheorem.ZeroDensityLayerBudgetQuadraticKernelMovingPNTTransfer

/-!
# Unnormalized quadratic-kernel moving PNT transfer

Multiplying the reciprocal-height relative target amplitude by the sample
point restores the exact unnormalized scale `x^(beta x - alpha)`, namely
`x^(beta x) / x^alpha`.  This module transfers both signs and packages the
result with the quadratic-kernel certificate from the preceding stack.
-/

namespace PrimeNumberTheorem

open Filter

noncomputable section

/-- Multiplication by the sample point restores the exact moving
reciprocal-height unnormalized exponent. -/
theorem self_mul_reciprocalPolynomialHeightVariableTargetAmplitude
    {beta : ℝ → ℝ} {alpha x : ℝ} (hx : 0 < x) :
    x * reciprocalPolynomialHeightVariableTargetAmplitude beta alpha x =
      x ^ (beta x - alpha) := by
  unfold reciprocalPolynomialHeightVariableTargetAmplitude
  calc
    x * (variableBoundaryTargetAmplitude beta x / x ^ alpha) =
        (x * variableBoundaryTargetAmplitude beta x) / x ^ alpha := by ring
    _ = x ^ beta x / x ^ alpha := by
      rw [self_mul_variableBoundaryTargetAmplitude hx]
    _ = x ^ (beta x - alpha) := by
      rw [Real.rpow_sub hx]

/-- Positive relative reciprocal-height witnesses transfer to the
unnormalized centered Chebyshev error. -/
theorem
    HasFarPositiveTargetAmplitudeWitness.relativeChebyshevPsi0Error_to_unnormalized_reciprocalPolynomialHeight
    {beta : ℝ → ℝ} {alpha q : ℝ}
    (hwitness :
      HasFarPositiveTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x =>
          q * reciprocalPolynomialHeightVariableTargetAmplitude
            beta alpha x)) :
    HasFarPositiveTargetAmplitudeWitness chebyshevPsi0Error
      (fun x => q * x ^ (beta x - alpha)) := by
  intro X
  rcases hwitness (max X 1) with ⟨x, hxMax, hxWitness⟩
  have hxOne : 1 ≤ x := (le_max_right X 1).trans hxMax
  have hxPos : 0 < x := zero_lt_one.trans_le hxOne
  have hscaled := mul_le_mul_of_nonneg_left hxWitness hxPos.le
  refine ⟨x, (le_max_left X 1).trans hxMax, ?_⟩
  calc
    q * x ^ (beta x - alpha) =
        x *
          (q * reciprocalPolynomialHeightVariableTargetAmplitude
            beta alpha x) := by
      rw [← self_mul_reciprocalPolynomialHeightVariableTargetAmplitude hxPos]
      ring
    _ ≤ x * relativeChebyshevPsi0Error x := hscaled
    _ = chebyshevPsi0Error x :=
      (chebyshevPsi0Error_eq_self_mul_relative hxPos.ne').symm

/-- Negative relative reciprocal-height witnesses transfer to the
unnormalized centered Chebyshev error. -/
theorem
    HasFarNegativeTargetAmplitudeWitness.relativeChebyshevPsi0Error_to_unnormalized_reciprocalPolynomialHeight
    {beta : ℝ → ℝ} {alpha q : ℝ}
    (hwitness :
      HasFarNegativeTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x =>
          q * reciprocalPolynomialHeightVariableTargetAmplitude
            beta alpha x)) :
    HasFarNegativeTargetAmplitudeWitness chebyshevPsi0Error
      (fun x => q * x ^ (beta x - alpha)) := by
  intro X
  rcases hwitness (max X 1) with ⟨x, hxMax, hxWitness⟩
  have hxOne : 1 ≤ x := (le_max_right X 1).trans hxMax
  have hxPos : 0 < x := zero_lt_one.trans_le hxOne
  have hscaled := mul_le_mul_of_nonneg_left hxWitness hxPos.le
  refine ⟨x, (le_max_left X 1).trans hxMax, ?_⟩
  calc
    chebyshevPsi0Error x = x * relativeChebyshevPsi0Error x :=
      chebyshevPsi0Error_eq_self_mul_relative hxPos.ne'
    _ ≤ x *
        (-(q * reciprocalPolynomialHeightVariableTargetAmplitude
          beta alpha x)) := hscaled
    _ = -(q * x ^ (beta x - alpha)) := by
      rw [← self_mul_reciprocalPolynomialHeightVariableTargetAmplitude hxPos]
      ring

/-- A quadratic-kernel certificate and one unsigned moving-main witness force
one sign of the actual unnormalized PNT error at the exact
`x^(beta(x)-alpha)` reciprocal-height scale. -/
theorem QuadraticKernelMovingPNTCertificate.unnormalizedSignAlternative
    {beta0 alpha c loss : ℝ} {beta : ℝ → ℝ} {main : ℕ → ℝ}
    (certificate :
      QuadraticKernelMovingPNTCertificate beta0 alpha beta main)
    (hmargin : 1 - beta0 < alpha)
    (hbeta : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hloss : 0 < loss) (hlossC : loss < c)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness main
        (fun m : ℕ =>
          c * reciprocalPolynomialHeightVariableTargetAmplitude
            beta alpha (m : ℝ))) :
    0 < c - loss ∧
      (HasFarPositiveTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ => (c - loss) * x ^ (beta x - alpha)) ∨
        HasFarNegativeTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ => (c - loss) * x ^ (beta x - alpha))) := by
  rcases certificate.relativeSignAlternative
      hmargin hbeta hloss hlossC hmain with
    ⟨hcoefficient, hsign⟩
  refine ⟨hcoefficient, ?_⟩
  rcases hsign with hpos | hneg
  · exact Or.inl
      hpos.toReal.relativeChebyshevPsi0Error_to_unnormalized_reciprocalPolynomialHeight
  · exact Or.inr
      hneg.toReal.relativeChebyshevPsi0Error_to_unnormalized_reciprocalPolynomialHeight

end
end PrimeNumberTheorem
