import PrimeNumberTheorem.ZeroDensityLayerBudgetKernelOrderReciprocalHeightCriterion
import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryAmplitudeDomination

/-!
# Quadratic-kernel certificate for a moving PNT lower transfer

This module records the exact certificate a smoothed order-two explicit
formula must provide.  A quadratic polynomial-height remainder bound is
automatically negligible at the reciprocal-height target zero scale.  A
fixed anchor exponent then transfers to every eventually larger moving
boundary exponent, and one unsigned main-term witness forces one persistent
sign of the genuine relative PNT error.

The analytic construction of such a smoothed zeta kernel remains external.
-/

namespace PrimeNumberTheorem

open Filter Topology

noncomputable section

/-- Fixed-exponent target amplitude after paying one reciprocal polynomial
height factor. -/
noncomputable def reciprocalPolynomialHeightTargetAmplitude
    (beta alpha x : ℝ) : ℝ :=
  targetZeroPowerAmplitude beta x / x ^ alpha

/-- Moving-exponent version of the reciprocal polynomial-height target
amplitude. -/
noncomputable def reciprocalPolynomialHeightVariableTargetAmplitude
    (beta : ℝ → ℝ) (alpha x : ℝ) : ℝ :=
  variableBoundaryTargetAmplitude beta x / x ^ alpha

/-- The natural-point order-two power-log remainder majorant. -/
noncomputable def quadraticKernelNaturalRemainderMajorant
    (C alpha : ℝ) (m : ℕ) : ℝ :=
  C * (m : ℝ) ^ (-(2 * alpha)) *
    (1 + Real.log (m : ℝ)) ^ 2

/-- The quadratic power-log majorant is negligible relative to the fixed
reciprocal-height target amplitude under the usual contour margin. -/
theorem quadraticKernelNaturalRemainderMajorant_reciprocalHeightNegligible
    {C beta alpha : ℝ}
    (hC : 0 ≤ C) (hmargin : 1 - beta < alpha) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ =>
        reciprocalPolynomialHeightTargetAmplitude
          beta alpha (m : ℝ))
      (quadraticKernelNaturalRemainderMajorant C alpha) := by
  have hratio :=
    (tendsto_quadraticKernelReciprocalHeightRemainderRatio_zero
      hC hmargin).comp tendsto_natCast_atTop_atTop
  unfold NaturalPointTargetAmplitudeNegligible
  apply hratio.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hxPos : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hmajorant :
      0 ≤ quadraticKernelNaturalRemainderMajorant C alpha m := by
    unfold quadraticKernelNaturalRemainderMajorant
    exact mul_nonneg
      (mul_nonneg hC (Real.rpow_nonneg hxPos.le _)) (sq_nonneg _)
  rw [abs_of_nonneg hmajorant]
  rfl

/-- The reciprocal-height target amplitude is eventually positive at natural
points. -/
theorem eventually_reciprocalPolynomialHeightVariableTargetAmplitude_pos
    (beta : ℝ → ℝ) (alpha : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      0 < reciprocalPolynomialHeightVariableTargetAmplitude
        beta alpha (m : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hxPos : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  unfold reciprocalPolynomialHeightVariableTargetAmplitude
    variableBoundaryTargetAmplitude targetZeroPowerAmplitude
  exact div_pos (Real.rpow_pos_of_pos hxPos _)
    (Real.rpow_pos_of_pos hxPos _)

/-- Enlarging the moving exponent enlarges the reciprocal-height amplitude;
the polynomial-height denominator is unchanged. -/
theorem reciprocalPolynomialHeightTargetAmplitude_le_variable
    {beta0 alpha : ℝ} {beta : ℝ → ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hbeta : beta0 ≤ beta (m : ℝ)) :
    reciprocalPolynomialHeightTargetAmplitude beta0 alpha (m : ℝ) ≤
      reciprocalPolynomialHeightVariableTargetAmplitude
        beta alpha (m : ℝ) := by
  have hxPos : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  unfold reciprocalPolynomialHeightTargetAmplitude
    reciprocalPolynomialHeightVariableTargetAmplitude
  exact div_le_div_of_nonneg_right
    (targetZeroPowerAmplitude_le_variableBoundaryTargetAmplitude hm hbeta)
    (Real.rpow_nonneg hxPos.le _)

/-- A quadratic fixed-anchor remainder is negligible at every eventually
larger moving reciprocal-height amplitude. -/
theorem
    naturalPointReciprocalHeightNegligible_variableBoundary_of_quadraticMajorant
    {C beta0 alpha : ℝ} {beta : ℝ → ℝ} {remainder : ℕ → ℝ}
    (hC : 0 ≤ C)
    (hmargin : 1 - beta0 < alpha)
    (hbeta : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hbound :
      ∀ᶠ m : ℕ in atTop,
        |remainder m| ≤ quadraticKernelNaturalRemainderMajorant C alpha m) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ =>
        reciprocalPolynomialHeightVariableTargetAmplitude
          beta alpha (m : ℝ))
      remainder := by
  have hfixed :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ =>
          reciprocalPolynomialHeightTargetAmplitude
            beta0 alpha (m : ℝ))
        (quadraticKernelNaturalRemainderMajorant C alpha) :=
    quadraticKernelNaturalRemainderMajorant_reciprocalHeightNegligible
      hC hmargin
  have hfixedPos :
      ∀ᶠ m : ℕ in atTop,
        0 < reciprocalPolynomialHeightTargetAmplitude
          beta0 alpha (m : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hxPos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    unfold reciprocalPolynomialHeightTargetAmplitude
      targetZeroPowerAmplitude
    exact div_pos (Real.rpow_pos_of_pos hxPos _)
      (Real.rpow_pos_of_pos hxPos _)
  have hmajorantTransfer :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ =>
          reciprocalPolynomialHeightVariableTargetAmplitude
            beta alpha (m : ℝ))
        (quadraticKernelNaturalRemainderMajorant C alpha) := by
    apply hfixed.mono_amplitude
    · exact hfixedPos
    · exact eventually_reciprocalPolynomialHeightVariableTargetAmplitude_pos
        beta alpha
    · filter_upwards [hbeta, eventually_ge_atTop (1 : ℕ)] with m hbetaM hm
      exact reciprocalPolynomialHeightTargetAmplitude_le_variable hm hbetaM
  exact NaturalPointTargetAmplitudeNegligible.of_eventually_abs_le
    (eventually_reciprocalPolynomialHeightVariableTargetAmplitude_pos
      beta alpha)
    hmajorantTransfer hbound

/-- Exact order-two smoothed-kernel obligation for a proposed moving main
term of the actual relative PNT error. -/
structure QuadraticKernelMovingPNTCertificate
    (beta0 alpha : ℝ) (beta : ℝ → ℝ) (main : ℕ → ℝ) where
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  residual_bound :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ) - main m| ≤
        quadraticKernelNaturalRemainderMajorant constant alpha m

/-- The certificate produces residual negligibility at the exact moving
reciprocal-height scale. -/
theorem QuadraticKernelMovingPNTCertificate.residual_negligible
    {beta0 alpha : ℝ} {beta : ℝ → ℝ} {main : ℕ → ℝ}
    (certificate :
      QuadraticKernelMovingPNTCertificate beta0 alpha beta main)
    (hmargin : 1 - beta0 < alpha)
    (hbeta : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ)) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ =>
        reciprocalPolynomialHeightVariableTargetAmplitude
          beta alpha (m : ℝ))
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ) - main m) :=
  naturalPointReciprocalHeightNegligible_variableBoundary_of_quadraticMajorant
    certificate.constant_nonneg hmargin hbeta certificate.residual_bound

/-- One unsigned smoothed moving-main witness and the quadratic-kernel
certificate force one persistent sign of the genuine relative PNT error at
the reciprocal-height target scale. -/
theorem QuadraticKernelMovingPNTCertificate.relativeSignAlternative
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
      (HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          (fun m : ℕ =>
            (c - loss) *
              reciprocalPolynomialHeightVariableTargetAmplitude
                beta alpha (m : ℝ)) ∨
        HasFarNaturalPointNegativeTargetAmplitudeWitness
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          (fun m : ℕ =>
            (c - loss) *
              reciprocalPolynomialHeightVariableTargetAmplitude
                beta alpha (m : ℝ))) := by
  have hresidual := certificate.residual_negligible hmargin hbeta
  have hamplitude :=
    eventually_reciprocalPolynomialHeightVariableTargetAmplitude_pos
      beta alpha
  have hsmall :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ) - main m| <
          loss * reciprocalPolynomialHeightVariableTargetAmplitude
            beta alpha (m : ℝ) :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      hamplitude hresidual hloss
  refine ⟨sub_pos.mpr hlossC, ?_⟩
  rcases hmain.signAlternative with hpos | hneg
  · exact Or.inl (hpos.transfer_eventually_sub_lt hsmall)
  · exact Or.inr (hneg.transfer_eventually_sub_lt hsmall)

end
end PrimeNumberTheorem
