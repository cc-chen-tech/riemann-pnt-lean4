import HardyTheorem.SelbergSqrtZetaSignedFullTaper
import HardyTheorem.SelbergSqrtZetaSignedRationalReducedRayEnergy

/-!
# Complete and boundary pieces of one reduced Selberg ray

The signed bilinear scale sum on a coprime ray has two structurally different
parts.  On the complete denominator range, arithmetic convolution turns the
two copies of the linear taper into one negative and one positive taper.  All
failure of that identity is confined to the explicit boundary-scale support.

This file records the exact decomposition before any absolute values or
Cauchy estimates are applied.
-/

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-- The complete-range contribution on one coprime ray after recombining the
four logarithmic terms into the two visible taper factors. -/
noncomputable def selbergSqrtZetaSignedReducedRayCompleteTerm
    (N X a b : ℕ) : ℝ :=
  ∑ d ∈ selbergSqrtZetaSignedCoprimeRayCompleteScaleSupport N X a b,
    (d : ℝ)⁻¹ *
      (selbergSqrtZetaCoeff (a * d) *
        (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          selbergSqrtZetaCoeff) (b * d))) *
      (1 - Real.log (a * d) / Real.log X) *
      (1 + Real.log (b * d) / Real.log X)

/-- The exact truncation defect on one coprime ray.  Its support is the
explicit harmonic boundary tail. -/
noncomputable def selbergSqrtZetaSignedReducedRayBoundaryTerm
    (N X a b : ℕ) : ℝ :=
  ∑ d ∈ selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
    (d : ℝ)⁻¹ * selbergSqrtZetaTaperedCoeff X (a * d) *
      ∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X (b * d),
        selbergSqrtZetaTaperedCoeff X p.2

/-- Exact complete-range/boundary decomposition of the signed bilinear scale
sum on a positive coprime ray. -/
theorem
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_eq_complete_add_boundary
    (N X a b : ℕ) (hb : 0 < b) :
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
        (selbergSqrtZetaTaperedCoeff X)
        (selbergSqrtZetaTaperedCoeff X) =
      selbergSqrtZetaSignedReducedRayCompleteTerm N X a b +
        selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b := by
  have h :=
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_eq_complete_zeta_add_boundary
      N X a b (selbergSqrtZetaFullTapered X)
        (selbergSqrtZetaFullTapered X) hb
  rw [selbergSqrtZetaSignedCoprimeRayComplete_fullTaper_eq_twoFactors] at h
  unfold selbergSqrtZetaSignedCoprimeRayBilinearScaleSum at h ⊢
  simpa only [selbergSqrtZetaSignedReducedRayCompleteTerm,
    selbergSqrtZetaSignedReducedRayBoundaryTerm,
    selbergSqrtZetaFullTapered_apply,
    selbergSqrtZetaTaperedCoeff,
    selbergMoebiusWeight] using h

/-- The reduced local-separation energy written directly as the square of its
complete main term plus its boundary truncation defect. -/
theorem normSq_div_localFrequencySeparation_le_reducedRayCompleteBoundaryWeight
    {N X a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hQ : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial)
    (hq : (a : ℚ) / (b : ℚ) ∈
      selbergSqrtZetaSignedRationalSupport N X) :
    Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff N X
            ((a : ℚ) / (b : ℚ))) /
        PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
          (selbergSqrtZetaSignedRationalSupport N X)
          selbergSqrtZetaSignedRationalFrequency
          ((a : ℚ) / (b : ℚ)) ≤
      ((X * min (a * N) b + 1 : ℕ) : ℝ) *
        (((a * b : ℕ) : ℝ)⁻¹ *
          (selbergSqrtZetaSignedReducedRayCompleteTerm N X a b +
            selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b) ^ 2) := by
  have h :=
    normSq_div_localFrequencySeparation_le_reducedRayBilinearWeight
      ha hb hab hQ hq
  rw [
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_eq_complete_add_boundary
      N X a b hb] at h
  exact h

end HardyTheorem
