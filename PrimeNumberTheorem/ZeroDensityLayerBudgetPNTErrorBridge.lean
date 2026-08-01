import PrimeNumberTheorem.ZeroDensityLayerBudgetFiniteZeroSumBridge

/-!
# Pintz--Carlson transfer to the actual PNT error

A fixed-height certificate records exactly the truncated contour formula
available at that height.  The finite nontrivial-zero contribution is then
replaced by the proved Pintz--Carlson aggregate, while every remaining term
stays explicit.
-/

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem

/-- The `chebyshevPsi0` error normalized by its sample scale. -/
noncomputable def relativeChebyshevPsi0Error (x : ℝ) : ℝ :=
  (chebyshevPsi0 x - x) / x

/--
A fixed-height truncated explicit-formula certificate.

The structure does not assert that every height admits such a certificate;
good-height existence is supplied by a separate adapter.
-/
structure TruncatedPNTErrorCertificate (x T : ℝ) : Type where
  trivialContribution : ℂ
  remainderBound : ℝ
  remainder_nonneg : 0 ≤ remainderBound
  formula_bound :
    ‖trivialContribution +
        ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
          ∑ rho ∈ nontrivialZerosFinset T,
            pntFiniteZeroContribution x rho) -
        (chebyshevPsi0 x : ℂ)‖ ≤
      remainderBound

/-- A fixed-height contour certificate bounds the actual unnormalized PNT
error by the finite zero sum and the three explicit residual terms. -/
theorem TruncatedPNTErrorCertificate.abs_chebyshevPsi0_sub_id_le
    {x T : ℝ} (certificate : TruncatedPNTErrorCertificate x T) :
    |chebyshevPsi0 x - x| ≤
      ‖finiteNontrivialZeroSumWithMultiplicity x T‖ +
        ‖deriv riemannZeta 0 / riemannZeta 0‖ +
        ‖certificate.trivialContribution‖ +
        certificate.remainderBound := by
  let formulaError : ℂ :=
    certificate.trivialContribution +
      ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
        ∑ rho ∈ nontrivialZerosFinset T,
          pntFiniteZeroContribution x rho) -
      (chebyshevPsi0 x : ℂ)
  have hsum :=
    sum_pntFiniteZeroContribution_eq_neg_finiteNontrivialZeroSumWithMultiplicity
      x T
  have hidentity :
      (((chebyshevPsi0 x - x : ℝ) : ℂ)) =
        -formulaError + certificate.trivialContribution -
          deriv riemannZeta 0 / riemannZeta 0 -
          finiteNontrivialZeroSumWithMultiplicity x T := by
    dsimp [formulaError]
    rw [hsum]
    push_cast
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hidentity]
  calc
    ‖-formulaError + certificate.trivialContribution -
        deriv riemannZeta 0 / riemannZeta 0 -
        finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
      ‖-formulaError + certificate.trivialContribution -
          deriv riemannZeta 0 / riemannZeta 0‖ +
        ‖finiteNontrivialZeroSumWithMultiplicity x T‖ :=
      norm_sub_le _ _
    _ ≤
      (‖-formulaError + certificate.trivialContribution‖ +
          ‖deriv riemannZeta 0 / riemannZeta 0‖) +
        ‖finiteNontrivialZeroSumWithMultiplicity x T‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤
      ((‖-formulaError‖ + ‖certificate.trivialContribution‖) +
          ‖deriv riemannZeta 0 / riemannZeta 0‖) +
        ‖finiteNontrivialZeroSumWithMultiplicity x T‖ := by
      gcongr
      exact norm_add_le _ _
    _ =
      ‖formulaError‖ + ‖certificate.trivialContribution‖ +
        ‖deriv riemannZeta 0 / riemannZeta 0‖ +
        ‖finiteNontrivialZeroSumWithMultiplicity x T‖ := by
      rw [norm_neg]
    _ ≤
      certificate.remainderBound + ‖certificate.trivialContribution‖ +
        ‖deriv riemannZeta 0 / riemannZeta 0‖ +
        ‖finiteNontrivialZeroSumWithMultiplicity x T‖ := by
      gcongr
      exact certificate.formula_bound
    _ =
      ‖finiteNontrivialZeroSumWithMultiplicity x T‖ +
        ‖deriv riemannZeta 0 / riemannZeta 0‖ +
        ‖certificate.trivialContribution‖ +
        certificate.remainderBound := by
      ring

/-- Inject the automatic Pintz--Carlson finite-zero estimate into the actual
unnormalized PNT error. -/
theorem TruncatedPNTErrorCertificate.abs_chebyshevPsi0_sub_id_le_pintz
    {x T : ℝ} {n : ℕ}
    (certificate : TruncatedPNTErrorCertificate x T)
    (input : PositiveZeroBucketInput T n)
    (hx : 1 ≤ x) :
    |chebyshevPsi0 x - x| ≤
      x *
          (2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
              (Finset.univ : Finset (Fin n)) input.sigma () x T +
            ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
              pntRelativeZeroContribution x rho‖) +
        ‖deriv riemannZeta 0 / riemannZeta 0‖ +
        ‖certificate.trivialContribution‖ +
        certificate.remainderBound := by
  calc
    |chebyshevPsi0 x - x| ≤
        ‖finiteNontrivialZeroSumWithMultiplicity x T‖ +
          ‖deriv riemannZeta 0 / riemannZeta 0‖ +
          ‖certificate.trivialContribution‖ +
          certificate.remainderBound :=
      certificate.abs_chebyshevPsi0_sub_id_le
    _ ≤
        x *
            (2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
                (Finset.univ : Finset (Fin n)) input.sigma () x T +
              ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
                pntRelativeZeroContribution x rho‖) +
          ‖deriv riemannZeta 0 / riemannZeta 0‖ +
          ‖certificate.trivialContribution‖ +
          certificate.remainderBound := by
      gcongr
      exact input.norm_finiteNontrivialZeroSumWithMultiplicity_le_pintz hx

/-- Normalized actual PNT error bound at a certified height. -/
theorem TruncatedPNTErrorCertificate.abs_relativeChebyshevPsi0Error_le_pintz
    {x T : ℝ} {n : ℕ}
    (certificate : TruncatedPNTErrorCertificate x T)
    (input : PositiveZeroBucketInput T n)
    (hx : 1 ≤ x) :
    |relativeChebyshevPsi0Error x| ≤
      2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
          (Finset.univ : Finset (Fin n)) input.sigma () x T +
        ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
          pntRelativeZeroContribution x rho‖ +
        (‖deriv riemannZeta 0 / riemannZeta 0‖ +
            ‖certificate.trivialContribution‖ +
            certificate.remainderBound) / x := by
  have hxpos : 0 < x :=
    lt_of_lt_of_le zero_lt_one hx
  have hbound :=
    certificate.abs_chebyshevPsi0_sub_id_le_pintz input hx
  rw [relativeChebyshevPsi0Error, abs_div, abs_of_pos hxpos]
  apply (div_le_iff₀ hxpos).2
  calc
    |chebyshevPsi0 x - x| ≤
        x *
            (2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
                (Finset.univ : Finset (Fin n)) input.sigma () x T +
              ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
                pntRelativeZeroContribution x rho‖) +
          ‖deriv riemannZeta 0 / riemannZeta 0‖ +
          ‖certificate.trivialContribution‖ +
          certificate.remainderBound :=
      hbound
    _ =
        (2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
              (Finset.univ : Finset (Fin n)) input.sigma () x T +
            ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
              pntRelativeZeroContribution x rho‖ +
            (‖deriv riemannZeta 0 / riemannZeta 0‖ +
                ‖certificate.trivialContribution‖ +
                certificate.remainderBound) / x) * x := by
      field_simp [hxpos.ne']
      ring

end PrimeNumberTheorem
