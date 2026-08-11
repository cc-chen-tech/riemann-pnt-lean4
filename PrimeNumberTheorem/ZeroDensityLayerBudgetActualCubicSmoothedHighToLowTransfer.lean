import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCarlsonDiagonalTail

/-!
# Actual cubic Carlson high-to-low smoothed strip transfer

This module turns the genuine reciprocal-cubic, analytic-multiplicity-square
Carlson capacity into an exact dyadic high-to-low decomposition. At a natural
scale `m`, the finite energy through an outer cut is the energy through a lower
cut plus the intervening blocks. The intervening finite energy is bounded by
the actual diagonal `tsum` from the lower cut, so the quantitative Carlson
tail from the preceding module makes it negligible after normalization by
`m ^ (-2 * beta)`.

The final theorem uses one joint parameter package at both `gammaLow` and
`gammaHigh`, while keeping `alpha` as the distinct outer contour exponent.
This is the actual-zeta zero-energy side required by a third-order smoothed
explicit formula. It does not claim that the repository already contains
that third-order Perron or contour formula.
-/

namespace PrimeNumberTheorem

open Filter Topology
open scoped BigOperators

noncomputable def actualCubicSmoothedStripEnergyUpTo
    (sigma tau gamma : ℝ) (S : Finset ℂ) (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (actualCubicDyadicPolynomialCut gamma m + 1),
    actualCubicDyadicStripSquareCapacityExcluding (m : ℝ) sigma tau n S

noncomputable def actualCubicSmoothedStripEnergyBetween
    (sigma tau gammaFrom gammaTo : ℝ) (S : Finset ℂ) (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico
      (actualCubicDyadicPolynomialCut gammaFrom m + 1)
      (actualCubicDyadicPolynomialCut gammaTo m + 1),
    actualCubicDyadicStripSquareCapacityExcluding (m : ℝ) sigma tau n S

noncomputable def actualCubicNormalizedSmoothedStripEnergyUpTo
    (beta sigma tau gamma : ℝ) (S : Finset ℂ) (m : ℕ) : ℝ :=
  (m : ℝ) ^ (-2 * beta) *
    actualCubicSmoothedStripEnergyUpTo sigma tau gamma S m

noncomputable def actualCubicNormalizedSmoothedStripEnergyBetween
    (beta sigma tau gammaFrom gammaTo : ℝ) (S : Finset ℂ) (m : ℕ) : ℝ :=
  (m : ℝ) ^ (-2 * beta) *
    actualCubicSmoothedStripEnergyBetween sigma tau gammaFrom gammaTo S m

theorem actualCubicDyadicStripSquareCapacityExcluding_nonneg
    (x sigma tau : ℝ) (hx : 0 ≤ x) (n : ℕ) (S : Finset ℂ) :
    0 ≤ actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S := by
  unfold actualCubicDyadicStripSquareCapacityExcluding
  apply Finset.sum_nonneg
  intro rho hrho
  exact mul_nonneg
    (div_nonneg (sq_nonneg _) (sq_nonneg _))
    (div_nonneg (Real.rpow_nonneg hx _) (by positivity))

theorem actualCubicSmoothedStripEnergyUpTo_nonneg
    (sigma tau gamma : ℝ) (S : Finset ℂ) (m : ℕ) :
    0 ≤ actualCubicSmoothedStripEnergyUpTo sigma tau gamma S m := by
  unfold actualCubicSmoothedStripEnergyUpTo
  apply Finset.sum_nonneg
  intro n hn
  exact actualCubicDyadicStripSquareCapacityExcluding_nonneg _ _ _ (Nat.cast_nonneg m) _ _

theorem actualCubicSmoothedStripEnergyBetween_nonneg
    (sigma tau gammaFrom gammaTo : ℝ) (S : Finset ℂ) (m : ℕ) :
    0 ≤ actualCubicSmoothedStripEnergyBetween
      sigma tau gammaFrom gammaTo S m := by
  unfold actualCubicSmoothedStripEnergyBetween
  apply Finset.sum_nonneg
  intro n hn
  exact actualCubicDyadicStripSquareCapacityExcluding_nonneg _ _ _ (Nat.cast_nonneg m) _ _

theorem actualCubicNormalizedSmoothedStripEnergyBetween_nonneg
    (beta sigma tau gammaFrom gammaTo : ℝ) (S : Finset ℂ) (m : ℕ) :
    0 ≤ actualCubicNormalizedSmoothedStripEnergyBetween
      beta sigma tau gammaFrom gammaTo S m := by
  unfold actualCubicNormalizedSmoothedStripEnergyBetween
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _)
    (actualCubicSmoothedStripEnergyBetween_nonneg _ _ _ _ _ _)

theorem actualCubicSmoothedStripEnergyUpTo_eq_add_between
    {sigma tau gammaFrom gammaTo : ℝ} {S : Finset ℂ} {m : ℕ}
    (hcut : actualCubicDyadicPolynomialCut gammaFrom m ≤
      actualCubicDyadicPolynomialCut gammaTo m) :
    actualCubicSmoothedStripEnergyUpTo sigma tau gammaTo S m =
      actualCubicSmoothedStripEnergyUpTo sigma tau gammaFrom S m +
        actualCubicSmoothedStripEnergyBetween
          sigma tau gammaFrom gammaTo S m := by
  unfold actualCubicSmoothedStripEnergyUpTo
    actualCubicSmoothedStripEnergyBetween
  exact (Finset.sum_range_add_sum_Ico _ (Nat.succ_le_succ hcut)).symm

theorem actualCubicNormalizedSmoothedStripEnergyUpTo_eq_add_between
    {beta sigma tau gammaFrom gammaTo : ℝ} {S : Finset ℂ} {m : ℕ}
    (hcut : actualCubicDyadicPolynomialCut gammaFrom m ≤
      actualCubicDyadicPolynomialCut gammaTo m) :
    actualCubicNormalizedSmoothedStripEnergyUpTo
        beta sigma tau gammaTo S m =
      actualCubicNormalizedSmoothedStripEnergyUpTo
          beta sigma tau gammaFrom S m +
        actualCubicNormalizedSmoothedStripEnergyBetween
          beta sigma tau gammaFrom gammaTo S m := by
  unfold actualCubicNormalizedSmoothedStripEnergyUpTo
    actualCubicNormalizedSmoothedStripEnergyBetween
  rw [actualCubicSmoothedStripEnergyUpTo_eq_add_between hcut]
  ring

theorem CarlsonEventualMajorant.actualCubicSmoothedStripEnergyBetween_le_diagonalTail
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {tau gammaFrom gammaTo : ℝ} {S : Finset ℂ} {m : ℕ}
    (hm : 1 ≤ m) :
    actualCubicSmoothedStripEnergyBetween
        sigma tau gammaFrom gammaTo S m ≤
      actualCubicCarlsonDiagonalTail sigma tau gammaFrom S m := by
  let cut := actualCubicDyadicPolynomialCut gammaFrom m
  let f : ℕ → ℝ := fun n =>
    actualCubicDyadicStripSquareCapacityExcluding (m : ℝ) sigma tau n S
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsum : Summable f := by
    exact certificate.summable_actualCubicDyadicStripSquareCapacityExcluding
      hmReal S
  have hshift : Summable (fun n => f (n + (cut + 1))) :=
    (summable_nat_add_iff (cut + 1)).2 hsum
  have hfinite := hshift.sum_le_tsum
    (Finset.range
      (actualCubicDyadicPolynomialCut gammaTo m + 1 - (cut + 1)))
    (fun n hn => by
      exact actualCubicDyadicStripSquareCapacityExcluding_nonneg _ _ _ (Nat.cast_nonneg m) _ _)
  unfold actualCubicSmoothedStripEnergyBetween
    actualCubicCarlsonDiagonalTail
  rw [Finset.sum_Ico_eq_sum_range]
  simpa [cut, f, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hfinite

theorem CarlsonEventualMajorant.actualCubicNormalizedSmoothedStripEnergyBetween_le_diagonalTail
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {beta tau gammaFrom gammaTo : ℝ} {S : Finset ℂ} {m : ℕ}
    (hm : 1 ≤ m) :
    actualCubicNormalizedSmoothedStripEnergyBetween
        beta sigma tau gammaFrom gammaTo S m ≤
      actualCubicCarlsonNormalizedDiagonalTail
        beta sigma tau gammaFrom S m := by
  unfold actualCubicNormalizedSmoothedStripEnergyBetween
    actualCubicCarlsonNormalizedDiagonalTail
  exact mul_le_mul_of_nonneg_left
    (certificate.actualCubicSmoothedStripEnergyBetween_le_diagonalTail hm)
    (Real.rpow_nonneg (Nat.cast_nonneg m) _)

theorem CarlsonEventualMajorant.tendsto_actualCubicNormalizedSmoothedStripEnergyBetween_zero_of_tail
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {beta tau gammaFrom gammaTo : ℝ} (S : Finset ℂ)
    (htail : Tendsto
      (actualCubicCarlsonNormalizedDiagonalTail
        beta sigma tau gammaFrom S) atTop (nhds 0)) :
    Tendsto
      (actualCubicNormalizedSmoothedStripEnergyBetween
        beta sigma tau gammaFrom gammaTo S) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds htail
  · exact Filter.Eventually.of_forall fun m =>
      actualCubicNormalizedSmoothedStripEnergyBetween_nonneg
        beta sigma tau gammaFrom gammaTo S m
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact certificate.actualCubicNormalizedSmoothedStripEnergyBetween_le_diagonalTail hm

theorem CarlsonEventualMajorant.actualCubicSmoothedHighToLowTransfer_of_tail
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {beta tau gammaFrom gammaTo : ℝ}
    (hgamma : gammaFrom ≤ gammaTo) (S : Finset ℂ)
    (htail : Tendsto
      (actualCubicCarlsonNormalizedDiagonalTail
        beta sigma tau gammaFrom S) atTop (nhds 0)) :
    (∀ᶠ m : ℕ in atTop,
      actualCubicNormalizedSmoothedStripEnergyUpTo
          beta sigma tau gammaTo S m =
        actualCubicNormalizedSmoothedStripEnergyUpTo
            beta sigma tau gammaFrom S m +
          actualCubicNormalizedSmoothedStripEnergyBetween
            beta sigma tau gammaFrom gammaTo S m) ∧
      Tendsto
        (actualCubicNormalizedSmoothedStripEnergyBetween
          beta sigma tau gammaFrom gammaTo S) atTop (nhds 0) := by
  constructor
  · have hcuts := eventually_actualCubicLowDyadicCut_le_outer hgamma
    simpa [actualCubicLowDyadicCut, actualCubicOuterDyadicCut] using
      hcuts.mono (fun m hm =>
        actualCubicNormalizedSmoothedStripEnergyUpTo_eq_add_between hm)
  · exact
      certificate.tendsto_actualCubicNormalizedSmoothedStripEnergyBetween_zero_of_tail
        S htail

theorem exists_jointTwoHeightParameters_with_actualCubicSmoothedHighToLowTransfers
    {beta : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    ∃ sigma tau alpha gammaLow gammaHigh : ℝ,
      1 / 2 < sigma ∧ sigma < tau ∧ tau < beta ∧
      0 < gammaLow ∧ gammaLow ≤ alpha ∧
      0 < gammaHigh ∧ gammaHigh < alpha ∧ 0 < alpha ∧
      ∀ (certificate : CarlsonEventualMajorant sigma) (S : Finset ℂ),
        ((∀ᶠ m : ℕ in atTop,
          actualCubicNormalizedSmoothedStripEnergyUpTo
              beta sigma tau alpha S m =
            actualCubicNormalizedSmoothedStripEnergyUpTo
                beta sigma tau gammaLow S m +
              actualCubicNormalizedSmoothedStripEnergyBetween
                beta sigma tau gammaLow alpha S m) ∧
          Tendsto
            (actualCubicNormalizedSmoothedStripEnergyBetween
              beta sigma tau gammaLow alpha S) atTop (nhds 0)) ∧
        ((∀ᶠ m : ℕ in atTop,
          actualCubicNormalizedSmoothedStripEnergyUpTo
              beta sigma tau alpha S m =
            actualCubicNormalizedSmoothedStripEnergyUpTo
                beta sigma tau gammaHigh S m +
              actualCubicNormalizedSmoothedStripEnergyBetween
                beta sigma tau gammaHigh alpha S m) ∧
          Tendsto
            (actualCubicNormalizedSmoothedStripEnergyBetween
              beta sigma tau gammaHigh alpha S) atTop (nhds 0)) := by
  obtain ⟨sigma, tau, alpha, gammaLow, gammaHigh,
      hsigma, hsigmaTau, htauBeta,
      hgammaLow, hgammaLowAlpha,
      hgammaHigh, hgammaHighAlpha, halpha, hall⟩ :=
    exists_jointTwoHeightParameters_with_actualCubicCarlsonDiagonalTails
      hbeta hbetaOne
  refine ⟨sigma, tau, alpha, gammaLow, gammaHigh,
    hsigma, hsigmaTau, htauBeta,
    hgammaLow, hgammaLowAlpha,
    hgammaHigh, hgammaHighAlpha, halpha, ?_⟩
  intro certificate S
  obtain ⟨hlowTail, hhighTail, _halphaTail⟩ := hall certificate S
  exact ⟨
    certificate.actualCubicSmoothedHighToLowTransfer_of_tail
      hgammaLowAlpha S hlowTail,
    certificate.actualCubicSmoothedHighToLowTransfer_of_tail
      hgammaHighAlpha.le S hhighTail⟩

end PrimeNumberTheorem
