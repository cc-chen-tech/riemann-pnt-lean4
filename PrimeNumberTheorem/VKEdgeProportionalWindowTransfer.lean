import PrimeNumberTheorem.VKEdgeInitialFullMovingEnergy

open Complex Filter MeasureTheory Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Proportional-window transfer to the full moving complement

For a zero with real part `beta > 1 / 2`, a sufficiently small fixed
proportional window still admits a uniformly small finite-height
explicit-formula approximation.  This module combines that fact with the
true empty-cluster residual lower bound and the canonical full-bucket
identity.

The result is a uniform positive Gaussian energy lower bound for every
finite-height complementary zero, with no omitted or duplicated zero inside
the chosen height.
-/

/-- The fixed-window full-moving transfer remains valid on the proportional
window `[a, (1 + ε) * a]` when the normalization gain dominates its growth
loss.  The Gaussian variance is the square of the window length. -/
theorem
    eventually_exists_goodHeight_normalizedRemainder_to_fullMovingGaussianEnergy_proportional
    {S : Finset ℂ} {beta ε eta : ℝ}
    (hbeta : 1 / 2 < beta)
    (hbeta1 : beta < 1)
    (hε : 0 < ε)
    (hdecay : (1 - beta) * ε < beta - 1 / 2)
    (heta : 0 < eta) :
    ∀ᶠ a : ℝ in atTop,
      ∃ T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1),
        ExplicitFormulaAux.goodHeight T ∧
          (1 / 3 : ℝ) *
                normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
                  S T beta a ((ε * a) ^ 2) (ε * a) -
              (eta ^ 2 +
                (Real.exp (-beta * a) *
                  zeroPackageClosedTermsUniformBound) ^ 2) ≤
            dynamicComplementForwardMovingGaussianSecondMoment
              S T beta a (dynamicComplementFullBucketSet S T)
                ((ε * a) ^ 2) (ε * a) := by
  have hselect :=
    ExplicitFormulaResidues.eventually_exists_uniform_goodHeight_normalized_proportional_window_remainder_lt
      hbeta hbeta1 hε hdecay heta
  have haOne : ∀ᶠ a : ℝ in atTop, 1 ≤ a := eventually_ge_atTop 1
  filter_upwards [hselect, haOne] with a hselectA ha
  rcases hselectA with ⟨T, hTmem, hgood, hpoint⟩
  refine ⟨T, hTmem, hgood, ?_⟩
  apply
    dynamicComplementFullMovingGaussianSecondMoment_ge_of_normalizedRemainder
      (sq_pos_of_pos (mul_pos hε (zero_lt_one.trans_le ha)))
      (by linarith) ha heta.le
  · intro y hy
    rw [normalizedFiniteZeroClusterApproximationError, norm_mul]
    have hscalar :
        ‖((Real.exp (-beta * y) : ℝ) : ℂ)‖ =
          Real.exp (-beta * y) := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    rw [hscalar]
    have hy' : y ∈ Set.Icc a ((1 + ε) * a) := by
      constructor
      · exact hy.1
      · convert hy.2 using 1 <;> ring
    exact (hpoint y hy').le
  · exact le_rfl

/-- The positive fraction of the true initial residual energy that remains
after paying approximation and closed-term budgets. -/
def initialEmptyClusterFullMovingGaussianL2Constant
    (ε : ℝ) (rho : ℂ) (k : ℕ) : ℝ :=
  initialEmptyClusterResidualGaussianL2Constant ε rho k / 6

private theorem tendsto_exp_neg_mul_initialFullEnergy
    {beta : ℝ} (hbeta : 0 < beta) :
    Tendsto (fun a : ℝ => Real.exp (-beta * a))
      atTop (nhds 0) := by
  have hlinear : Tendsto (fun a : ℝ => beta * a) atTop atTop := by
    simpa [mul_comm] using tendsto_id.atTop_mul_const hbeta
  simpa only [neg_mul] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear

/-- One off-critical-line zero forces a uniform positive Gaussian energy in
the canonical full moving complementary-zero packet on every sufficiently
late admissible proportional logarithmic window.

The selected height contains every complementary zero represented by the
canonical bucket set.  This is an energy lower bound, not yet an iteration
producing distinct new zero layers. -/
theorem
    exists_eventually_emptyClusterFullMovingGaussianSecondMoment_gt
    {ε : ℝ} {rho : ℂ} {sigma : ℝ}
    (hε : 0 < ε)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hσ : 1 / 2 < sigma)
    (hσrho : sigma < rho.re)
    (hrhoRe1 : rho.re < 1)
    (hdecay : (1 - rho.re) * ε < rho.re - 1 / 2) :
    ∃ k : ℕ,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      0 < initialEmptyClusterFullMovingGaussianL2Constant ε rho k ∧
      ∀ᶠ Y : ℝ in atTop,
        ∃ T ∈
            Set.Icc
              (Real.exp (Real.log Y / 2))
              (Real.exp (Real.log Y / 2) + 1),
          ExplicitFormulaAux.goodHeight T ∧
            initialEmptyClusterFullMovingGaussianL2Constant ε rho k <
              dynamicComplementForwardMovingGaussianSecondMoment
                ∅ T rho.re (Real.log Y)
                  (dynamicComplementFullBucketSet ∅ T)
                  ((ε * Real.log Y) ^ 2) (ε * Real.log Y) := by
  rcases
      exists_eventually_emptyClusterResidualForwardGaussianSecondMoment_gt
        hε hgamma hzero hσ hσrho hrhoRe1 with
    ⟨k, hmissing, hRpos, hresidual⟩
  let R : ℝ := initialEmptyClusterResidualGaussianL2Constant ε rho k
  let eta : ℝ := min 1 (R / 12)
  have hR : 0 < R := by
    dsimp [R]
    exact hRpos
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min zero_lt_one (div_pos hR (by norm_num))
  have hetaSq : eta ^ 2 ≤ R / 12 := by
    have hetaOne : eta ≤ 1 := min_le_left _ _
    have hetaR : eta ≤ R / 12 := min_le_right _ _
    nlinarith [heta.le]
  have hbeta : 1 / 2 < rho.re := hσ.trans hσrho
  have htransferA :=
    eventually_exists_goodHeight_normalizedRemainder_to_fullMovingGaussianEnergy_proportional
      (S := (∅ : Finset ℂ)) hbeta hrhoRe1 hε hdecay heta
  have htransferY :
      ∀ᶠ Y : ℝ in atTop,
        ∃ T ∈
            Set.Icc
              (Real.exp (Real.log Y / 2))
              (Real.exp (Real.log Y / 2) + 1),
          ExplicitFormulaAux.goodHeight T ∧
            (1 / 3 : ℝ) *
                  normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
                    ∅ T rho.re (Real.log Y)
                      ((ε * Real.log Y) ^ 2) (ε * Real.log Y) -
                (eta ^ 2 +
                  (Real.exp (-rho.re * Real.log Y) *
                    zeroPackageClosedTermsUniformBound) ^ 2) ≤
              dynamicComplementForwardMovingGaussianSecondMoment
                ∅ T rho.re (Real.log Y)
                  (dynamicComplementFullBucketSet ∅ T)
                  ((ε * Real.log Y) ^ 2) (ε * Real.log Y) :=
    Real.tendsto_log_atTop.eventually htransferA
  have hclosed0 :
      Tendsto
        (fun a : ℝ =>
          (Real.exp (-rho.re * a) *
            zeroPackageClosedTermsUniformBound) ^ 2)
        atTop (nhds 0) := by
    have hexp :=
      tendsto_exp_neg_mul_initialFullEnergy (show 0 < rho.re by linarith)
    have hmul :
        Tendsto
          (fun a : ℝ =>
            Real.exp (-rho.re * a) *
              zeroPackageClosedTermsUniformBound)
          atTop (nhds 0) := by
      simpa [mul_comm] using
        hexp.const_mul zeroPackageClosedTermsUniformBound
    simpa using hmul.pow 2
  have hclosedA :
      ∀ᶠ a : ℝ in atTop,
        (Real.exp (-rho.re * a) *
          zeroPackageClosedTermsUniformBound) ^ 2 < R / 12 :=
    (tendsto_order.1 hclosed0).2 (R / 12) (div_pos hR (by norm_num))
  have hclosedY :
      ∀ᶠ Y : ℝ in atTop,
        (Real.exp (-rho.re * Real.log Y) *
          zeroPackageClosedTermsUniformBound) ^ 2 < R / 12 :=
    Real.tendsto_log_atTop.eventually hclosedA
  have hfullPos :
      0 < initialEmptyClusterFullMovingGaussianL2Constant ε rho k := by
    unfold initialEmptyClusterFullMovingGaussianL2Constant
    positivity
  refine ⟨k, hmissing, hfullPos, ?_⟩
  filter_upwards [hresidual, htransferY, hclosedY] with
      Y hresidualY htransferY' hclosedY'
  rcases htransferY' with ⟨T, hTmem, hgood, henergy⟩
  refine ⟨T, hTmem, hgood, ?_⟩
  have hRlower :
      R <
        normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
          ∅ T rho.re (Real.log Y)
            ((ε * Real.log Y) ^ 2) (ε * Real.log Y) := by
    dsimp [R]
    exact hresidualY T
  have hbudget :
      R / 6 <
        (1 / 3 : ℝ) *
              normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
                ∅ T rho.re (Real.log Y)
                  ((ε * Real.log Y) ^ 2) (ε * Real.log Y) -
            (eta ^ 2 +
              (Real.exp (-rho.re * Real.log Y) *
                zeroPackageClosedTermsUniformBound) ^ 2) := by
    nlinarith
  unfold initialEmptyClusterFullMovingGaussianL2Constant
  exact hbudget.trans_le henergy

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
