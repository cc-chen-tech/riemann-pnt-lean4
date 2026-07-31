import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryFullTailBudget
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryRealOrdinateDecay

/-!
# Variable-boundary real-ordinate tail decay

Real-ordinate nontrivial zeros form a fixed finite set.  A strict fixed gap
below `beta0` gives decay at the fixed target amplitude, while an eventual
lower bound `beta0 <= beta(m)` makes this fixed finite sum a majorant for the
actual moving-package real tail.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Fixed-exponent finite majorant for all real-ordinate nontrivial zeros. -/
noncomputable def variableBoundaryRealOrdinateFixedMajorant
    (beta0 : ℝ) (m : ℕ) : ℝ :=
  ∑ rho ∈ realOrdinateNontrivialZerosFinset 0,
    ‖pntRelativeZeroContribution (m : ℝ) rho‖ /
      targetZeroPowerAmplitude beta0 (m : ℝ)

/-- A fixed strict real-part gap makes the finite real-ordinate majorant tend
to zero. -/
theorem variableBoundaryRealOrdinateFixedMajorant_tendsto_zero
    {beta0 : ℝ}
    (hright :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0) :
    Tendsto
      (variableBoundaryRealOrdinateFixedMajorant beta0)
      atTop (𝓝 0) := by
  unfold variableBoundaryRealOrdinateFixedMajorant
  simpa only [Finset.sum_const_zero] using
    tendsto_finset_sum
      (realOrdinateNontrivialZerosFinset 0)
      (fun rho hrho =>
        (tendsto_norm_pntRelativeZeroContribution_div_targetZeroPowerAmplitude
          (hright rho hrho)).comp tendsto_natCast_atTop_atTop)

/-- At one natural point, deleting moving-package members and enlarging the
target exponent bounds the actual real tail by the fixed finite majorant. -/
theorem variableBoundaryRealNormalizedSum_le_fixedMajorant
    {beta0 : ℝ} {H beta : ℝ → ℝ} {m : ℕ}
    (hm : 1 ≤ m)
    (hH : 0 ≤ H (m : ℝ))
    (hbeta : beta0 ≤ beta (m : ℝ)) :
    variableBoundaryRealNormalizedSum H beta m ≤
      variableBoundaryRealOrdinateFixedMajorant beta0 m := by
  let S := variableBoundaryZeroPackage H beta (m : ℝ)
  let base := realOrdinateNontrivialZerosFinset 0
  have hset :
      realOrdinateNontrivialZerosOutsideClusterFinset
          (H (m : ℝ)) S = base \ S := by
    unfold realOrdinateNontrivialZerosOutsideClusterFinset
    rw [realOrdinateNontrivialZerosFinset_eq_zeroHeight hH]
  have hnorm :
      ‖∑ rho ∈ base \ S,
          pntRelativeZeroContribution (m : ℝ) rho‖ ≤
        ∑ rho ∈ base \ S,
          ‖pntRelativeZeroContribution (m : ℝ) rho‖ :=
    norm_sum_le _ _
  have hsumle :
      (∑ rho ∈ base \ S,
          ‖pntRelativeZeroContribution (m : ℝ) rho‖) ≤
        ∑ rho ∈ base,
          ‖pntRelativeZeroContribution (m : ℝ) rho‖ := by
    rw [sum_sdiff_eq_sum_if_mem_zero]
    apply Finset.sum_le_sum
    intro rho hrho
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  have hfixedPos :
      0 < targetZeroPowerAmplitude beta0 (m : ℝ) := by
    unfold targetZeroPowerAmplitude
    exact Real.rpow_pos_of_pos (by exact_mod_cast (Nat.zero_lt_of_lt hm)) _
  have hvariablePos :
      0 < variableBoundaryTargetAmplitude beta (m : ℝ) := by
    unfold variableBoundaryTargetAmplitude targetZeroPowerAmplitude
    exact Real.rpow_pos_of_pos (by exact_mod_cast (Nat.zero_lt_of_lt hm)) _
  have hAmplitude :=
    targetZeroPowerAmplitude_le_variableBoundaryTargetAmplitude hm hbeta
  have hsumNonneg :
      0 ≤ ∑ rho ∈ base,
        ‖pntRelativeZeroContribution (m : ℝ) rho‖ := by positivity
  unfold variableBoundaryRealNormalizedSum
  rw [dynamicRealOrdinateOutsideClusterPNTZeroTailNorm, hset]
  calc
    ‖∑ rho ∈ base \ S,
        pntRelativeZeroContribution (m : ℝ) rho‖ /
          variableBoundaryTargetAmplitude beta (m : ℝ)
        ≤
      (∑ rho ∈ base \ S,
          ‖pntRelativeZeroContribution (m : ℝ) rho‖) /
            variableBoundaryTargetAmplitude beta (m : ℝ) :=
      (div_le_div_iff_of_pos_right hvariablePos).2 hnorm
    _ ≤
      (∑ rho ∈ base,
          ‖pntRelativeZeroContribution (m : ℝ) rho‖) /
            variableBoundaryTargetAmplitude beta (m : ℝ) :=
      (div_le_div_iff_of_pos_right hvariablePos).2 hsumle
    _ ≤
      (∑ rho ∈ base,
          ‖pntRelativeZeroContribution (m : ℝ) rho‖) /
            targetZeroPowerAmplitude beta0 (m : ℝ) := by
      apply (div_le_div_iff₀ hvariablePos hfixedPos).2
      exact mul_le_mul_of_nonneg_left hAmplitude hsumNonneg
    _ = variableBoundaryRealOrdinateFixedMajorant beta0 m := by
      unfold variableBoundaryRealOrdinateFixedMajorant
      rw [Finset.sum_div]

/-- The actual moving-package real-ordinate normalized tail tends to zero
from a fixed strict real gap and an eventual moving-exponent lower bound. -/
theorem variableBoundaryRealNormalizedSum_tendsto_zero_of_fixed_gap
    {beta0 : ℝ} {H beta : ℝ → ℝ}
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hright :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0) :
    Tendsto (variableBoundaryRealNormalizedSum H beta)
      atTop (𝓝 0) := by
  have hmajor :=
    variableBoundaryRealOrdinateFixedMajorant_tendsto_zero hright
  have hHnonneg :
      ∀ᶠ m : ℕ in atTop, 0 ≤ H (m : ℝ) :=
    hHtop.eventually (eventually_ge_atTop (0 : ℝ))
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    unfold variableBoundaryRealNormalizedSum
    exact div_nonneg (norm_nonneg _)
      (le_of_lt (by
        unfold variableBoundaryTargetAmplitude targetZeroPowerAmplitude
        exact Real.rpow_pos_of_pos
          (by exact_mod_cast (Nat.zero_lt_of_lt hm)) _))
  · filter_upwards
      [eventually_ge_atTop (1 : ℕ), hHnonneg, hbetaLower] with
        m hm hHm hbetaM
    exact variableBoundaryRealNormalizedSum_le_fixedMajorant
      hm hHm hbetaM

/-- Stack105's complete moving explicit-formula residual with the
real-ordinate tail discharged by the fixed-gap theorem. -/
theorem
    actualVariableBoundaryFullTailExplicitFormulaResidual_targetAmplitudeNegligible_of_realGap
    {sigma beta0 : ℝ} {H beta : ℝ → ℝ} {low : ℕ → ℝ}
    (hbeta0 : 0 < beta0)
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta)
    (hgap : VariableBoundaryAbsorptionOrGap (sigma := sigma) H beta)
    (hpositive :
      VariableBoundaryVisiblePositiveTailMajorized
        (sigma := sigma) H beta low)
    (hlow : Tendsto low atTop (𝓝 0))
    (remainder :
      ActualSelectedHeightNaturalPointRemainderCertificate beta0 H) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => variableBoundaryTargetAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)) := by
  apply
    actualVariableBoundaryFullTailExplicitFormulaResidual_targetAmplitudeNegligible
      hbeta0 hbetaLower hhalf hone hright hgap hpositive hlow
  · exact variableBoundaryRealNormalizedSum_tendsto_zero_of_fixed_gap
      hHtop hbetaLower hrightReal
  · exact remainder

end PrimeNumberTheorem
