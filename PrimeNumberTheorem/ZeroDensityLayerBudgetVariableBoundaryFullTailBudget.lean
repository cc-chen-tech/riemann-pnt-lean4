import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryVisibleResidualAssembly
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryFullTail

/-!
# Variable-boundary full-tail budget

The visible Carlson tail controls only high positive-ordinate zeros.  This
module restores the mathematically correct bookkeeping for the complete
signed complement: conjugation costs a factor two on the positive tail, and
real-ordinate zeros remain a separate normalized term.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Positive-ordinate complement outside the pointwise moving package,
normalized by the moving target amplitude. -/
noncomputable def variableBoundaryPositiveNormalizedSum
    (H beta : ℝ → ℝ) (m : ℕ) : ℝ :=
  dynamicPositiveOutsideClusterPNTTailNorm H
      (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ) /
    variableBoundaryTargetAmplitude beta (m : ℝ)

/-- Real-ordinate complement outside the pointwise moving package,
normalized by the moving target amplitude. -/
noncomputable def variableBoundaryRealNormalizedSum
    (H beta : ℝ → ℝ) (m : ℕ) : ℝ :=
  dynamicRealOrdinateOutsideClusterPNTZeroTailNorm H
      (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ) /
    variableBoundaryTargetAmplitude beta (m : ℝ)

/-- The complete signed complement pays at most twice the positive-ordinate
tail plus the real-ordinate tail. -/
theorem abs_variableBoundaryComplement_div_le_two_positive_add_real
    {H beta : ℝ → ℝ} {m : ℕ} (hm : 0 < m) :
    |dynamicOutsideClusterPNTComplement H
        (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)| /
        variableBoundaryTargetAmplitude beta (m : ℝ) ≤
      2 * variableBoundaryPositiveNormalizedSum H beta m +
        variableBoundaryRealNormalizedSum H beta m := by
  have hcluster :
      IsConjugationInvariantCluster
        (variableBoundaryZeroPackage H beta (m : ℝ)) := by
    unfold variableBoundaryZeroPackage
    exact equalRealPartZeroPackage_isConjugationInvariant
      (H (m : ℝ)) (beta (m : ℝ))
  have hfull :=
    dynamicFullOutsideClusterPNTZeroTailNorm_le_two_positive_add_real
      (T := H) hcluster (show 0 < (m : ℝ) by exact_mod_cast hm)
  have hsigned :=
    abs_dynamicOutsideClusterPNTComplement_le_tailNorm H
      (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)
  have hAmplitude :
      0 < variableBoundaryTargetAmplitude beta (m : ℝ) := by
    unfold variableBoundaryTargetAmplitude targetZeroPowerAmplitude
    exact Real.rpow_pos_of_pos (by exact_mod_cast hm) _
  have hdivided :=
    (div_le_div_iff_of_pos_right hAmplitude).2 (hsigned.trans hfull)
  simpa [variableBoundaryPositiveNormalizedSum,
    variableBoundaryRealNormalizedSum, add_div, two_mul] using hdivided

/-- The complete positive-ordinate normalized tail is eventually bounded by
a separately controlled low-strip majorant plus the visible Carlson tail. -/
def VariableBoundaryVisiblePositiveTailMajorized
    {sigma : ℝ} (H beta : ℝ → ℝ) (low : ℕ → ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop,
    variableBoundaryPositiveNormalizedSum H beta m ≤
      low m +
        variableBoundaryVisibleNormalizedKernelTail
          (sigma := sigma) H beta m

/-- The low strip, visible high Carlson tail, and real-ordinate tail together
force decay of the complete signed moving-package complement. -/
theorem variableBoundaryFullComplement_targetAmplitudeNegligible
    {sigma : ℝ} {H beta : ℝ → ℝ} {low : ℕ → ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta)
    (hgap : VariableBoundaryAbsorptionOrGap (sigma := sigma) H beta)
    (hpositive :
      VariableBoundaryVisiblePositiveTailMajorized
        (sigma := sigma) H beta low)
    (hlow : Tendsto low atTop (𝓝 0))
    (hreal :
      Tendsto (variableBoundaryRealNormalizedSum H beta)
        atTop (𝓝 0)) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => variableBoundaryTargetAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        dynamicOutsideClusterPNTComplement H
          (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)) := by
  have htail :=
    variableBoundaryVisibleNormalizedKernelTail_tendsto_zero
      hhalf hone hright hgap
  have hmajor :
      Tendsto
        (fun m : ℕ =>
          2 * (low m +
              variableBoundaryVisibleNormalizedKernelTail
                (sigma := sigma) H beta m) +
            variableBoundaryRealNormalizedSum H beta m)
        atTop (𝓝 0) := by
    convert ((hlow.add htail).const_mul 2).add hreal using 1
    all_goals norm_num
  have hamplitude := eventually_variableBoundaryTargetAmplitude_pos beta
  unfold NaturalPointTargetAmplitudeNegligible
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [hamplitude] with m hamplitudeM
    exact div_nonneg (abs_nonneg _) hamplitudeM.le
  · unfold VariableBoundaryVisiblePositiveTailMajorized at hpositive
    filter_upwards [hpositive, eventually_gt_atTop (0 : ℕ)] with
        m hpositiveM hm
    have hfull :=
      abs_variableBoundaryComplement_div_le_two_positive_add_real
        (H := H) (beta := beta) hm
    linarith

/-- Exact variable-boundary explicit-formula residual theorem using the
constant-correct full-tail budget. -/
theorem
    actualVariableBoundaryFullTailExplicitFormulaResidual_targetAmplitudeNegligible
    {sigma beta0 : ℝ} {H beta : ℝ → ℝ} {low : ℕ → ℝ}
    (hbeta0 : 0 < beta0)
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta)
    (hgap : VariableBoundaryAbsorptionOrGap (sigma := sigma) H beta)
    (hpositive :
      VariableBoundaryVisiblePositiveTailMajorized
        (sigma := sigma) H beta low)
    (hlow : Tendsto low atTop (𝓝 0))
    (hreal :
      Tendsto (variableBoundaryRealNormalizedSum H beta)
        atTop (𝓝 0))
    (remainder :
      ActualSelectedHeightNaturalPointRemainderCertificate beta0 H) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => variableBoundaryTargetAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)) := by
  have hamplitude := eventually_variableBoundaryTargetAmplitude_pos beta
  have hclosedFixed :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta0 (m : ℝ))
        (fun m : ℕ => actualPNTClosedRealAxisRelativeTerm (m : ℝ)) :=
    (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible
      hbeta0).naturalPoint
  have hclosed :=
    naturalPointTargetAmplitudeNegligible_variableBoundary_of_fixed
      hbetaLower hclosedFixed
  have hcontour :=
    naturalPointTargetAmplitudeNegligible_variableBoundary_of_fixed
      hbetaLower remainder.negligible
  have hcomplement :=
    variableBoundaryFullComplement_targetAmplitudeNegligible
      hhalf hone hright hgap hpositive hlow hreal
  have hthree :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => variableBoundaryTargetAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
              actualPNTExplicitFormulaRelativeRemainder H (m : ℝ) +
            dynamicOutsideClusterPNTComplement H
              (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)) :=
    NaturalPointTargetAmplitudeNegligible.add hamplitude
      (NaturalPointTargetAmplitudeNegligible.add
        hamplitude hclosed hcontour)
      hcomplement
  unfold NaturalPointTargetAmplitudeNegligible at hthree ⊢
  apply hthree.congr'
  filter_upwards with m
  rw [relativeChebyshevPsi0Error_eq_variableBoundaryPackage_add_actualResiduals
    H beta (m : ℝ)]
  congr 2
  all_goals ring

end PrimeNumberTheorem
