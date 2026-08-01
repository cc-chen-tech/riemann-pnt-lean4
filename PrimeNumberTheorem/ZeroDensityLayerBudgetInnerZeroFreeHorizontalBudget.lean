import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDesmoothedContourEdgeBudget
import ZeroFreeRegion.PhragmenLindelofZeta

open Complex MeasureTheory Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- The left endpoint of the narrower classical zero-free strip at contour
height `2*pi*W`. -/
noncomputable def innerZeroFreeHorizontalLeftBoundary (k W : ℝ) : ℝ :=
  1 - k / (2 * Real.log (2 * Real.pi * W))

/-- The log-squared logarithmic-derivative budget at contour height
`2*pi*W`. -/
noncomputable def innerZeroFreeHorizontalLogBudget (C W : ℝ) : ℝ :=
  C * (Real.log (2 * Real.pi * W)) ^ 2

/-- The bottom horizontal segment beginning at the inner zero-free boundary
inherits the actual zeta logarithmic-derivative bound. -/
theorem norm_logDeriv_cubicBottomContourPoint_le_innerZeroFreeHorizontalLogBudget
    {k C T0 c W sigma : ℝ}
    (hzero : ∀ sigma t : ℝ, T0 ≤ |t| →
      1 - k / (2 * Real.log |t|) ≤ sigma → sigma ≤ 2 →
        ‖logDeriv riemannZeta ((sigma : ℂ) + I * t)‖ ≤
          C * (Real.log |t|) ^ 2)
    (hW : 0 < W) (hheight : T0 ≤ 2 * Real.pi * W)
    (hleftc : innerZeroFreeHorizontalLeftBoundary k W ≤ c) (hc2 : c ≤ 2)
    (hsigma : sigma ∈ Ι (innerZeroFreeHorizontalLeftBoundary k W) c) :
    ‖logDeriv riemannZeta (cubicBottomContourPoint W sigma)‖ ≤
      innerZeroFreeHorizontalLogBudget C W := by
  have hT := two_pi_mul_pos hW
  have hleft : innerZeroFreeHorizontalLeftBoundary k W < sigma ∧ sigma ≤ c := by
    rw [Set.uIoc_of_le hleftc] at hsigma
    exact hsigma
  have hraw := hzero sigma (-(2 * Real.pi * W))
    (by simpa [abs_of_pos hT] using hheight)
    (by
      simpa [innerZeroFreeHorizontalLeftBoundary, abs_of_pos hT] using hleft.1.le)
    (hleft.2.trans hc2)
  simpa [cubicBottomContourPoint, innerZeroFreeHorizontalLogBudget,
    abs_of_pos hT, abs_of_pos hW, abs_of_pos Real.pi_pos,
    mul_assoc, mul_left_comm, mul_comm] using hraw

/-- The top horizontal segment beginning at the inner zero-free boundary
inherits the same actual zeta logarithmic-derivative bound. -/
theorem norm_logDeriv_cubicTopContourPoint_le_innerZeroFreeHorizontalLogBudget
    {k C T0 c W sigma : ℝ}
    (hzero : ∀ sigma t : ℝ, T0 ≤ |t| →
      1 - k / (2 * Real.log |t|) ≤ sigma → sigma ≤ 2 →
        ‖logDeriv riemannZeta ((sigma : ℂ) + I * t)‖ ≤
          C * (Real.log |t|) ^ 2)
    (hW : 0 < W) (hheight : T0 ≤ 2 * Real.pi * W)
    (hleftc : innerZeroFreeHorizontalLeftBoundary k W ≤ c) (hc2 : c ≤ 2)
    (hsigma : sigma ∈ Ι (innerZeroFreeHorizontalLeftBoundary k W) c) :
    ‖logDeriv riemannZeta (cubicTopContourPoint W sigma)‖ ≤
      innerZeroFreeHorizontalLogBudget C W := by
  have hT := two_pi_mul_pos hW
  have hleft : innerZeroFreeHorizontalLeftBoundary k W < sigma ∧ sigma ≤ c := by
    rw [Set.uIoc_of_le hleftc] at hsigma
    exact hsigma
  have hraw := hzero sigma (2 * Real.pi * W)
    (by simpa [abs_of_pos hT] using hheight)
    (by
      simpa [innerZeroFreeHorizontalLeftBoundary, abs_of_pos hT] using hleft.1.le)
    (hleft.2.trans hc2)
  simpa [cubicTopContourPoint, innerZeroFreeHorizontalLogBudget,
    abs_of_pos hT, abs_of_pos hW, abs_of_pos Real.pi_pos,
    mul_assoc, mul_left_comm, mul_comm] using hraw

/-- Automatic actual bottom-right horizontal contour budget from the narrower
classical zero-free strip. -/
theorem norm_desmoothedCubicBottomInnerZeroFreeContourIntegral_le
    {k C T0 x h c W : ℝ}
    (hzero : ∀ sigma t : ℝ, T0 ≤ |t| →
      1 - k / (2 * Real.log |t|) ≤ sigma → sigma ≤ 2 →
        ‖logDeriv riemannZeta ((sigma : ℂ) + I * t)‖ ≤
          C * (Real.log |t|) ^ 2)
    (hx : 0 < x) (hx1 : 1 ≤ x) (hC : 0 ≤ C) (hW : 0 < W)
    (hheight : T0 ≤ 2 * Real.pi * W)
    (hleftpos : 0 < innerZeroFreeHorizontalLeftBoundary k W)
    (hleftc : innerZeroFreeHorizontalLeftBoundary k W ≤ c) (hc2 : c ≤ 2)
    (hh : 0 < h) (hsmall : h * cubicHorizontalEdgeRadius c W ≤ 1) :
    ‖desmoothedCubicBottomContourIntegral x h
        (innerZeroFreeHorizontalLeftBoundary k W) c W‖ ≤
      desmoothedCubicPointwiseBudget x h c (2 * Real.pi * W)
          (innerZeroFreeHorizontalLogBudget C W)
          (cubicHorizontalEdgeRadius c W) *
        |c - innerZeroFreeHorizontalLeftBoundary k W| := by
  apply norm_desmoothedCubicBottomContourIntegral_le hx hx1 hleftpos hleftc
    hW
  · unfold innerZeroFreeHorizontalLogBudget
    positivity
  · intro sigma hsigma
    exact norm_logDeriv_cubicBottomContourPoint_le_innerZeroFreeHorizontalLogBudget
      hzero hW hheight hleftc hc2 hsigma
  · exact hh
  · exact hsmall

/-- Automatic actual top-right horizontal contour budget from the narrower
classical zero-free strip. -/
theorem norm_desmoothedCubicTopInnerZeroFreeContourIntegral_le
    {k C T0 x h c W : ℝ}
    (hzero : ∀ sigma t : ℝ, T0 ≤ |t| →
      1 - k / (2 * Real.log |t|) ≤ sigma → sigma ≤ 2 →
        ‖logDeriv riemannZeta ((sigma : ℂ) + I * t)‖ ≤
          C * (Real.log |t|) ^ 2)
    (hx : 0 < x) (hx1 : 1 ≤ x) (hC : 0 ≤ C) (hW : 0 < W)
    (hheight : T0 ≤ 2 * Real.pi * W)
    (hleftpos : 0 < innerZeroFreeHorizontalLeftBoundary k W)
    (hleftc : innerZeroFreeHorizontalLeftBoundary k W ≤ c) (hc2 : c ≤ 2)
    (hh : 0 < h) (hsmall : h * cubicHorizontalEdgeRadius c W ≤ 1) :
    ‖desmoothedCubicTopContourIntegral x h
        (innerZeroFreeHorizontalLeftBoundary k W) c W‖ ≤
      desmoothedCubicPointwiseBudget x h c (2 * Real.pi * W)
          (innerZeroFreeHorizontalLogBudget C W)
          (cubicHorizontalEdgeRadius c W) *
        |c - innerZeroFreeHorizontalLeftBoundary k W| := by
  apply norm_desmoothedCubicTopContourIntegral_le hx hx1 hleftpos hleftc
    hW
  · unfold innerZeroFreeHorizontalLogBudget
    positivity
  · intro sigma hsigma
    exact norm_logDeriv_cubicTopContourPoint_le_innerZeroFreeHorizontalLogBudget
      hzero hW hheight hleftc hc2 hsigma
  · exact hh
  · exact hsmall

/-- The existing proved inner zero-free-region theorem supplies constants for
both actual right horizontal contour budgets simultaneously. -/
theorem exists_actual_innerZeroFreeHorizontalContourBudgets :
    ∃ k C T0 : ℝ, 0 < k ∧ 0 ≤ C ∧ 2 ≤ T0 ∧
      ∀ x h c W : ℝ, 0 < x → 1 ≤ x → 0 < W →
        T0 ≤ 2 * Real.pi * W →
        0 < innerZeroFreeHorizontalLeftBoundary k W →
        innerZeroFreeHorizontalLeftBoundary k W ≤ c → c ≤ 2 →
        0 < h → h * cubicHorizontalEdgeRadius c W ≤ 1 →
        ‖desmoothedCubicBottomContourIntegral x h
            (innerZeroFreeHorizontalLeftBoundary k W) c W‖ ≤
          desmoothedCubicPointwiseBudget x h c (2 * Real.pi * W)
              (innerZeroFreeHorizontalLogBudget C W)
              (cubicHorizontalEdgeRadius c W) *
            |c - innerZeroFreeHorizontalLeftBoundary k W| ∧
        ‖desmoothedCubicTopContourIntegral x h
            (innerZeroFreeHorizontalLeftBoundary k W) c W‖ ≤
          desmoothedCubicPointwiseBudget x h c (2 * Real.pi * W)
              (innerZeroFreeHorizontalLogBudget C W)
              (cubicHorizontalEdgeRadius c W) *
            |c - innerZeroFreeHorizontalLeftBoundary k W| := by
  rcases
      ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_le_log_sq_on_inner_zeroFreeRegion
    with ⟨k, C, T0, hk, hC, hT0, hzero⟩
  refine ⟨k, C, T0, hk, hC, hT0, ?_⟩
  intro x h c W hx hx1 hW hheight hleftpos hleftc hc2 hh hsmall
  exact ⟨
    norm_desmoothedCubicBottomInnerZeroFreeContourIntegral_le hzero hx hx1
      hC hW hheight hleftpos hleftc hc2 hh hsmall,
    norm_desmoothedCubicTopInnerZeroFreeContourIntegral_le hzero hx hx1
      hC hW hheight hleftpos hleftc hc2 hh hsmall⟩

end ExplicitFormulaResidues
end PrimeNumberTheorem
