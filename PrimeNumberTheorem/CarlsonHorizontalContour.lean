import PrimeNumberTheorem.CarlsonDetectorGrowth
import PrimeNumberTheorem.CarlsonLittlewood

open Complex Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Carlson's fixed-right Littlewood rectangle can be selected so that its
top edge carries the explicit logarithmic-derivative majorant.  The bottom
edge is confined to the fixed compact strip `-1 < Im(s) < 0`; bounding that
edge is the only remaining horizontal estimate in this certificate. -/
theorem exists_regularizedCarlson_fixedRight_count_with_explicit_top :
    ∃ C₁ C₂ : ℝ, 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {X : ℕ}, 1 ≤ X → ∀ {theta sigma T : ℝ},
        1 / 2 < theta → theta < sigma → sigma < 1 → 5 ≤ T →
        ∃ x0 y0 y1 : ℝ,
          theta < x0 ∧ x0 < sigma ∧ x0 < 4 ∧
          -1 < y0 ∧ y0 < 0 ∧
          T < y1 ∧ y1 ≤ T + 5 / 4 ∧ y0 < y1 ∧
          (∀ y ∈ Set.Icc y0 y1,
            regularizedCarlsonZeroDetector X
              ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
          (∀ y ∈ Set.Icc y0 y1,
            regularizedCarlsonZeroDetector X
              ((4 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
          (∀ x ∈ Set.Icc x0 4,
            regularizedCarlsonZeroDetector X
              ((x : ℂ) + (y0 : ℂ) * I) ≠ 0) ∧
          (∀ x ∈ Set.Icc x0 4,
            regularizedCarlsonZeroDetector X
              ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) ∧
          (2 * Real.pi) * (sigma - x0) *
              (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
            regularizedCarlsonLittlewoodFourEdges X x0 4 y0 y1 ∧
          ∀ x ∈ Set.Icc x0 4,
            ‖logDeriv (regularizedCarlsonZeroDetector X)
              ((x : ℂ) + (y1 : ℂ) * I)‖ ≤
              regularizedCarlsonHorizontalLogDerivMajorant
                C₁ C₂ X (T + 1 / 4) := by
  rcases exists_regularizedCarlson_horizontal_logDeriv_le_explicitMajorant with
    ⟨C₁, C₂, hC₁, hC₂, htopSelect⟩
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro X hX theta sigma T htheta hthetaSigma hsigmaOne hT
  have hthetaPos : 0 < theta := (by norm_num : (0 : ℝ) < 1 / 2).trans htheta
  have hTshift : 5 ≤ T + 1 / 4 := by linarith
  rcases htopSelect hX htheta hTshift with
    ⟨y1, hy1, htopNe, htopBound⟩
  rcases exists_regularizedCarlsonZeroDetector_horizontal_ne_zero
      hX hthetaPos (alpha := 4) (T := (-1 : ℝ)) with
    ⟨y0, hy0Lower, hy0Upper, hbottomTheta⟩
  rcases exists_regularizedCarlsonZeroDetector_vertical_ne_zero
      hX hthetaPos hthetaSigma (a := y0) (b := y1) with
    ⟨x0, hx0Lower, hx0Upper, hleft⟩
  have hx0Pos : 0 < x0 := hthetaPos.trans hx0Lower
  have hx04 : x0 < 4 := hx0Upper.trans (hsigmaOne.trans (by norm_num))
  have hTy1 : T < y1 := by linarith [hy1.1]
  have hy1Upper : y1 ≤ T + 5 / 4 := by linarith [hy1.2]
  have hy0Neg : y0 < 0 := by linarith [hy0Upper]
  have hy01 : y0 < y1 := by linarith [hy0Upper, hTy1, hT]
  have hright : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((4 : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y _hy
    apply regularizedCarlsonZeroDetector_ne_zero_of_four_le_re hX
    simp
  have hbottom : ∀ x ∈ Set.Icc x0 4,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y0 : ℂ) * I) ≠ 0 := by
    intro x hx
    apply hbottomTheta x
    exact ⟨hx0Lower.le.trans hx.1, hx.2⟩
  have htop : ∀ x ∈ Set.Icc x0 4,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y1 : ℂ) * I) ≠ 0 := by
    intro x hx
    apply htopNe x
    exact ⟨hx0Lower.le.trans hx.1, hx.2⟩
  have htop' : ∀ x ∈ Set.Icc x0 4,
      ‖logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y1 : ℂ) * I)‖ ≤
        regularizedCarlsonHorizontalLogDerivMajorant
          C₁ C₂ X (T + 1 / 4) := by
    intro x hx
    apply htopBound x
    exact ⟨hx0Lower.le.trans hx.1, hx.2⟩
  have hcount :=
    sub_mul_zeroDensityCount_le_regularizedCarlsonWeightedZeroSum
      (sigma := sigma) (T := T) (x0 := x0) (x1 := 4)
        (y0 := y0) (y1 := y1) hX hx0Pos hx0Upper
        (by norm_num) hy0Neg hTy1
  have htwoPi : 0 ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hscaled := mul_le_mul_of_nonneg_left hcount htwoPi
  have hedges :=
    two_pi_mul_regularizedCarlsonZeroMultiplicityWeightedRealSum_eq_four_edges
      hX hx0Pos hx04 hy01 hleft hright hbottom htop
  refine ⟨x0, y0, y1,
    hx0Lower, hx0Upper, hx04,
    hy0Lower, hy0Neg, hTy1, hy1Upper, hy01,
    hleft, hright, hbottom, htop, ?_, htop'⟩
  calc
    (2 * Real.pi) * (sigma - x0) *
        (ZeroDensity.zeroDensityCount sigma T : ℝ) =
        (2 * Real.pi) *
          ((sigma - x0) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) := by ring
    _ ≤ (2 * Real.pi) *
        ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
            X x0 4 y0 y1,
          (rho.re - x0) *
            (analyticOrderNatAt
              (regularizedCarlsonZeroDetector X) rho : ℝ) := hscaled
    _ = regularizedCarlsonLittlewoodFourEdges X x0 4 y0 y1 := by
      simpa [regularizedCarlsonLittlewoodFourEdges] using hedges

/-- Carlson's fixed-right rectangle with both horizontal logarithmic
derivatives bounded by the same explicit majorant.  Moving the bottom edge to
the high, fixed window `[5, 6]` avoids a separate low-height growth argument;
the omitted zeros are paid for by the fixed global count at height `6`. -/
theorem exists_regularizedCarlson_fixedRight_count_with_explicit_horizontals :
    ∃ C₁ C₂ : ℝ, 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {X : ℕ}, 1 ≤ X → ∀ {theta sigma T : ℝ},
        1 / 2 < theta → theta < sigma → sigma < 1 → 6 ≤ T →
        ∃ x0 y0 y1 : ℝ,
          theta < x0 ∧ x0 < sigma ∧ x0 < 4 ∧
          5 ≤ y0 ∧ y0 ≤ 6 ∧
          T < y1 ∧ y1 ≤ T + 5 / 4 ∧ y0 < y1 ∧
          (∀ y ∈ Set.Icc y0 y1,
            regularizedCarlsonZeroDetector X
              ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
          (∀ y ∈ Set.Icc y0 y1,
            regularizedCarlsonZeroDetector X
              ((4 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
          (∀ x ∈ Set.Icc x0 4,
            regularizedCarlsonZeroDetector X
              ((x : ℂ) + (y0 : ℂ) * I) ≠ 0) ∧
          (∀ x ∈ Set.Icc x0 4,
            regularizedCarlsonZeroDetector X
              ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) ∧
          (2 * Real.pi) * (sigma - x0) *
              (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
            (2 * Real.pi) * (sigma - x0) *
                ExplicitFormulaAux.globalZeroMultiplicity 6 +
              regularizedCarlsonLittlewoodFourEdges X x0 4 y0 y1 ∧
          (∀ x ∈ Set.Icc x0 4,
            ‖logDeriv (regularizedCarlsonZeroDetector X)
              ((x : ℂ) + (y0 : ℂ) * I)‖ ≤
              regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5) ∧
          ∀ x ∈ Set.Icc x0 4,
            ‖logDeriv (regularizedCarlsonZeroDetector X)
              ((x : ℂ) + (y1 : ℂ) * I)‖ ≤
              regularizedCarlsonHorizontalLogDerivMajorant
                C₁ C₂ X (T + 1 / 4) := by
  rcases exists_regularizedCarlson_horizontal_logDeriv_le_explicitMajorant with
    ⟨C₁, C₂, hC₁, hC₂, hselect⟩
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro X hX theta sigma T htheta hthetaSigma hsigmaOne hT
  have hthetaPos : 0 < theta := (by norm_num : (0 : ℝ) < 1 / 2).trans htheta
  rcases hselect hX htheta (T := (5 : ℝ)) (by norm_num) with
    ⟨y0, hy0, hbottomTheta, hbottomBoundTheta⟩
  have hy0Upper : y0 ≤ 6 := by linarith [hy0.2]
  have hTshift : 5 ≤ T + 1 / 4 := by linarith
  rcases hselect hX htheta hTshift with
    ⟨y1, hy1, htopTheta, htopBoundTheta⟩
  have hTy1 : T < y1 := by linarith [hy1.1]
  have hy1Upper : y1 ≤ T + 5 / 4 := by linarith [hy1.2]
  have hy01 : y0 < y1 := by linarith [hy0.2, hT, hTy1]
  rcases exists_regularizedCarlsonZeroDetector_vertical_ne_zero
      hX hthetaPos hthetaSigma (a := y0) (b := y1) with
    ⟨x0, hx0Lower, hx0Upper, hleft⟩
  have hx0Pos : 0 < x0 := hthetaPos.trans hx0Lower
  have hx04 : x0 < 4 := hx0Upper.trans (hsigmaOne.trans (by norm_num))
  have hright : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((4 : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y _hy
    apply regularizedCarlsonZeroDetector_ne_zero_of_four_le_re hX
    simp
  have hbottom : ∀ x ∈ Set.Icc x0 4,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y0 : ℂ) * I) ≠ 0 := by
    intro x hx
    apply hbottomTheta x
    exact ⟨hx0Lower.le.trans hx.1, hx.2⟩
  have htop : ∀ x ∈ Set.Icc x0 4,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y1 : ℂ) * I) ≠ 0 := by
    intro x hx
    apply htopTheta x
    exact ⟨hx0Lower.le.trans hx.1, hx.2⟩
  have hbottomBound : ∀ x ∈ Set.Icc x0 4,
      ‖logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y0 : ℂ) * I)‖ ≤
        regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5 := by
    intro x hx
    apply hbottomBoundTheta x
    exact ⟨hx0Lower.le.trans hx.1, hx.2⟩
  have htopBound : ∀ x ∈ Set.Icc x0 4,
      ‖logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y1 : ℂ) * I)‖ ≤
        regularizedCarlsonHorizontalLogDerivMajorant
          C₁ C₂ X (T + 1 / 4) := by
    intro x hx
    apply htopBoundTheta x
    exact ⟨hx0Lower.le.trans hx.1, hx.2⟩
  have hcount :=
    sub_mul_zeroDensityCount_le_low_global_add_regularizedCarlsonWeightedZeroSum
      (X := X) hX (sigma := sigma) (T := T) (U := 6)
        (x0 := x0) (x1 := 4) (y0 := y0) (y1 := y1)
        hx0Pos hx0Upper (by norm_num) hy0Upper hTy1
  have htwoPi : 0 ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hscaled := mul_le_mul_of_nonneg_left hcount htwoPi
  have hedges :=
    two_pi_mul_regularizedCarlsonZeroMultiplicityWeightedRealSum_eq_four_edges
      hX hx0Pos hx04 hy01 hleft hright hbottom htop
  refine ⟨x0, y0, y1,
    hx0Lower, hx0Upper, hx04,
    hy0.1, hy0Upper, hTy1, hy1Upper, hy01,
    hleft, hright, hbottom, htop, ?_, hbottomBound, htopBound⟩
  calc
    (2 * Real.pi) * (sigma - x0) *
        (ZeroDensity.zeroDensityCount sigma T : ℝ) =
        (2 * Real.pi) *
          ((sigma - x0) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) := by ring
    _ ≤ (2 * Real.pi) *
        ((sigma - x0) * ExplicitFormulaAux.globalZeroMultiplicity 6 +
          ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
              X x0 4 y0 y1,
            (rho.re - x0) *
              (analyticOrderNatAt
                (regularizedCarlsonZeroDetector X) rho : ℝ)) := hscaled
    _ = (2 * Real.pi) * (sigma - x0) *
          ExplicitFormulaAux.globalZeroMultiplicity 6 +
        (2 * Real.pi) *
          ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
              X x0 4 y0 y1,
            (rho.re - x0) *
              (analyticOrderNatAt
                (regularizedCarlsonZeroDetector X) rho : ℝ) := by ring
    _ = (2 * Real.pi) * (sigma - x0) *
          ExplicitFormulaAux.globalZeroMultiplicity 6 +
        regularizedCarlsonLittlewoodFourEdges X x0 4 y0 y1 := by
      exact congrArg
        (fun z : ℝ =>
          (2 * Real.pi) * (sigma - x0) *
            ExplicitFormulaAux.globalZeroMultiplicity 6 + z)
        hedges

/-- A window-controlled version of the fixed-right Carlson rectangle.  The
left edge is selected below `eta`, while the counted zeros may lie to the
right of the larger target `sigma`.  This separation is what later permits a
quantitative lower bound on `sigma - x0`. -/
theorem
    exists_regularizedCarlson_fixedRight_count_with_explicit_horizontals_of_leftWindow :
    ∃ C₁ C₂ : ℝ, 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {X : ℕ}, 1 ≤ X → ∀ {theta eta sigma T : ℝ},
        1 / 2 < theta → theta < eta → eta ≤ sigma → sigma < 1 → 6 ≤ T →
        ∃ x0 y0 y1 : ℝ,
          theta < x0 ∧ x0 < eta ∧ x0 < sigma ∧ x0 < 4 ∧
          5 ≤ y0 ∧ y0 ≤ 6 ∧
          T < y1 ∧ y1 ≤ T + 5 / 4 ∧ y0 < y1 ∧
          (∀ y ∈ Set.Icc y0 y1,
            regularizedCarlsonZeroDetector X
              ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
          (∀ y ∈ Set.Icc y0 y1,
            regularizedCarlsonZeroDetector X
              ((4 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
          (∀ x ∈ Set.Icc x0 4,
            regularizedCarlsonZeroDetector X
              ((x : ℂ) + (y0 : ℂ) * I) ≠ 0) ∧
          (∀ x ∈ Set.Icc x0 4,
            regularizedCarlsonZeroDetector X
              ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) ∧
          (2 * Real.pi) * (sigma - x0) *
              (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
            (2 * Real.pi) * (sigma - x0) *
                ExplicitFormulaAux.globalZeroMultiplicity 6 +
              regularizedCarlsonLittlewoodFourEdges X x0 4 y0 y1 ∧
          (∀ x ∈ Set.Icc x0 4,
            ‖logDeriv (regularizedCarlsonZeroDetector X)
              ((x : ℂ) + (y0 : ℂ) * I)‖ ≤
              regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5) ∧
          ∀ x ∈ Set.Icc x0 4,
            ‖logDeriv (regularizedCarlsonZeroDetector X)
              ((x : ℂ) + (y1 : ℂ) * I)‖ ≤
              regularizedCarlsonHorizontalLogDerivMajorant
                C₁ C₂ X (T + 1 / 4) := by
  rcases exists_regularizedCarlson_horizontal_logDeriv_le_explicitMajorant with
    ⟨C₁, C₂, hC₁, hC₂, hselect⟩
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro X hX theta eta sigma T htheta hthetaEta hetaSigma hsigmaOne hT
  have hthetaPos : 0 < theta := (by norm_num : (0 : ℝ) < 1 / 2).trans htheta
  rcases hselect hX htheta (T := (5 : ℝ)) (by norm_num) with
    ⟨y0, hy0, hbottomTheta, hbottomBoundTheta⟩
  have hy0Upper : y0 ≤ 6 := by linarith [hy0.2]
  have hTshift : 5 ≤ T + 1 / 4 := by linarith
  rcases hselect hX htheta hTshift with
    ⟨y1, hy1, htopTheta, htopBoundTheta⟩
  have hTy1 : T < y1 := by linarith [hy1.1]
  have hy1Upper : y1 ≤ T + 5 / 4 := by linarith [hy1.2]
  have hy01 : y0 < y1 := by linarith [hy0.2, hT, hTy1]
  rcases exists_regularizedCarlsonZeroDetector_vertical_ne_zero
      hX hthetaPos hthetaEta (a := y0) (b := y1) with
    ⟨x0, hx0Lower, hx0Eta, hleft⟩
  have hx0Sigma : x0 < sigma := hx0Eta.trans_le hetaSigma
  have hx0Pos : 0 < x0 := hthetaPos.trans hx0Lower
  have hx04 : x0 < 4 := hx0Sigma.trans (hsigmaOne.trans (by norm_num))
  have hright : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((4 : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y _hy
    apply regularizedCarlsonZeroDetector_ne_zero_of_four_le_re hX
    simp
  have hbottom : ∀ x ∈ Set.Icc x0 4,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y0 : ℂ) * I) ≠ 0 := by
    intro x hx
    apply hbottomTheta x
    exact ⟨hx0Lower.le.trans hx.1, hx.2⟩
  have htop : ∀ x ∈ Set.Icc x0 4,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y1 : ℂ) * I) ≠ 0 := by
    intro x hx
    apply htopTheta x
    exact ⟨hx0Lower.le.trans hx.1, hx.2⟩
  have hbottomBound : ∀ x ∈ Set.Icc x0 4,
      ‖logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y0 : ℂ) * I)‖ ≤
        regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5 := by
    intro x hx
    apply hbottomBoundTheta x
    exact ⟨hx0Lower.le.trans hx.1, hx.2⟩
  have htopBound : ∀ x ∈ Set.Icc x0 4,
      ‖logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y1 : ℂ) * I)‖ ≤
        regularizedCarlsonHorizontalLogDerivMajorant
          C₁ C₂ X (T + 1 / 4) := by
    intro x hx
    apply htopBoundTheta x
    exact ⟨hx0Lower.le.trans hx.1, hx.2⟩
  have hcount :=
    sub_mul_zeroDensityCount_le_low_global_add_regularizedCarlsonWeightedZeroSum
      (X := X) hX (sigma := sigma) (T := T) (U := 6)
        (x0 := x0) (x1 := 4) (y0 := y0) (y1 := y1)
        hx0Pos hx0Sigma (by norm_num) hy0Upper hTy1
  have htwoPi : 0 ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hscaled := mul_le_mul_of_nonneg_left hcount htwoPi
  have hedges :=
    two_pi_mul_regularizedCarlsonZeroMultiplicityWeightedRealSum_eq_four_edges
      hX hx0Pos hx04 hy01 hleft hright hbottom htop
  refine ⟨x0, y0, y1,
    hx0Lower, hx0Eta, hx0Sigma, hx04,
    hy0.1, hy0Upper, hTy1, hy1Upper, hy01,
    hleft, hright, hbottom, htop, ?_, hbottomBound, htopBound⟩
  calc
    (2 * Real.pi) * (sigma - x0) *
        (ZeroDensity.zeroDensityCount sigma T : ℝ) =
        (2 * Real.pi) *
          ((sigma - x0) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) := by ring
    _ ≤ (2 * Real.pi) *
        ((sigma - x0) * ExplicitFormulaAux.globalZeroMultiplicity 6 +
          ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
              X x0 4 y0 y1,
            (rho.re - x0) *
              (analyticOrderNatAt
                (regularizedCarlsonZeroDetector X) rho : ℝ)) := hscaled
    _ = (2 * Real.pi) * (sigma - x0) *
          ExplicitFormulaAux.globalZeroMultiplicity 6 +
        (2 * Real.pi) *
          ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
              X x0 4 y0 y1,
            (rho.re - x0) *
              (analyticOrderNatAt
                (regularizedCarlsonZeroDetector X) rho : ℝ) := by ring
    _ = (2 * Real.pi) * (sigma - x0) *
          ExplicitFormulaAux.globalZeroMultiplicity 6 +
        regularizedCarlsonLittlewoodFourEdges X x0 4 y0 y1 := by
      exact congrArg
        (fun z : ℝ =>
          (2 * Real.pi) * (sigma - x0) *
            ExplicitFormulaAux.globalZeroMultiplicity 6 + z)
        hedges

/-- The two selected horizontal bounds are absorbed into the explicit
remaining-boundary estimate, leaving only the left logarithmic norm integral
for the Carlson mean-square argument. -/
theorem exists_regularizedCarlson_fixedRight_count_le_left_add_explicit_boundary :
    ∃ C₁ C₂ : ℝ, 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {X : ℕ}, 1 ≤ X → ∀ {theta sigma T : ℝ},
        1 / 2 < theta → theta < sigma → sigma < 1 → 6 ≤ T →
        ∃ x0 y0 y1 : ℝ,
          theta < x0 ∧ x0 < sigma ∧ x0 < 4 ∧
          5 ≤ y0 ∧ y0 ≤ 6 ∧
          T < y1 ∧ y1 ≤ T + 5 / 4 ∧ y0 < y1 ∧
          (∀ y ∈ Set.Icc y0 y1,
            regularizedCarlsonZeroDetector X
              ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
          (2 * Real.pi) * (sigma - x0) *
              (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
            (2 * Real.pi) * (sigma - x0) *
                ExplicitFormulaAux.globalZeroMultiplicity 6 +
              (∫ y in y0..y1,
                Real.log ‖regularizedCarlsonZeroDetector X
                  ((x0 : ℂ) + (y : ℂ) * I)‖) +
              (4 - x0) ^ 2 *
                (regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5 +
                  regularizedCarlsonHorizontalLogDerivMajorant
                    C₁ C₂ X (T + 1 / 4)) +
              (4 - x0) * (3 * Real.pi) -
              (y1 - y0) * Real.log (56 / 81 : ℝ) := by
  rcases exists_regularizedCarlson_fixedRight_count_with_explicit_horizontals with
    ⟨C₁, C₂, hC₁, hC₂, hcertificate⟩
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro X hX theta sigma T htheta hthetaSigma hsigmaOne hT
  rcases hcertificate hX htheta hthetaSigma hsigmaOne hT with
    ⟨x0, y0, y1,
      hx0Lower, hx0Upper, hx04,
      hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
      hleft, hright, hbottom, htop, hcount,
      hbottomBound, htopBound⟩
  have hx0Pos : 0 < x0 :=
    ((by norm_num : (0 : ℝ) < 1 / 2).trans htheta).trans hx0Lower
  let M0 := regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5
  let M1 := regularizedCarlsonHorizontalLogDerivMajorant
    C₁ C₂ X (T + 1 / 4)
  have hM0 : 0 ≤ M0 := by
    exact (norm_nonneg _).trans
      (hbottomBound x0 ⟨le_rfl, hx04.le⟩)
  have hM1 : 0 ≤ M1 := by
    exact (norm_nonneg _).trans
      (htopBound x0 ⟨le_rfl, hx04.le⟩)
  have hremaining :
      regularizedCarlsonLittlewoodRemainingEdges X x0 4 y0 y1 ≤
        (4 - x0) ^ 2 * (M0 + M1) +
          (4 - x0) * (3 * Real.pi) -
          (y1 - y0) * Real.log (56 / 81 : ℝ) :=
    regularizedCarlsonLittlewoodRemainingEdges_fixedRight_le_of_horizontalBounds
      hX hx04.le hy01.le hM0 hM1 hbottomBound htopBound
  have hform := regularizedCarlsonLittlewoodFourEdges_eq_logNormFormDef
    hx0Pos hx04 hy01 hleft hright hbottom htop
  rw [hform,
    regularizedCarlsonLittlewoodLogNormForm_eq_left_add_remaining] at hcount
  refine ⟨x0, y0, y1,
    hx0Lower, hx0Upper, hx04,
    hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
    hleft, ?_⟩
  dsimp [M0, M1] at hremaining ⊢
  linarith

/-- Window-controlled left-edge certificate.  In addition to the target
counting line `sigma`, it records the strict upper window `x0 < eta`, which
is later used to bound `sigma - x0` from below. -/
theorem
    exists_regularizedCarlson_fixedRight_count_le_left_add_explicit_boundary_of_leftWindow :
    ∃ C₁ C₂ : ℝ, 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {X : ℕ}, 1 ≤ X → ∀ {theta eta sigma T : ℝ},
        1 / 2 < theta → theta < eta → eta ≤ sigma → sigma < 1 → 6 ≤ T →
        ∃ x0 y0 y1 : ℝ,
          theta < x0 ∧ x0 < eta ∧ x0 < sigma ∧ x0 < 4 ∧
          5 ≤ y0 ∧ y0 ≤ 6 ∧
          T < y1 ∧ y1 ≤ T + 5 / 4 ∧ y0 < y1 ∧
          (∀ y ∈ Set.Icc y0 y1,
            regularizedCarlsonZeroDetector X
              ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
          (2 * Real.pi) * (sigma - x0) *
              (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
            (2 * Real.pi) * (sigma - x0) *
                ExplicitFormulaAux.globalZeroMultiplicity 6 +
              (∫ y in y0..y1,
                Real.log ‖regularizedCarlsonZeroDetector X
                  ((x0 : ℂ) + (y : ℂ) * I)‖) +
              (4 - x0) ^ 2 *
                (regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5 +
                  regularizedCarlsonHorizontalLogDerivMajorant
                    C₁ C₂ X (T + 1 / 4)) +
              (4 - x0) * (3 * Real.pi) -
              (y1 - y0) * Real.log (56 / 81 : ℝ) := by
  rcases
      exists_regularizedCarlson_fixedRight_count_with_explicit_horizontals_of_leftWindow with
    ⟨C₁, C₂, hC₁, hC₂, hcertificate⟩
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro X hX theta eta sigma T htheta hthetaEta hetaSigma hsigmaOne hT
  rcases hcertificate hX htheta hthetaEta hetaSigma hsigmaOne hT with
    ⟨x0, y0, y1,
      hx0Lower, hx0Eta, hx0Sigma, hx04,
      hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
      hleft, hright, hbottom, htop, hcount,
      hbottomBound, htopBound⟩
  have hx0Pos : 0 < x0 :=
    ((by norm_num : (0 : ℝ) < 1 / 2).trans htheta).trans hx0Lower
  let M0 := regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5
  let M1 := regularizedCarlsonHorizontalLogDerivMajorant
    C₁ C₂ X (T + 1 / 4)
  have hM0 : 0 ≤ M0 := by
    exact (norm_nonneg _).trans
      (hbottomBound x0 ⟨le_rfl, hx04.le⟩)
  have hM1 : 0 ≤ M1 := by
    exact (norm_nonneg _).trans
      (htopBound x0 ⟨le_rfl, hx04.le⟩)
  have hremaining :
      regularizedCarlsonLittlewoodRemainingEdges X x0 4 y0 y1 ≤
        (4 - x0) ^ 2 * (M0 + M1) +
          (4 - x0) * (3 * Real.pi) -
          (y1 - y0) * Real.log (56 / 81 : ℝ) :=
    regularizedCarlsonLittlewoodRemainingEdges_fixedRight_le_of_horizontalBounds
      hX hx04.le hy01.le hM0 hM1 hbottomBound htopBound
  have hform := regularizedCarlsonLittlewoodFourEdges_eq_logNormFormDef
    hx0Pos hx04 hy01 hleft hright hbottom htop
  rw [hform,
    regularizedCarlsonLittlewoodLogNormForm_eq_left_add_remaining] at hcount
  refine ⟨x0, y0, y1,
    hx0Lower, hx0Eta, hx0Sigma, hx04,
    hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
    hleft, ?_⟩
  dsimp [M0, M1] at hremaining ⊢
  linarith

private theorem
    integral_log_norm_regularizedCarlsonZeroDetector_le_geometricCoverOfEndpoint
    (E : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hdouble : ∀ (X : ℕ) (sigma u v : ℝ),
      1 ≤ X → 1 ≤ u → u ≤ v → v ≤ 2 * u →
      1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc u v,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in u..v,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          E X sigma u v (4 * u))
    (X : ℕ) (sigma u v : ℝ) (n : ℕ)
    (hX : 1 ≤ X) (hu : 1 ≤ u)
    (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1)
    (hnv : u * (2 : ℝ) ^ n ≤ v)
    (hvn : v ≤ u * (2 : ℝ) ^ (n + 1))
    (hboundary : ∀ t ∈ Set.Icc u v,
      regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t) ≠ 0) :
    (∫ t in u..v,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖) ≤
      (∑ k ∈ Finset.range n,
        E X sigma (u * (2 : ℝ) ^ k)
          (u * (2 : ℝ) ^ (k + 1))
          (4 * (u * (2 : ℝ) ^ k))) +
      E X sigma (u * (2 : ℝ) ^ n) v
        (4 * (u * (2 : ℝ) ^ n)) := by
  induction n generalizing v with
  | zero =>
      have huv : u ≤ v := by simpa using hnv
      have hvu : v ≤ 2 * u := by simpa [mul_comm] using hvn
      simpa using
        hdouble X sigma u v hX hu huv hvu hsigma hsigma1 hboundary
  | succ n ih =>
      let w : ℝ := u * (2 : ℝ) ^ (n + 1)
      have huw : u ≤ w := by
        dsimp [w]
        have hpow : 1 ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
        nlinarith [show 0 ≤ u by linarith]
      have hwv : w ≤ v := by simpa [w] using hnv
      have hvw : v ≤ 2 * w := by
        simpa [w, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hvn
      have hwOne : 1 ≤ w := hu.trans huw
      have hleftBoundary : ∀ t ∈ Set.Icc u w,
          regularizedCarlsonZeroDetector X
            ((sigma : ℂ) + Complex.I * t) ≠ 0 := by
        intro t ht
        exact hboundary t ⟨ht.1, ht.2.trans hwv⟩
      have hrightBoundary : ∀ t ∈ Set.Icc w v,
          regularizedCarlsonZeroDetector X
            ((sigma : ℂ) + Complex.I * t) ≠ 0 := by
        intro t ht
        exact hboundary t ⟨huw.trans ht.1, ht.2⟩
      have hleftLower : u * (2 : ℝ) ^ n ≤ w := by
        dsimp [w]
        have hstep : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) :=
          pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
        exact mul_le_mul_of_nonneg_left hstep (by linarith)
      have hleftUpper : w ≤ u * (2 : ℝ) ^ (n + 1) := by rfl
      have hleft := ih w hleftLower hleftUpper hleftBoundary
      have hright :=
        hdouble X sigma w v hX hwOne hwv hvw hsigma hsigma1 hrightBoundary
      let f : ℝ → ℝ := fun t =>
        Real.log ‖regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖
      have hleftInt : IntervalIntegrable f MeasureTheory.volume u w := by
        apply intervalIntegrable_log_norm_regularizedCarlsonZeroDetector
          (by linarith)
        intro t ht
        rw [Set.uIcc_of_le huw] at ht
        exact hleftBoundary t ht
      have hrightInt : IntervalIntegrable f MeasureTheory.volume w v := by
        apply intervalIntegrable_log_norm_regularizedCarlsonZeroDetector
          (by linarith)
        intro t ht
        rw [Set.uIcc_of_le hwv] at ht
        exact hrightBoundary t ht
      calc
        (∫ t in u..v, f t) =
            (∫ t in u..w, f t) + ∫ t in w..v, f t := by
          exact (intervalIntegral.integral_add_adjacent_intervals
            hleftInt hrightInt).symm
        _ ≤ ((∑ k ∈ Finset.range n,
              E X sigma (u * (2 : ℝ) ^ k)
                (u * (2 : ℝ) ^ (k + 1))
                (4 * (u * (2 : ℝ) ^ k))) +
              E X sigma (u * (2 : ℝ) ^ n) w
                (4 * (u * (2 : ℝ) ^ n))) +
            E X sigma w v (4 * w) := add_le_add hleft hright
        _ = (∑ k ∈ Finset.range (n + 1),
              E X sigma (u * (2 : ℝ) ^ k)
                (u * (2 : ℝ) ^ (k + 1))
                (4 * (u * (2 : ℝ) ^ k))) +
            E X sigma (u * (2 : ℝ) ^ (n + 1)) v
              (4 * (u * (2 : ℝ) ^ (n + 1))) := by
          simp only [Finset.sum_range_succ]
          rfl

private theorem
    integral_log_norm_regularizedCarlsonZeroDetector_le_geometricCoverExplicit
    {A : ℝ}
    (hdouble : ∀ (X : ℕ) (sigma u v : ℝ),
      1 ≤ X → 1 ≤ u → u ≤ v → v ≤ 2 * u →
      1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc u v,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in u..v,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          regularizedCarlsonLogNormEndpointExplicit
            A 4 X sigma u v (4 * u))
    (X : ℕ) (sigma u v : ℝ) (n : ℕ)
    (hX : 1 ≤ X) (hu : 1 ≤ u)
    (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1)
    (hnv : u * (2 : ℝ) ^ n ≤ v)
    (hvn : v ≤ u * (2 : ℝ) ^ (n + 1))
    (hboundary : ∀ t ∈ Set.Icc u v,
      regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t) ≠ 0) :
    (∫ t in u..v,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖) ≤
      (∑ k ∈ Finset.range n,
        regularizedCarlsonLogNormEndpointExplicit
          A 4 X sigma (u * (2 : ℝ) ^ k)
            (u * (2 : ℝ) ^ (k + 1))
            (4 * (u * (2 : ℝ) ^ k))) +
      regularizedCarlsonLogNormEndpointExplicit
        A 4 X sigma (u * (2 : ℝ) ^ n) v
          (4 * (u * (2 : ℝ) ^ n)) := by
  exact integral_log_norm_regularizedCarlsonZeroDetector_le_geometricCoverOfEndpoint
    (fun X sigma u v x =>
      regularizedCarlsonLogNormEndpointExplicit A 4 X sigma u v x)
    hdouble X sigma u v n hX hu hsigma hsigma1 hnv hvn hboundary

private theorem
    integral_log_norm_carlsonZeroDetector_le_geometricCoverOfEndpoint
    (E : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hdouble : ∀ (X : ℕ) (sigma u v : ℝ),
      1 ≤ X → 1 ≤ u → u ≤ v → v ≤ 2 * u →
      1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc u v,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in u..v,
            Real.log ‖carlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          E X sigma u v (4 * u))
    (X : ℕ) (sigma u v : ℝ) (n : ℕ)
    (hX : 1 ≤ X) (hu : 1 ≤ u)
    (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1)
    (hnv : u * (2 : ℝ) ^ n ≤ v)
    (hvn : v ≤ u * (2 : ℝ) ^ (n + 1))
    (hboundary : ∀ t ∈ Set.Icc u v,
      regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t) ≠ 0) :
    (∫ t in u..v,
        Real.log ‖carlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖) ≤
      (∑ k ∈ Finset.range n,
        E X sigma (u * (2 : ℝ) ^ k)
          (u * (2 : ℝ) ^ (k + 1))
          (4 * (u * (2 : ℝ) ^ k))) +
      E X sigma (u * (2 : ℝ) ^ n) v
        (4 * (u * (2 : ℝ) ^ n)) := by
  induction n generalizing v with
  | zero =>
      have huv : u ≤ v := by simpa using hnv
      have hvu : v ≤ 2 * u := by simpa [mul_comm] using hvn
      simpa using
        hdouble X sigma u v hX hu huv hvu hsigma hsigma1 hboundary
  | succ n ih =>
      let w : ℝ := u * (2 : ℝ) ^ (n + 1)
      have huw : u ≤ w := by
        dsimp [w]
        have hpow : 1 ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
        nlinarith [show 0 ≤ u by linarith]
      have hwv : w ≤ v := by simpa [w] using hnv
      have hvw : v ≤ 2 * w := by
        simpa [w, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hvn
      have hwOne : 1 ≤ w := hu.trans huw
      have hleftBoundary : ∀ t ∈ Set.Icc u w,
          regularizedCarlsonZeroDetector X
            ((sigma : ℂ) + Complex.I * t) ≠ 0 := by
        intro t ht
        exact hboundary t ⟨ht.1, ht.2.trans hwv⟩
      have hrightBoundary : ∀ t ∈ Set.Icc w v,
          regularizedCarlsonZeroDetector X
            ((sigma : ℂ) + Complex.I * t) ≠ 0 := by
        intro t ht
        exact hboundary t ⟨huw.trans ht.1, ht.2⟩
      have hleftLower : u * (2 : ℝ) ^ n ≤ w := by
        dsimp [w]
        have hstep : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) :=
          pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
        exact mul_le_mul_of_nonneg_left hstep (by linarith)
      have hleftUpper : w ≤ u * (2 : ℝ) ^ (n + 1) := by rfl
      have hleft := ih w hleftLower hleftUpper hleftBoundary
      have hright :=
        hdouble X sigma w v hX hwOne hwv hvw hsigma hsigma1 hrightBoundary
      let f : ℝ → ℝ := fun t =>
        Real.log ‖carlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖
      have hleftDet : ∀ t ∈ Set.uIcc u w,
          carlsonZeroDetector X
            ((sigma : ℂ) + Complex.I * t) ≠ 0 := by
        intro t ht hzero
        have hreg := hleftBoundary t (by
          simpa only [Set.uIcc_of_le huw] using ht)
        let s : ℂ := (sigma : ℂ) + Complex.I * t
        have hs0 : s ≠ 0 := by
          intro hz
          have hre := congrArg Complex.re hz
          dsimp [s] at hre
          norm_num at hre
          linarith
        have hs1 : s ≠ 1 := by
          intro hz
          have hre := congrArg Complex.re hz
          dsimp [s] at hre
          norm_num at hre
          linarith
        apply hreg
        rw [show regularizedCarlsonZeroDetector X s =
            (s - 1) ^ 2 * carlsonZeroDetector X s from
          regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X hs0 hs1]
        change carlsonZeroDetector X s = 0 at hzero
        simp [hzero]
      have hrightDet : ∀ t ∈ Set.uIcc w v,
          carlsonZeroDetector X
            ((sigma : ℂ) + Complex.I * t) ≠ 0 := by
        intro t ht hzero
        have hreg := hrightBoundary t (by
          simpa only [Set.uIcc_of_le hwv] using ht)
        let s : ℂ := (sigma : ℂ) + Complex.I * t
        have hs0 : s ≠ 0 := by
          intro hz
          have hre := congrArg Complex.re hz
          dsimp [s] at hre
          norm_num at hre
          linarith
        have hs1 : s ≠ 1 := by
          intro hz
          have hre := congrArg Complex.re hz
          dsimp [s] at hre
          norm_num at hre
          linarith
        apply hreg
        rw [show regularizedCarlsonZeroDetector X s =
            (s - 1) ^ 2 * carlsonZeroDetector X s from
          regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X hs0 hs1]
        change carlsonZeroDetector X s = 0 at hzero
        simp [hzero]
      have hleftInt : IntervalIntegrable f MeasureTheory.volume u w := by
        exact intervalIntegrable_log_norm_carlsonZeroDetector
          (ne_of_lt hsigma1) hleftDet
      have hrightInt : IntervalIntegrable f MeasureTheory.volume w v := by
        exact intervalIntegrable_log_norm_carlsonZeroDetector
          (ne_of_lt hsigma1) hrightDet
      calc
        (∫ t in u..v, f t) =
            (∫ t in u..w, f t) + ∫ t in w..v, f t := by
          exact (intervalIntegral.integral_add_adjacent_intervals
            hleftInt hrightInt).symm
        _ ≤ ((∑ k ∈ Finset.range n,
              E X sigma (u * (2 : ℝ) ^ k)
                (u * (2 : ℝ) ^ (k + 1))
                (4 * (u * (2 : ℝ) ^ k))) +
              E X sigma (u * (2 : ℝ) ^ n) w
                (4 * (u * (2 : ℝ) ^ n))) +
            E X sigma w v (4 * w) := add_le_add hleft hright
        _ = (∑ k ∈ Finset.range (n + 1),
              E X sigma (u * (2 : ℝ) ^ k)
                (u * (2 : ℝ) ^ (k + 1))
                (4 * (u * (2 : ℝ) ^ k))) +
            E X sigma (u * (2 : ℝ) ^ (n + 1)) v
              (4 * (u * (2 : ℝ) ^ (n + 1))) := by
          simp only [Finset.sum_range_succ]
          rfl

/-- The sharp arithmetic Carlson endpoint on a geometric cover. -/
theorem
    exists_integral_log_norm_carlsonZeroDetector_le_sharpGeometricCoverExplicit_of_regularizedBoundary :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma u v : ℝ) (n : ℕ),
      1 ≤ X → 1 ≤ u → 1 / 2 < sigma → sigma < 1 →
      u * (2 : ℝ) ^ n ≤ v → v ≤ u * (2 : ℝ) ^ (n + 1) →
      (∀ t ∈ Set.Icc u v,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in u..v,
            Real.log ‖carlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          (∑ k ∈ Finset.range n,
            carlsonLogNormSharpEndpointExplicit
              A 4 X sigma (u * (2 : ℝ) ^ k)
                (u * (2 : ℝ) ^ (k + 1))
                (4 * (u * (2 : ℝ) ^ k))) +
          carlsonLogNormSharpEndpointExplicit
            A 4 X sigma (u * (2 : ℝ) ^ n) v
              (4 * (u * (2 : ℝ) ^ n)) := by
  obtain ⟨A, hA, hdouble⟩ :=
    exists_integral_log_norm_carlsonZeroDetector_le_sharpDoublingIntervalExplicit_of_regularizedBoundary
  refine ⟨A, hA, ?_⟩
  intro X sigma u v n hX hu hsigma hsigma1 hnv hvn hboundary
  exact integral_log_norm_carlsonZeroDetector_le_geometricCoverOfEndpoint
    (fun X sigma u v x =>
      carlsonLogNormSharpEndpointExplicit A 4 X sigma u v x)
    hdouble X sigma u v n hX hu hsigma hsigma1 hnv hvn hboundary

/-- The Carlson left-edge mean-square estimate on a geometric cover starting
at an arbitrary positive height `u`, rather than only at height `1`. -/
theorem
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_geometricCoverExplicit :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma u v : ℝ) (n : ℕ),
      1 ≤ X → 1 ≤ u → 1 / 2 < sigma → sigma < 1 →
      u * (2 : ℝ) ^ n ≤ v → v ≤ u * (2 : ℝ) ^ (n + 1) →
      (∀ t ∈ Set.Icc u v,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in u..v,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          (∑ k ∈ Finset.range n,
            regularizedCarlsonLogNormEndpointExplicit
              A 4 X sigma (u * (2 : ℝ) ^ k)
                (u * (2 : ℝ) ^ (k + 1))
                (4 * (u * (2 : ℝ) ^ k))) +
          regularizedCarlsonLogNormEndpointExplicit
            A 4 X sigma (u * (2 : ℝ) ^ n) v
              (4 * (u * (2 : ℝ) ^ n)) := by
  obtain ⟨A, hA, hdouble⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_doublingInterval
  have hdoubleExplicit : ∀ (X : ℕ) (sigma u v : ℝ),
      1 ≤ X → 1 ≤ u → u ≤ v → v ≤ 2 * u →
      1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc u v,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in u..v,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          regularizedCarlsonLogNormEndpointExplicit
            A 4 X sigma u v (4 * u) := by
    intro X sigma u v hX hu huv hvu hsigma hsigma1 hboundary
    exact (hdouble X sigma u v hX hu huv hvu hsigma hsigma1 hboundary).trans
      (regularizedCarlsonLogNormEndpoint_le_explicit
        (by linarith) hsigma1 hu huv)
  refine ⟨A, hA, ?_⟩
  intro X sigma u v n hX hu hsigma hsigma1 hnv hvn hboundary
  exact
    integral_log_norm_regularizedCarlsonZeroDetector_le_geometricCoverExplicit
      hdoubleExplicit X sigma u v n hX hu hsigma hsigma1 hnv hvn hboundary

/-- The sharp Carlson left-edge estimate on a geometric cover. -/
theorem
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_sharpGeometricCoverExplicit :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma u v : ℝ) (n : ℕ),
      1 ≤ X → 1 ≤ u → 1 / 2 < sigma → sigma < 1 →
      u * (2 : ℝ) ^ n ≤ v → v ≤ u * (2 : ℝ) ^ (n + 1) →
      (∀ t ∈ Set.Icc u v,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in u..v,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          (∑ k ∈ Finset.range n,
            regularizedCarlsonLogNormSharpEndpointExplicit
              A 4 X sigma (u * (2 : ℝ) ^ k)
                (u * (2 : ℝ) ^ (k + 1))
                (4 * (u * (2 : ℝ) ^ k))) +
          regularizedCarlsonLogNormSharpEndpointExplicit
            A 4 X sigma (u * (2 : ℝ) ^ n) v
              (4 * (u * (2 : ℝ) ^ n)) := by
  obtain ⟨A, hA, hdouble⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_sharpDoublingIntervalExplicit
  refine ⟨A, hA, ?_⟩
  intro X sigma u v n hX hu hsigma hsigma1 hnv hvn hboundary
  exact integral_log_norm_regularizedCarlsonZeroDetector_le_geometricCoverOfEndpoint
    (fun X sigma u v x =>
      regularizedCarlsonLogNormSharpEndpointExplicit A 4 X sigma u v x)
    hdouble X sigma u v n hX hu hsigma hsigma1 hnv hvn hboundary

/-- The explicit endpoint sum attached to a geometric Carlson cover. -/
noncomputable def regularizedCarlsonGeometricCoverExplicitBound
    (A : ℝ) (X : ℕ) (sigma u v : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range n,
    regularizedCarlsonLogNormEndpointExplicit
      A 4 X sigma (u * (2 : ℝ) ^ k)
        (u * (2 : ℝ) ^ (k + 1))
        (4 * (u * (2 : ℝ) ^ k))) +
  regularizedCarlsonLogNormEndpointExplicit
    A 4 X sigma (u * (2 : ℝ) ^ n) v
      (4 * (u * (2 : ℝ) ^ n))

/-- The sharp endpoint sum attached to a geometric Carlson cover. -/
noncomputable def regularizedCarlsonSharpGeometricCoverExplicitBound
    (A : ℝ) (X : ℕ) (sigma u v : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range n,
    regularizedCarlsonLogNormSharpEndpointExplicit
      A 4 X sigma (u * (2 : ℝ) ^ k)
        (u * (2 : ℝ) ^ (k + 1))
        (4 * (u * (2 : ℝ) ^ k))) +
  regularizedCarlsonLogNormSharpEndpointExplicit
    A 4 X sigma (u * (2 : ℝ) ^ n) v
      (4 * (u * (2 : ℝ) ^ n))

/-- The arithmetic sharp endpoint sum, with the elementary `(s - 1)^2`
regularization factor omitted because it cancels between the vertical edges. -/
noncomputable def carlsonSharpGeometricCoverExplicitBound
    (A : ℝ) (X : ℕ) (sigma u v : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range n,
    carlsonLogNormSharpEndpointExplicit
      A 4 X sigma (u * (2 : ℝ) ^ k)
        (u * (2 : ℝ) ^ (k + 1))
        (4 * (u * (2 : ℝ) ^ k))) +
  carlsonLogNormSharpEndpointExplicit
    A 4 X sigma (u * (2 : ℝ) ^ n) v
      (4 * (u * (2 : ℝ) ^ n))

/-- Full pre-asymptotic Carlson certificate: the weighted zero-density count
is bounded by a fixed low-zero term, the explicit geometric-cover mean-square
endpoints, and the explicit horizontal/right boundary contribution. -/
theorem
    exists_regularizedCarlson_fixedRight_count_le_geometricCover_add_explicit_boundary :
    ∃ A C₁ C₂ : ℝ, 0 ≤ A ∧ 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {X : ℕ}, 1 ≤ X → ∀ {theta sigma T : ℝ},
        1 / 2 < theta → theta < sigma → sigma < 1 → 6 ≤ T →
        ∃ x0 y0 y1 : ℝ, ∃ n : ℕ,
          theta < x0 ∧ x0 < sigma ∧ x0 < 4 ∧
          5 ≤ y0 ∧ y0 ≤ 6 ∧
          T < y1 ∧ y1 ≤ T + 5 / 4 ∧ y0 < y1 ∧
          y0 * (2 : ℝ) ^ n ≤ y1 ∧
          y1 ≤ y0 * (2 : ℝ) ^ (n + 1) ∧
          (2 * Real.pi) * (sigma - x0) *
              (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
            (2 * Real.pi) * (sigma - x0) *
                ExplicitFormulaAux.globalZeroMultiplicity 6 +
              regularizedCarlsonGeometricCoverExplicitBound
                A X x0 y0 y1 n +
              (4 - x0) ^ 2 *
                (regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5 +
                  regularizedCarlsonHorizontalLogDerivMajorant
                    C₁ C₂ X (T + 1 / 4)) +
              (4 - x0) * (3 * Real.pi) -
              (y1 - y0) * Real.log (56 / 81 : ℝ) := by
  obtain ⟨A, hA, hcover⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_geometricCoverExplicit
  obtain ⟨C₁, C₂, hC₁, hC₂, hcertificate⟩ :=
    exists_regularizedCarlson_fixedRight_count_le_left_add_explicit_boundary
  refine ⟨A, C₁, C₂, hA, hC₁, hC₂, ?_⟩
  intro X hX theta sigma T htheta hthetaSigma hsigmaOne hT
  rcases hcertificate hX htheta hthetaSigma hsigmaOne hT with
    ⟨x0, y0, y1,
      hx0Lower, hx0Upper, hx04,
      hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
      hleft, hcount⟩
  have hy0Pos : 0 < y0 := by linarith
  have hratio : 1 ≤ y1 / y0 := by
    rw [le_div_iff₀ hy0Pos]
    linarith
  obtain ⟨n, hnLower, hnUpper⟩ :=
    exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hnv : y0 * (2 : ℝ) ^ n ≤ y1 := by
    have h := (le_div_iff₀ hy0Pos).mp hnLower
    simpa [mul_comm] using h
  have hvn : y1 ≤ y0 * (2 : ℝ) ^ (n + 1) := by
    have h := (div_lt_iff₀ hy0Pos).mp hnUpper
    exact (by simpa [mul_comm] using h.le)
  have hx0Half : 1 / 2 < x0 := htheta.trans hx0Lower
  have hx0One : x0 < 1 := hx0Upper.trans hsigmaOne
  have hleft' : ∀ t ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht
    simpa [mul_comm] using hleft t ht
  have hleftBound :
      (∫ t in y0..y1,
          Real.log ‖regularizedCarlsonZeroDetector X
            ((x0 : ℂ) + (t : ℂ) * Complex.I)‖) ≤
        (∑ k ∈ Finset.range n,
          regularizedCarlsonLogNormEndpointExplicit
            A 4 X x0 (y0 * (2 : ℝ) ^ k)
              (y0 * (2 : ℝ) ^ (k + 1))
              (4 * (y0 * (2 : ℝ) ^ k))) +
        regularizedCarlsonLogNormEndpointExplicit
          A 4 X x0 (y0 * (2 : ℝ) ^ n) y1
            (4 * (y0 * (2 : ℝ) ^ n)) := by
    simpa only [mul_comm Complex.I] using
      (hcover X x0 y0 y1 n hX (by linarith) hx0Half hx0One
        hnv hvn hleft')
  refine ⟨x0, y0, y1, n,
    hx0Lower, hx0Upper, hx04,
    hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
    hnv, hvn, ?_⟩
  dsimp [regularizedCarlsonGeometricCoverExplicitBound] at hleftBound ⊢
  linarith

/-- Sharp pre-asymptotic Carlson certificate.  Unlike the legacy endpoint,
the left-edge contribution preserves the two scales required for Carlson's
`4σ(1-σ)` exponent. -/
theorem
    exists_regularizedCarlson_fixedRight_count_le_sharpGeometricCover_add_explicit_boundary :
    ∃ A C₁ C₂ : ℝ, 0 ≤ A ∧ 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {X : ℕ}, 1 ≤ X → ∀ {theta sigma T : ℝ},
        1 / 2 < theta → theta < sigma → sigma < 1 → 6 ≤ T →
        ∃ x0 y0 y1 : ℝ, ∃ n : ℕ,
          theta < x0 ∧ x0 < sigma ∧ x0 < 4 ∧
          5 ≤ y0 ∧ y0 ≤ 6 ∧
          T < y1 ∧ y1 ≤ T + 5 / 4 ∧ y0 < y1 ∧
          y0 * (2 : ℝ) ^ n ≤ y1 ∧
          y1 ≤ y0 * (2 : ℝ) ^ (n + 1) ∧
          (2 * Real.pi) * (sigma - x0) *
              (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
            (2 * Real.pi) * (sigma - x0) *
                ExplicitFormulaAux.globalZeroMultiplicity 6 +
              regularizedCarlsonSharpGeometricCoverExplicitBound
                A X x0 y0 y1 n +
              (4 - x0) ^ 2 *
                (regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5 +
                  regularizedCarlsonHorizontalLogDerivMajorant
                    C₁ C₂ X (T + 1 / 4)) +
              (4 - x0) * (3 * Real.pi) -
              (y1 - y0) * Real.log (56 / 81 : ℝ) := by
  obtain ⟨A, hA, hcover⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_sharpGeometricCoverExplicit
  obtain ⟨C₁, C₂, hC₁, hC₂, hcertificate⟩ :=
    exists_regularizedCarlson_fixedRight_count_le_left_add_explicit_boundary
  refine ⟨A, C₁, C₂, hA, hC₁, hC₂, ?_⟩
  intro X hX theta sigma T htheta hthetaSigma hsigmaOne hT
  rcases hcertificate hX htheta hthetaSigma hsigmaOne hT with
    ⟨x0, y0, y1,
      hx0Lower, hx0Upper, hx04,
      hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
      hleft, hcount⟩
  have hy0Pos : 0 < y0 := by linarith
  have hratio : 1 ≤ y1 / y0 := by
    rw [le_div_iff₀ hy0Pos]
    linarith
  obtain ⟨n, hnLower, hnUpper⟩ :=
    exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hnv : y0 * (2 : ℝ) ^ n ≤ y1 := by
    have h := (le_div_iff₀ hy0Pos).mp hnLower
    simpa [mul_comm] using h
  have hvn : y1 ≤ y0 * (2 : ℝ) ^ (n + 1) := by
    have h := (div_lt_iff₀ hy0Pos).mp hnUpper
    exact (by simpa [mul_comm] using h.le)
  have hx0Half : 1 / 2 < x0 := htheta.trans hx0Lower
  have hx0One : x0 < 1 := hx0Upper.trans hsigmaOne
  have hleft' : ∀ t ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht
    simpa [mul_comm] using hleft t ht
  have hleftBound :=
    hcover X x0 y0 y1 n hX (by linarith) hx0Half hx0One
      hnv hvn hleft'
  have hleftBound' :
      (∫ t in y0..y1,
          Real.log ‖regularizedCarlsonZeroDetector X
            ((x0 : ℂ) + (t : ℂ) * Complex.I)‖) ≤
        (∑ k ∈ Finset.range n,
          regularizedCarlsonLogNormSharpEndpointExplicit
            A 4 X x0 (y0 * (2 : ℝ) ^ k)
              (y0 * (2 : ℝ) ^ (k + 1))
              (4 * (y0 * (2 : ℝ) ^ k))) +
        regularizedCarlsonLogNormSharpEndpointExplicit
          A 4 X x0 (y0 * (2 : ℝ) ^ n) y1
            (4 * (y0 * (2 : ℝ) ^ n)) := by
    simpa only [mul_comm Complex.I] using hleftBound
  refine ⟨x0, y0, y1, n,
    hx0Lower, hx0Upper, hx04,
    hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
    hnv, hvn, ?_⟩
  dsimp [regularizedCarlsonSharpGeometricCoverExplicitBound]
    at hleftBound' ⊢
  linarith

/-- Sharp pre-asymptotic Carlson certificate with the auxiliary left edge
confined to `(theta, eta)`, independently of the target counting line
`sigma`. -/
theorem
    exists_regularizedCarlson_fixedRight_count_le_sharpGeometricCover_add_explicit_boundary_of_leftWindow :
    ∃ A C₁ C₂ : ℝ, 0 ≤ A ∧ 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {X : ℕ}, 1 ≤ X → ∀ {theta eta sigma T : ℝ},
        1 / 2 < theta → theta < eta → eta ≤ sigma → sigma < 1 → 6 ≤ T →
        ∃ x0 y0 y1 : ℝ, ∃ n : ℕ,
          theta < x0 ∧ x0 < eta ∧ x0 < sigma ∧ x0 < 4 ∧
          5 ≤ y0 ∧ y0 ≤ 6 ∧
          T < y1 ∧ y1 ≤ T + 5 / 4 ∧ y0 < y1 ∧
          y0 * (2 : ℝ) ^ n ≤ y1 ∧
          y1 ≤ y0 * (2 : ℝ) ^ (n + 1) ∧
          (2 * Real.pi) * (sigma - x0) *
              (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
            (2 * Real.pi) * (sigma - x0) *
                ExplicitFormulaAux.globalZeroMultiplicity 6 +
              regularizedCarlsonSharpGeometricCoverExplicitBound
                A X x0 y0 y1 n +
              (4 - x0) ^ 2 *
                (regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5 +
                  regularizedCarlsonHorizontalLogDerivMajorant
                    C₁ C₂ X (T + 1 / 4)) +
              (4 - x0) * (3 * Real.pi) -
              (y1 - y0) * Real.log (56 / 81 : ℝ) := by
  obtain ⟨A, hA, hcover⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_sharpGeometricCoverExplicit
  obtain ⟨C₁, C₂, hC₁, hC₂, hcertificate⟩ :=
    exists_regularizedCarlson_fixedRight_count_le_left_add_explicit_boundary_of_leftWindow
  refine ⟨A, C₁, C₂, hA, hC₁, hC₂, ?_⟩
  intro X hX theta eta sigma T htheta hthetaEta hetaSigma hsigmaOne hT
  rcases hcertificate hX htheta hthetaEta hetaSigma hsigmaOne hT with
    ⟨x0, y0, y1,
      hx0Lower, hx0Eta, hx0Sigma, hx04,
      hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
      hleft, hcount⟩
  have hy0Pos : 0 < y0 := by linarith
  have hratio : 1 ≤ y1 / y0 := by
    rw [le_div_iff₀ hy0Pos]
    linarith
  obtain ⟨n, hnLower, hnUpper⟩ :=
    exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hnv : y0 * (2 : ℝ) ^ n ≤ y1 := by
    have h := (le_div_iff₀ hy0Pos).mp hnLower
    simpa [mul_comm] using h
  have hvn : y1 ≤ y0 * (2 : ℝ) ^ (n + 1) := by
    have h := (div_lt_iff₀ hy0Pos).mp hnUpper
    exact (by simpa [mul_comm] using h.le)
  have hx0Half : 1 / 2 < x0 := htheta.trans hx0Lower
  have hx0One : x0 < 1 := hx0Sigma.trans hsigmaOne
  have hleft' : ∀ t ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht
    simpa [mul_comm] using hleft t ht
  have hleftBound :=
    hcover X x0 y0 y1 n hX (by linarith) hx0Half hx0One
      hnv hvn hleft'
  have hleftBound' :
      (∫ t in y0..y1,
          Real.log ‖regularizedCarlsonZeroDetector X
            ((x0 : ℂ) + (t : ℂ) * Complex.I)‖) ≤
        (∑ k ∈ Finset.range n,
          regularizedCarlsonLogNormSharpEndpointExplicit
            A 4 X x0 (y0 * (2 : ℝ) ^ k)
              (y0 * (2 : ℝ) ^ (k + 1))
              (4 * (y0 * (2 : ℝ) ^ k))) +
        regularizedCarlsonLogNormSharpEndpointExplicit
          A 4 X x0 (y0 * (2 : ℝ) ^ n) y1
            (4 * (y0 * (2 : ℝ) ^ n)) := by
    simpa only [mul_comm Complex.I] using hleftBound
  refine ⟨x0, y0, y1, n,
    hx0Lower, hx0Eta, hx0Sigma, hx04,
    hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
    hnv, hvn, ?_⟩
  dsimp [regularizedCarlsonSharpGeometricCoverExplicitBound]
    at hleftBound' ⊢
  linarith

/-- Carlson's sharp pre-asymptotic certificate after exact cancellation of
the elementary `(s - 1)^2` regularization factor between the two vertical
edges.  This removes the spurious `T log T` term from the contour bound. -/
theorem
    exists_regularizedCarlson_fixedRight_count_le_cancelledSharpGeometricCover_add_explicit_boundary_of_leftWindow :
    ∃ A C₁ C₂ : ℝ, 0 ≤ A ∧ 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {X : ℕ}, 1 ≤ X → ∀ {theta eta sigma T : ℝ},
        1 / 2 < theta → theta < eta → eta ≤ sigma → sigma < 1 → 6 ≤ T →
        ∃ x0 y0 y1 : ℝ, ∃ n : ℕ,
          theta < x0 ∧ x0 < eta ∧ x0 < sigma ∧ x0 < 4 ∧
          5 ≤ y0 ∧ y0 ≤ 6 ∧
          T < y1 ∧ y1 ≤ T + 5 / 4 ∧ y0 < y1 ∧
          y0 * (2 : ℝ) ^ n ≤ y1 ∧
          y1 ≤ y0 * (2 : ℝ) ^ (n + 1) ∧
          (2 * Real.pi) * (sigma - x0) *
              (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
            (2 * Real.pi) * (sigma - x0) *
                ExplicitFormulaAux.globalZeroMultiplicity 6 +
              carlsonSharpGeometricCoverExplicitBound
                A X x0 y0 y1 n +
              (4 - x0) ^ 2 *
                (regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5 +
                  regularizedCarlsonHorizontalLogDerivMajorant
                    C₁ C₂ X (T + 1 / 4)) +
              (4 - x0) * (3 * Real.pi) -
              (y1 - y0) * Real.log (56 / 81 : ℝ) := by
  obtain ⟨A, hA, hcover⟩ :=
    exists_integral_log_norm_carlsonZeroDetector_le_sharpGeometricCoverExplicit_of_regularizedBoundary
  obtain ⟨C₁, C₂, hC₁, hC₂, hcertificate⟩ :=
    exists_regularizedCarlson_fixedRight_count_with_explicit_horizontals_of_leftWindow
  refine ⟨A, C₁, C₂, hA, hC₁, hC₂, ?_⟩
  intro X hX theta eta sigma T htheta hthetaEta hetaSigma hsigmaOne hT
  rcases hcertificate hX htheta hthetaEta hetaSigma hsigmaOne hT with
    ⟨x0, y0, y1,
      hx0Lower, hx0Eta, hx0Sigma, hx04,
      hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
      hleft, hright, hbottom, htop, hcount,
      hbottomBound, htopBound⟩
  have hy0Pos : 0 < y0 := by linarith
  have hratio : 1 ≤ y1 / y0 := by
    rw [le_div_iff₀ hy0Pos]
    linarith
  obtain ⟨n, hnLower, hnUpper⟩ :=
    exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hnv : y0 * (2 : ℝ) ^ n ≤ y1 := by
    have h := (le_div_iff₀ hy0Pos).mp hnLower
    simpa [mul_comm] using h
  have hvn : y1 ≤ y0 * (2 : ℝ) ^ (n + 1) := by
    have h := (div_lt_iff₀ hy0Pos).mp hnUpper
    exact (by simpa [mul_comm] using h.le)
  have hx0Half : 1 / 2 < x0 := htheta.trans hx0Lower
  have hx0One : x0 < 1 := hx0Sigma.trans hsigmaOne
  have hleftI : ∀ t ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht
    simpa [mul_comm] using hleft t ht
  have hdetI : ∀ t ∈ Set.Icc y0 y1,
      carlsonZeroDetector X
        ((x0 : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht hzero
    let s : ℂ := (x0 : ℂ) + Complex.I * t
    have hs0 : s ≠ 0 := by
      intro hz
      have hre := congrArg Complex.re hz
      dsimp [s] at hre
      norm_num at hre
      linarith
    have hs1 : s ≠ 1 := by
      intro hz
      have hre := congrArg Complex.re hz
      dsimp [s] at hre
      norm_num at hre
      linarith
    apply hleftI t ht
    rw [show regularizedCarlsonZeroDetector X s =
        (s - 1) ^ 2 * carlsonZeroDetector X s from
      regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X hs0 hs1]
    change carlsonZeroDetector X s = 0 at hzero
    simp [hzero]
  have hleftBound :=
    hcover X x0 y0 y1 n hX (by linarith) hx0Half hx0One
      hnv hvn hleftI
  have hleftBound' :
      (∫ t in y0..y1,
          Real.log ‖carlsonZeroDetector X
            ((x0 : ℂ) + (t : ℂ) * Complex.I)‖) ≤
        carlsonSharpGeometricCoverExplicitBound
          A X x0 y0 y1 n := by
    dsimp [carlsonSharpGeometricCoverExplicitBound]
    simpa only [mul_comm Complex.I] using hleftBound
  have hgeomCont : Continuous (fun t : ℝ =>
      Real.log ‖(x0 : ℂ) + (t : ℂ) * Complex.I - 1‖) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : (x0 : ℂ) + (t : ℂ) * Complex.I - 1 ≠ 0 := by
      intro hz
      have hre := congrArg Complex.re hz
      norm_num at hre
      linarith
    have hmap : ContinuousAt
        (fun u : ℝ => (x0 : ℂ) + (u : ℂ) * Complex.I - 1) t := by
      fun_prop
    have hlog : ContinuousAt Real.log
        ‖(x0 : ℂ) + (t : ℂ) * Complex.I - 1‖ :=
      Real.continuousAt_log (norm_ne_zero_iff.mpr hne)
    exact hlog.comp_of_eq
      (continuous_norm.continuousAt.comp_of_eq hmap rfl) rfl
  have hgeomInt : IntervalIntegrable (fun t : ℝ =>
      Real.log ‖(x0 : ℂ) + (t : ℂ) * Complex.I - 1‖)
      MeasureTheory.volume y0 y1 := hgeomCont.intervalIntegrable y0 y1
  have hdetU : ∀ t ∈ Set.uIcc y0 y1,
      carlsonZeroDetector X
        ((x0 : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht
    exact hdetI t (by simpa only [Set.uIcc_of_le hy01.le] using ht)
  have hdetIntI := intervalIntegrable_log_norm_carlsonZeroDetector
    (X := X) (sigma := x0) (a := y0) (b := y1)
    (ne_of_lt hx0One) hdetU
  have hdetInt : IntervalIntegrable (fun t : ℝ =>
      Real.log ‖carlsonZeroDetector X
        ((x0 : ℂ) + (t : ℂ) * Complex.I)‖)
      MeasureTheory.volume y0 y1 := by
    simpa only [mul_comm Complex.I] using hdetIntI
  have hleftEq :
      (∫ t in y0..y1,
          Real.log ‖regularizedCarlsonZeroDetector X
            ((x0 : ℂ) + (t : ℂ) * Complex.I)‖) =
        2 * (∫ t in y0..y1,
          Real.log ‖(x0 : ℂ) + (t : ℂ) * Complex.I - 1‖) +
        ∫ t in y0..y1,
          Real.log ‖carlsonZeroDetector X
            ((x0 : ℂ) + (t : ℂ) * Complex.I)‖ := by
    calc
      (∫ t in y0..y1,
          Real.log ‖regularizedCarlsonZeroDetector X
            ((x0 : ℂ) + (t : ℂ) * Complex.I)‖) =
          ∫ t in y0..y1,
            (2 * Real.log ‖(x0 : ℂ) + (t : ℂ) * Complex.I - 1‖ +
              Real.log ‖carlsonZeroDetector X
                ((x0 : ℂ) + (t : ℂ) * Complex.I)‖) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htIcc : t ∈ Set.Icc y0 y1 := by
          simpa only [Set.uIcc_of_le hy01.le] using ht
        let s : ℂ := (x0 : ℂ) + (t : ℂ) * Complex.I
        have hs0 : s ≠ 0 := by
          intro hz
          have hre := congrArg Complex.re hz
          dsimp [s] at hre
          norm_num at hre
          linarith
        have hs1 : s ≠ 1 := by
          intro hz
          have hre := congrArg Complex.re hz
          dsimp [s] at hre
          norm_num at hre
          linarith
        have hdet : carlsonZeroDetector X s ≠ 0 := by
          simpa [s, mul_comm] using hdetI t htIcc
        exact log_norm_regularizedCarlsonZeroDetector_eq_two_log_norm_sub_one_add
          X hs0 hs1 hdet
      _ = 2 * (∫ t in y0..y1,
            Real.log ‖(x0 : ℂ) + (t : ℂ) * Complex.I - 1‖) +
          ∫ t in y0..y1,
            Real.log ‖carlsonZeroDetector X
              ((x0 : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [intervalIntegral.integral_add (hgeomInt.const_mul 2) hdetInt,
          intervalIntegral.integral_const_mul]
  let M0 := regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5
  let M1 := regularizedCarlsonHorizontalLogDerivMajorant
    C₁ C₂ X (T + 1 / 4)
  have hM0 : 0 ≤ M0 :=
    (norm_nonneg _).trans (hbottomBound x0 ⟨le_rfl, hx04.le⟩)
  have hM1 : 0 ≤ M1 :=
    (norm_nonneg _).trans (htopBound x0 ⟨le_rfl, hx04.le⟩)
  have hremaining :=
    regularizedCarlsonLittlewoodRemainingEdges_fixedRight_le_of_horizontalBounds_with_subOne
      hX hx04.le hy01.le hM0 hM1 hbottomBound htopBound
  have hgeom := integral_log_norm_subOne_left_le_fixedRight
    hx0Half hx0One hy01.le
  have hremaining' :
      regularizedCarlsonLittlewoodRemainingEdges X x0 4 y0 y1 ≤
        (4 - x0) ^ 2 *
            (regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5 +
              regularizedCarlsonHorizontalLogDerivMajorant
                C₁ C₂ X (T + 1 / 4)) +
          (4 - x0) * (3 * Real.pi) -
          2 * (∫ y in y0..y1,
            Real.log ‖(4 : ℂ) + (y : ℂ) * Complex.I - 1‖) -
          (y1 - y0) * Real.log (56 / 81 : ℝ) := by
    simpa only [mul_comm Complex.I] using hremaining
  have hgeom' :
      (∫ y in y0..y1,
          Real.log ‖(x0 : ℂ) + (y : ℂ) * Complex.I - 1‖) ≤
        ∫ y in y0..y1,
          Real.log ‖(4 : ℂ) + (y : ℂ) * Complex.I - 1‖ := by
    simpa only [mul_comm Complex.I] using hgeom
  have hform := regularizedCarlsonLittlewoodFourEdges_eq_logNormFormDef
    ((by norm_num : (0 : ℝ) < 1 / 2).trans hx0Half) hx04 hy01
    hleft hright hbottom htop
  rw [hform,
    regularizedCarlsonLittlewoodLogNormForm_eq_left_add_remaining] at hcount
  refine ⟨x0, y0, y1, n,
    hx0Lower, hx0Eta, hx0Sigma, hx04,
    hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
    hnv, hvn, ?_⟩
  dsimp [M0, M1] at hremaining ⊢
  linarith

/-- Carlson's sharp pre-asymptotic certificate with a height-uniform right-edge
bound and exact cancellation of the elementary regularization terms.  Unlike
the earlier coarse certificate, this leaves a fixed constant instead of an
`O(T)` contribution. -/
theorem
    exists_regularizedCarlson_fixedRight_count_le_cancelledSharpGeometricCover_add_explicit_boundary_of_leftWindow_constantRight :
    ∃ A C₁ C₂ : ℝ, 0 ≤ A ∧ 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {X : ℕ}, 1 ≤ X → ∀ {theta eta sigma T : ℝ},
        1 / 2 < theta → theta < eta → eta ≤ sigma → sigma < 1 → 6 ≤ T →
        ∃ x0 y0 y1 : ℝ, ∃ n : ℕ,
          theta < x0 ∧ x0 < eta ∧ x0 < sigma ∧ x0 < 4 ∧
          5 ≤ y0 ∧ y0 ≤ 6 ∧
          T < y1 ∧ y1 ≤ T + 5 / 4 ∧ y0 < y1 ∧
          y0 * (2 : ℝ) ^ n ≤ y1 ∧
          y1 ≤ y0 * (2 : ℝ) ^ (n + 1) ∧
          (2 * Real.pi) * (sigma - x0) *
              (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
            (2 * Real.pi) * (sigma - x0) *
                ExplicitFormulaAux.globalZeroMultiplicity 6 +
              carlsonSharpGeometricCoverExplicitBound
                A X x0 y0 y1 n +
              (4 - x0) ^ 2 *
                (regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5 +
                  regularizedCarlsonHorizontalLogDerivMajorant
                    C₁ C₂ X (T + 1 / 4)) +
              (4 - x0) * (3 * Real.pi) +
              125 / 18 := by
  obtain ⟨A, hA, hcover⟩ :=
    exists_integral_log_norm_carlsonZeroDetector_le_sharpGeometricCoverExplicit_of_regularizedBoundary
  obtain ⟨C₁, C₂, hC₁, hC₂, hcertificate⟩ :=
    exists_regularizedCarlson_fixedRight_count_with_explicit_horizontals_of_leftWindow
  refine ⟨A, C₁, C₂, hA, hC₁, hC₂, ?_⟩
  intro X hX theta eta sigma T htheta hthetaEta hetaSigma hsigmaOne hT
  rcases hcertificate hX htheta hthetaEta hetaSigma hsigmaOne hT with
    ⟨x0, y0, y1,
      hx0Lower, hx0Eta, hx0Sigma, hx04,
      hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
      hleft, hright, hbottom, htop, hcount,
      hbottomBound, htopBound⟩
  have hy0Pos : 0 < y0 := by linarith
  have hratio : 1 ≤ y1 / y0 := by
    rw [le_div_iff₀ hy0Pos]
    linarith
  obtain ⟨n, hnLower, hnUpper⟩ :=
    exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hnv : y0 * (2 : ℝ) ^ n ≤ y1 := by
    have h := (le_div_iff₀ hy0Pos).mp hnLower
    simpa [mul_comm] using h
  have hvn : y1 ≤ y0 * (2 : ℝ) ^ (n + 1) := by
    have h := (div_lt_iff₀ hy0Pos).mp hnUpper
    exact (by simpa [mul_comm] using h.le)
  have hx0Half : 1 / 2 < x0 := htheta.trans hx0Lower
  have hx0One : x0 < 1 := hx0Sigma.trans hsigmaOne
  have hleftI : ∀ t ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht
    simpa [mul_comm] using hleft t ht
  have hdetI : ∀ t ∈ Set.Icc y0 y1,
      carlsonZeroDetector X
        ((x0 : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht hzero
    let s : ℂ := (x0 : ℂ) + Complex.I * t
    have hs0 : s ≠ 0 := by
      intro hz
      have hre := congrArg Complex.re hz
      dsimp [s] at hre
      norm_num at hre
      linarith
    have hs1 : s ≠ 1 := by
      intro hz
      have hre := congrArg Complex.re hz
      dsimp [s] at hre
      norm_num at hre
      linarith
    apply hleftI t ht
    rw [show regularizedCarlsonZeroDetector X s =
        (s - 1) ^ 2 * carlsonZeroDetector X s from
      regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X hs0 hs1]
    change carlsonZeroDetector X s = 0 at hzero
    simp [hzero]
  have hleftBound :=
    hcover X x0 y0 y1 n hX (by linarith) hx0Half hx0One
      hnv hvn hleftI
  have hleftBound' :
      (∫ t in y0..y1,
          Real.log ‖carlsonZeroDetector X
            ((x0 : ℂ) + (t : ℂ) * Complex.I)‖) ≤
        carlsonSharpGeometricCoverExplicitBound
          A X x0 y0 y1 n := by
    dsimp [carlsonSharpGeometricCoverExplicitBound]
    simpa only [mul_comm Complex.I] using hleftBound
  have hgeomCont : Continuous (fun t : ℝ =>
      Real.log ‖(x0 : ℂ) + (t : ℂ) * Complex.I - 1‖) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : (x0 : ℂ) + (t : ℂ) * Complex.I - 1 ≠ 0 := by
      intro hz
      have hre := congrArg Complex.re hz
      norm_num at hre
      linarith
    have hmap : ContinuousAt
        (fun u : ℝ => (x0 : ℂ) + (u : ℂ) * Complex.I - 1) t := by
      fun_prop
    have hlog : ContinuousAt Real.log
        ‖(x0 : ℂ) + (t : ℂ) * Complex.I - 1‖ :=
      Real.continuousAt_log (norm_ne_zero_iff.mpr hne)
    exact hlog.comp_of_eq
      (continuous_norm.continuousAt.comp_of_eq hmap rfl) rfl
  have hgeomInt : IntervalIntegrable (fun t : ℝ =>
      Real.log ‖(x0 : ℂ) + (t : ℂ) * Complex.I - 1‖)
      MeasureTheory.volume y0 y1 := hgeomCont.intervalIntegrable y0 y1
  have hdetU : ∀ t ∈ Set.uIcc y0 y1,
      carlsonZeroDetector X
        ((x0 : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht
    exact hdetI t (by simpa only [Set.uIcc_of_le hy01.le] using ht)
  have hdetIntI := intervalIntegrable_log_norm_carlsonZeroDetector
    (X := X) (sigma := x0) (a := y0) (b := y1)
    (ne_of_lt hx0One) hdetU
  have hdetInt : IntervalIntegrable (fun t : ℝ =>
      Real.log ‖carlsonZeroDetector X
        ((x0 : ℂ) + (t : ℂ) * Complex.I)‖)
      MeasureTheory.volume y0 y1 := by
    simpa only [mul_comm Complex.I] using hdetIntI
  have hleftEq :
      (∫ t in y0..y1,
          Real.log ‖regularizedCarlsonZeroDetector X
            ((x0 : ℂ) + (t : ℂ) * Complex.I)‖) =
        2 * (∫ t in y0..y1,
          Real.log ‖(x0 : ℂ) + (t : ℂ) * Complex.I - 1‖) +
        ∫ t in y0..y1,
          Real.log ‖carlsonZeroDetector X
            ((x0 : ℂ) + (t : ℂ) * Complex.I)‖ := by
    calc
      (∫ t in y0..y1,
          Real.log ‖regularizedCarlsonZeroDetector X
            ((x0 : ℂ) + (t : ℂ) * Complex.I)‖) =
          ∫ t in y0..y1,
            (2 * Real.log ‖(x0 : ℂ) + (t : ℂ) * Complex.I - 1‖ +
              Real.log ‖carlsonZeroDetector X
                ((x0 : ℂ) + (t : ℂ) * Complex.I)‖) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htIcc : t ∈ Set.Icc y0 y1 := by
          simpa only [Set.uIcc_of_le hy01.le] using ht
        let s : ℂ := (x0 : ℂ) + (t : ℂ) * Complex.I
        have hs0 : s ≠ 0 := by
          intro hz
          have hre := congrArg Complex.re hz
          dsimp [s] at hre
          norm_num at hre
          linarith
        have hs1 : s ≠ 1 := by
          intro hz
          have hre := congrArg Complex.re hz
          dsimp [s] at hre
          norm_num at hre
          linarith
        have hdet : carlsonZeroDetector X s ≠ 0 := by
          simpa [s, mul_comm] using hdetI t htIcc
        exact log_norm_regularizedCarlsonZeroDetector_eq_two_log_norm_sub_one_add
          X hs0 hs1 hdet
      _ = 2 * (∫ t in y0..y1,
            Real.log ‖(x0 : ℂ) + (t : ℂ) * Complex.I - 1‖) +
          ∫ t in y0..y1,
            Real.log ‖carlsonZeroDetector X
              ((x0 : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [intervalIntegral.integral_add (hgeomInt.const_mul 2) hdetInt,
          intervalIntegral.integral_const_mul]
  let M0 := regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5
  let M1 := regularizedCarlsonHorizontalLogDerivMajorant
    C₁ C₂ X (T + 1 / 4)
  have hM0 : 0 ≤ M0 :=
    (norm_nonneg _).trans (hbottomBound x0 ⟨le_rfl, hx04.le⟩)
  have hM1 : 0 ≤ M1 :=
    (norm_nonneg _).trans (htopBound x0 ⟨le_rfl, hx04.le⟩)
  have hremaining :=
    regularizedCarlsonLittlewoodRemainingEdges_fixedRight_le_of_horizontalBounds_with_subOne_constant
      hX hx04.le hy01.le hM0 hM1 hbottomBound htopBound
  have hgeom := integral_log_norm_subOne_left_le_fixedRight
    hx0Half hx0One hy01.le
  have hremaining' :
      regularizedCarlsonLittlewoodRemainingEdges X x0 4 y0 y1 ≤
        (4 - x0) ^ 2 *
            (regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5 +
              regularizedCarlsonHorizontalLogDerivMajorant
                C₁ C₂ X (T + 1 / 4)) +
          (4 - x0) * (3 * Real.pi) -
          2 * (∫ y in y0..y1,
            Real.log ‖(4 : ℂ) + (y : ℂ) * Complex.I - 1‖) +
          125 / 18 := by
    simpa only [mul_comm Complex.I] using hremaining
  have hgeom' :
      (∫ y in y0..y1,
          Real.log ‖(x0 : ℂ) + (y : ℂ) * Complex.I - 1‖) ≤
        ∫ y in y0..y1,
          Real.log ‖(4 : ℂ) + (y : ℂ) * Complex.I - 1‖ := by
    simpa only [mul_comm Complex.I] using hgeom
  have hform := regularizedCarlsonLittlewoodFourEdges_eq_logNormFormDef
    ((by norm_num : (0 : ℝ) < 1 / 2).trans hx0Half) hx04 hy01
    hleft hright hbottom htop
  rw [hform,
    regularizedCarlsonLittlewoodLogNormForm_eq_left_add_remaining] at hcount
  refine ⟨x0, y0, y1, n,
    hx0Lower, hx0Eta, hx0Sigma, hx04,
    hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
    hnv, hvn, ?_⟩
  dsimp [M0, M1] at hremaining ⊢
  linarith

end CarlsonZeroDensity
end PrimeNumberTheorem
