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

end CarlsonZeroDensity
end PrimeNumberTheorem
