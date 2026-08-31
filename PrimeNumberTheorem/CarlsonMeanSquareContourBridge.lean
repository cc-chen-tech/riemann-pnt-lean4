import PrimeNumberTheorem.CarlsonHorizontalContour

/-!
# Carlson contour with the actual mollified mean square exposed

This theorem stops before the classical sharp endpoint is substituted.  Its
right-hand side contains the genuine `mollifiedZetaError` second moment, so a
new large-values estimate can enter here without being encoded as a density
conclusion.
-/

open Complex Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The fixed-right Carlson contour after exact cancellation of the
regularizing `(s - 1)^2` factors, with the actual mollified-error mean square
left unevaluated.  This is the analytic replacement point for any Carlson-type
large-values improvement. -/
theorem
    exists_regularizedCarlson_fixedRight_count_le_mollifiedMeanSquare_add_explicit_boundary_of_leftWindow_constantRight :
    ∃ C₁ C₂ : ℝ, 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {X : ℕ}, 1 ≤ X → ∀ {theta eta sigma T : ℝ},
        1 / 2 < theta → theta < eta → eta ≤ sigma → sigma < 1 → 6 ≤ T →
        ∃ x0 y0 y1 : ℝ,
          theta < x0 ∧ x0 < eta ∧ x0 < sigma ∧ x0 < 4 ∧
          5 ≤ y0 ∧ y0 ≤ 6 ∧
          T < y1 ∧ y1 ≤ T + 5 / 4 ∧ y0 < y1 ∧
          (2 * Real.pi) * (sigma - x0) *
              (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
            (2 * Real.pi) * (sigma - x0) *
                ExplicitFormulaAux.globalZeroMultiplicity 6 +
              (∫ t in y0..y1,
                ‖mollifiedZetaError X
                  ((x0 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) +
              (4 - x0) ^ 2 *
                (regularizedCarlsonHorizontalLogDerivMajorant C₁ C₂ X 5 +
                  regularizedCarlsonHorizontalLogDerivMajorant
                    C₁ C₂ X (T + 1 / 4)) +
              (4 - x0) * (3 * Real.pi) +
              125 / 18 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hcertificate⟩ :=
    exists_regularizedCarlson_fixedRight_count_with_explicit_horizontals_of_leftWindow
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro X hX theta eta sigma T htheta hthetaEta hetaSigma hsigmaOne hT
  rcases hcertificate hX htheta hthetaEta hetaSigma hsigmaOne hT with
    ⟨x0, y0, y1,
      hx0Lower, hx0Eta, hx0Sigma, hx04,
      hy0Lower, hy0Upper, hTy1, hy1Upper, hy01,
      hleft, hright, hbottom, htop, hcount,
      hbottomBound, htopBound⟩
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
  have hmeanI := integral_log_norm_carlsonZeroDetector_le_meanSquare
    (X := X) (sigma := x0) (a := y0) (b := y1)
    hy01.le (ne_of_lt hx0One) hdetI
  have hmean :
      (∫ t in y0..y1,
          Real.log ‖carlsonZeroDetector X
            ((x0 : ℂ) + (t : ℂ) * Complex.I)‖) ≤
        ∫ t in y0..y1,
          ‖mollifiedZetaError X
            ((x0 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    simpa only [mul_comm Complex.I] using hmeanI
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
  refine ⟨x0, y0, y1,
    hx0Lower, hx0Eta, hx0Sigma, hx04,
    hy0Lower, hy0Upper, hTy1, hy1Upper, hy01, ?_⟩
  dsimp [M0, M1] at hremaining ⊢
  linarith

end CarlsonZeroDensity
end PrimeNumberTheorem
