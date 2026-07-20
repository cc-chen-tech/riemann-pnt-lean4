import PrimeNumberTheorem.CarlsonDetectorCount
import PrimeNumberTheorem.LittlewoodRectangle

open Complex Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The four oriented real edge integrals in Littlewood's weighted rectangle
formula for the regularized Carlson detector. -/
noncomputable def regularizedCarlsonLittlewoodFourEdges
    (X : ℕ) (x0 x1 y0 y1 : ℝ) : ℝ :=
  (∫ x in x0..x1,
      ((((x : ℂ) + (y0 : ℂ) * I - (x0 : ℂ)) *
        logDeriv (regularizedCarlsonZeroDetector X)
          ((x : ℂ) + (y0 : ℂ) * I))).im) -
    (∫ x in x0..x1,
      ((((x : ℂ) + (y1 : ℂ) * I - (x0 : ℂ)) *
        logDeriv (regularizedCarlsonZeroDetector X)
          ((x : ℂ) + (y1 : ℂ) * I))).im) +
    (∫ y in y0..y1,
      ((((x1 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
        logDeriv (regularizedCarlsonZeroDetector X)
          ((x1 : ℂ) + (y : ℂ) * I))).re) -
    (∫ y in y0..y1,
      ((((x0 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
        logDeriv (regularizedCarlsonZeroDetector X)
          ((x0 : ℂ) + (y : ℂ) * I))).re)

/-- Endpoint-cancelled form of the regularized Carlson Littlewood rectangle.
This is the expression whose five remaining terms require quantitative
estimates. -/
noncomputable def regularizedCarlsonLittlewoodLogNormForm
    (X : ℕ) (x0 x1 y0 y1 : ℝ) : ℝ :=
  (∫ x in x0..x1,
      (x - x0) *
        (logDeriv (regularizedCarlsonZeroDetector X)
          ((x : ℂ) + (y0 : ℂ) * I)).im) -
    (∫ x in x0..x1,
      (x - x0) *
        (logDeriv (regularizedCarlsonZeroDetector X)
          ((x : ℂ) + (y1 : ℂ) * I)).im) +
    (x1 - x0) *
      (∫ y in y0..y1,
        (logDeriv (regularizedCarlsonZeroDetector X)
          ((x1 : ℂ) + (y : ℂ) * I)).re) +
    (∫ y in y0..y1,
      Real.log ‖regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + (y : ℂ) * I)‖) -
    (∫ y in y0..y1,
      Real.log ‖regularizedCarlsonZeroDetector X
        ((x1 : ℂ) + (y : ℂ) * I)‖)

/-- The still-uncontrolled part of the endpoint-cancelled Littlewood formula:
the bottom and top horizontal argument terms together with the two right-edge
terms. -/
noncomputable def regularizedCarlsonLittlewoodRemainingEdges
    (X : ℕ) (x0 x1 y0 y1 : ℝ) : ℝ :=
  (∫ x in x0..x1,
      (x - x0) *
        (logDeriv (regularizedCarlsonZeroDetector X)
          ((x : ℂ) + (y0 : ℂ) * I)).im) -
    (∫ x in x0..x1,
      (x - x0) *
        (logDeriv (regularizedCarlsonZeroDetector X)
          ((x : ℂ) + (y1 : ℂ) * I)).im) +
    (x1 - x0) *
      (∫ y in y0..y1,
        (logDeriv (regularizedCarlsonZeroDetector X)
          ((x1 : ℂ) + (y : ℂ) * I)).re) -
    (∫ y in y0..y1,
      Real.log ‖regularizedCarlsonZeroDetector X
        ((x1 : ℂ) + (y : ℂ) * I)‖)

/-- Exact split of the Littlewood log-norm form into the left logarithmic
norm integral and all remaining boundary contributions. -/
theorem regularizedCarlsonLittlewoodLogNormForm_eq_left_add_remaining
    (X : ℕ) (x0 x1 y0 y1 : ℝ) :
    regularizedCarlsonLittlewoodLogNormForm X x0 x1 y0 y1 =
      (∫ y in y0..y1,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I)‖) +
      regularizedCarlsonLittlewoodRemainingEdges X x0 x1 y0 y1 := by
  unfold regularizedCarlsonLittlewoodLogNormForm
    regularizedCarlsonLittlewoodRemainingEdges
  ring

/-- Any upper bound for the left logarithmic norm integral transfers the
Carlson count reduction to that bound plus the remaining three edges. -/
theorem zeroDensityCount_le_leftBound_add_remaining
    {X : ℕ} {sigma T x0 x1 y0 y1 leftBound : ℝ}
    (hcount :
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        regularizedCarlsonLittlewoodLogNormForm X x0 x1 y0 y1)
    (hleft :
      (∫ y in y0..y1,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I)‖) ≤ leftBound) :
    (2 * Real.pi) * (sigma - x0) *
        (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
      leftBound +
        regularizedCarlsonLittlewoodRemainingEdges X x0 x1 y0 y1 := by
  rw [regularizedCarlsonLittlewoodLogNormForm_eq_left_add_remaining] at hcount
  linarith

/-- The weighted argument principle specialized to the pole-free Carlson
detector.  The finite divisor support is proved to be exactly the zero set,
and zero-free boundary hypotheses force every counted zero into the strict
interior. -/
theorem boundaryRectIntegral_regularizedCarlsonZeroDetector_eq_zeroMultiplicitySum
    {X : ℕ} (hX : 1 ≤ X) {x0 x1 y0 y1 : ℝ}
    (hx0 : 0 < x0) (hx01 : x0 < x1) (hy01 : y0 < y1)
    (hleft : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x1 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hbottom : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    MathlibAux.boundaryRectIntegral
        (fun z : ℂ => (z - (x0 : ℂ)) *
          logDeriv (regularizedCarlsonZeroDetector X) z)
        x0 x1 y0 y1 =
      (2 * Real.pi * I) *
        ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
            X x0 x1 y0 y1,
          (rho - (x0 : ℂ)) *
            (analyticOrderNatAt
              (regularizedCarlsonZeroDetector X) rho : ℂ) := by
  classical
  let K : Set ℂ := carlsonDetectorRectangle x0 x1 y0 y1
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X) K
  let P := regularizedCarlsonDetectorRectangleDivisorSupport X x0 x1 y0 y1
  have hPmem : ∀ rho ∈ P, rho ∈ K := by
    intro rho hrho
    have hrhoSupport : rho ∈ D.support := by
      dsimp [P, regularizedCarlsonDetectorRectangleDivisorSupport] at hrho
      exact (D.finiteSupport
        (isCompact_carlsonDetectorRectangle x0 x1 y0 y1)).mem_toFinset.mp hrho
    exact D.supportWithinDomain hrhoSupport
  have hanalytic : AnalyticOnNhd ℂ (regularizedCarlsonZeroDetector X)
      ([[x0, x1]] ×ℂ [[y0, y1]]) := by
    intro z hz
    have hzx : z.re ∈ Set.Icc x0 x1 := by
      simpa only [uIcc_of_le hx01.le] using hz.1
    have hzre : x0 ≤ z.re := hzx.1
    exact analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X z (hx0.trans_le hzre)
  have hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ),
      regularizedCarlsonZeroDetector X z = 0 ↔ z ∈ P := by
    intro z hz
    have hzK : z ∈ K := by
      simpa [K, carlsonDetectorRectangle, uIcc_of_le hx01.le,
        uIcc_of_le hy01.le] using hz
    simpa [P] using
      (mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
        hX hx0 hzK).symm
  have horder : ∀ rho ∈ P,
      analyticOrderAt (regularizedCarlsonZeroDetector X) rho =
        analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho := by
    intro rho hrho
    have hrhoK := hPmem rho hrho
    have hrhore : 0 < rho.re := hx0.trans_le hrhoK.1.1
    have hfinite :=
      analyticOrderAt_regularizedCarlsonZeroDetector_ne_top X hX hrhore
    simpa using (Nat.cast_analyticOrderNatAt hfinite).symm
  have hpoles : ∀ rho ∈ P,
      x0 < rho.re ∧ rho.re < x1 ∧ y0 < rho.im ∧ rho.im < y1 := by
    intro rho hrho
    have hrhoK := hPmem rho hrho
    have hrhoZero : regularizedCarlsonZeroDetector X rho = 0 :=
      (mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
        hX hx0 hrhoK).mp hrho
    have hleftNe : x0 ≠ rho.re := by
      intro heq
      apply hleft rho.im hrhoK.2
      have hpoint : (x0 : ℂ) + (rho.im : ℂ) * I = rho := by
        apply Complex.ext <;> simp [heq]
      rw [hpoint]
      exact hrhoZero
    have hrightNe : rho.re ≠ x1 := by
      intro heq
      apply hright rho.im hrhoK.2
      have hpoint : (x1 : ℂ) + (rho.im : ℂ) * I = rho := by
        apply Complex.ext <;> simp [heq]
      rw [hpoint]
      exact hrhoZero
    have hbottomNe : y0 ≠ rho.im := by
      intro heq
      apply hbottom rho.re hrhoK.1
      have hpoint : (rho.re : ℂ) + (y0 : ℂ) * I = rho := by
        apply Complex.ext <;> simp [heq]
      rw [hpoint]
      exact hrhoZero
    have htopNe : rho.im ≠ y1 := by
      intro heq
      apply htop rho.re hrhoK.1
      have hpoint : (rho.re : ℂ) + (y1 : ℂ) * I = rho := by
        apply Complex.ext <;> simp [heq]
      rw [hpoint]
      exact hrhoZero
    exact ⟨lt_of_le_of_ne hrhoK.1.1 hleftNe,
      lt_of_le_of_ne hrhoK.1.2 hrightNe,
      lt_of_le_of_ne hrhoK.2.1 hbottomNe,
      lt_of_le_of_ne hrhoK.2.2 htopNe⟩
  simpa [P] using
    boundaryRectIntegral_weighted_logDeriv_eq_zeroMultiplicitySum
      P (fun rho => analyticOrderNatAt
        (regularizedCarlsonZeroDetector X) rho) (x0 : ℂ)
      hanalytic hzero horder hpoles

/-- The detector-specific weighted argument principle, expanded into its four
oriented edge integrals.  Analyticity and the zero-free side hypotheses also
discharge all interval-integrability obligations. -/
theorem two_pi_mul_regularizedCarlsonZeroMultiplicityWeightedRealSum_eq_four_edges
    {X : ℕ} (hX : 1 ≤ X) {x0 x1 y0 y1 : ℝ}
    (hx0 : 0 < x0) (hx01 : x0 < x1) (hy01 : y0 < y1)
    (hleft : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x1 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hbottom : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    (2 * Real.pi) *
        ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
            X x0 x1 y0 y1,
          (rho.re - x0) *
            (analyticOrderNatAt
              (regularizedCarlsonZeroDetector X) rho : ℝ) =
      (∫ x in x0..x1,
          ((((x : ℂ) + (y0 : ℂ) * I - (x0 : ℂ)) *
            logDeriv (regularizedCarlsonZeroDetector X)
              ((x : ℂ) + (y0 : ℂ) * I))).im) -
        (∫ x in x0..x1,
          ((((x : ℂ) + (y1 : ℂ) * I - (x0 : ℂ)) *
            logDeriv (regularizedCarlsonZeroDetector X)
              ((x : ℂ) + (y1 : ℂ) * I))).im) +
        (∫ y in y0..y1,
          ((((x1 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
            logDeriv (regularizedCarlsonZeroDetector X)
              ((x1 : ℂ) + (y : ℂ) * I))).re) -
        (∫ y in y0..y1,
          ((((x0 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
            logDeriv (regularizedCarlsonZeroDetector X)
              ((x0 : ℂ) + (y : ℂ) * I))).re) := by
  classical
  let f := regularizedCarlsonZeroDetector X
  have horizontalIntegrable (y : ℝ)
      (hne : ∀ x ∈ Set.Icc x0 x1,
        f ((x : ℂ) + (y : ℂ) * I) ≠ 0) :
      IntervalIntegrable
        (fun x : ℝ =>
          (((x : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
            logDeriv f ((x : ℂ) + (y : ℂ) * I)))
        MeasureTheory.volume x0 x1 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hxIcc : x ∈ Set.Icc x0 x1 := by
      simpa only [uIcc_of_le hx01.le] using hx
    have hanalytic : AnalyticAt ℂ f ((x : ℂ) + (y : ℂ) * I) := by
      dsimp [f]
      exact analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
        (theta := (0 : ℝ)) le_rfl X _ (by
          simpa using hx0.trans_le hxIcc.1)
    have hparam : ContinuousAt
        (fun u : ℝ => (u : ℂ) + (y : ℂ) * I) x := by
      fun_prop
    have hlog : ContinuousAt
        (fun u : ℝ => logDeriv f ((u : ℂ) + (y : ℂ) * I)) x := by
      simpa [Function.comp_def] using
        (ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero
          hanalytic (hne x hxIcc)).continuousAt.comp_of_eq hparam rfl
    exact ((by fun_prop : ContinuousAt
      (fun u : ℝ => (u : ℂ) + (y : ℂ) * I - (x0 : ℂ)) x).mul hlog).continuousWithinAt
  have verticalIntegrable (x : ℝ) (hxpos : 0 < x)
      (hne : ∀ y ∈ Set.Icc y0 y1,
        f ((x : ℂ) + (y : ℂ) * I) ≠ 0) :
      IntervalIntegrable
        (fun y : ℝ =>
          (((x : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
            logDeriv f ((x : ℂ) + (y : ℂ) * I)))
        MeasureTheory.volume y0 y1 := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    have hyIcc : y ∈ Set.Icc y0 y1 := by
      simpa only [uIcc_of_le hy01.le] using hy
    have hanalytic : AnalyticAt ℂ f ((x : ℂ) + (y : ℂ) * I) := by
      dsimp [f]
      exact analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
        (theta := (0 : ℝ)) le_rfl X _ (by simpa using hxpos)
    have hparam : ContinuousAt
        (fun u : ℝ => (x : ℂ) + (u : ℂ) * I) y := by
      fun_prop
    have hlog : ContinuousAt
        (fun u : ℝ => logDeriv f ((x : ℂ) + (u : ℂ) * I)) y := by
      simpa [Function.comp_def] using
        (ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero
          hanalytic (hne y hyIcc)).continuousAt.comp_of_eq hparam rfl
    exact ((by fun_prop : ContinuousAt
      (fun u : ℝ => (x : ℂ) + (u : ℂ) * I - (x0 : ℂ)) y).mul hlog).continuousWithinAt
  have hbottomInt := horizontalIntegrable y0 hbottom
  have htopInt := horizontalIntegrable y1 htop
  have hrightInt := verticalIntegrable x1 (hx0.trans hx01) hright
  have hleftInt := verticalIntegrable x0 hx0 hleft
  have hcontour :=
    boundaryRectIntegral_regularizedCarlsonZeroDetector_eq_zeroMultiplicitySum
      hX hx0 hx01 hy01 hleft hright hbottom htop
  have hedges := im_boundaryRectIntegral_eq_four_edges
    (G := fun z : ℂ => (z - (x0 : ℂ)) *
      logDeriv (regularizedCarlsonZeroDetector X) z)
    hbottomInt htopInt hrightInt hleftInt
  have him := congrArg Complex.im hcontour
  rw [hedges] at him
  have hsumRe :
      (∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
          X x0 x1 y0 y1,
        (rho - (x0 : ℂ)) *
          (analyticOrderNatAt
            (regularizedCarlsonZeroDetector X) rho : ℂ)).re =
        ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
            X x0 x1 y0 y1,
          (rho.re - x0) *
            (analyticOrderNatAt
              (regularizedCarlsonZeroDetector X) rho : ℝ) := by
    simp [Complex.re_sum, Complex.mul_re]
  rw [Complex.mul_im, hsumRe] at him
  simpa [f] using him.symm

/-- The anchored left vertical edge is exactly an endpoint contribution minus
the logarithmic norm integral.  The argument-variation term vanishes because
the edge and the weight have the same real anchor. -/
theorem regularizedCarlsonLittlewood_leftEdge_eq_logNorm
    {X : ℕ} {x0 y0 y1 : ℝ}
    (hx0 : 0 < x0) (hy01 : y0 < y1)
    (hleft : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) :
    (∫ y in y0..y1,
        ((((x0 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
          logDeriv (regularizedCarlsonZeroDetector X)
            ((x0 : ℂ) + (y : ℂ) * I))).re) =
      y1 * Real.log ‖regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y1 : ℂ) * I)‖ -
      y0 * Real.log ‖regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y0 : ℂ) * I)‖ -
      ∫ y in y0..y1,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I)‖ := by
  have hanalytic : ∀ y ∈ [[y0, y1]],
      AnalyticAt ℂ (regularizedCarlsonZeroDetector X)
        ((x0 : ℂ) + I * (y : ℂ)) := by
    intro y _
    exact analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X _ (by simpa using hx0)
  have hne : ∀ y ∈ [[y0, y1]],
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + I * (y : ℂ)) ≠ 0 := by
    intro y hy
    simpa [mul_comm] using
      hleft y (by simpa only [uIcc_of_le hy01.le] using hy)
  simpa [mul_comm] using
    (intervalIntegral_re_weighted_logDeriv_vertical_eq_of_analytic
      (f := regularizedCarlsonZeroDetector X)
      (sigma := x0) (anchor := x0) hanalytic hne)

/-- The right vertical edge splits into argument variation, endpoint values,
and the logarithmic norm integral. -/
theorem regularizedCarlsonLittlewood_rightEdge_eq_logNorm
    {X : ℕ} {x0 x1 y0 y1 : ℝ}
    (hx1 : 0 < x1) (hy01 : y0 < y1)
    (hright : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x1 : ℂ) + (y : ℂ) * I) ≠ 0) :
    (∫ y in y0..y1,
        ((((x1 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
          logDeriv (regularizedCarlsonZeroDetector X)
            ((x1 : ℂ) + (y : ℂ) * I))).re) =
      (x1 - x0) *
        (∫ y in y0..y1,
          (logDeriv (regularizedCarlsonZeroDetector X)
            ((x1 : ℂ) + (y : ℂ) * I)).re) +
      y1 * Real.log ‖regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y1 : ℂ) * I)‖ -
      y0 * Real.log ‖regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y0 : ℂ) * I)‖ -
      ∫ y in y0..y1,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y : ℂ) * I)‖ := by
  have hanalytic : ∀ y ∈ [[y0, y1]],
      AnalyticAt ℂ (regularizedCarlsonZeroDetector X)
        ((x1 : ℂ) + I * (y : ℂ)) := by
    intro y _
    exact analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X _ (by simpa using hx1)
  have hne : ∀ y ∈ [[y0, y1]],
      regularizedCarlsonZeroDetector X
        ((x1 : ℂ) + I * (y : ℂ)) ≠ 0 := by
    intro y hy
    simpa [mul_comm] using
      hright y (by simpa only [uIcc_of_le hy01.le] using hy)
  simpa [mul_comm] using
    (intervalIntegral_re_weighted_logDeriv_vertical_eq_of_analytic
      (f := regularizedCarlsonZeroDetector X)
      (sigma := x1) (anchor := x0) hanalytic hne)

/-- The negative log-norm integral on the fixed right edge `Re(s) = 4` is
bounded by an explicit constant times its length. -/
theorem neg_integral_log_norm_regularizedCarlson_fixedRight_le
    {X : ℕ} (hX : 1 ≤ X) {y0 y1 : ℝ} (hy01 : y0 ≤ y1) :
    -(∫ y in y0..y1,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((4 : ℂ) + I * (y : ℂ))‖) ≤
      -(y1 - y0) * Real.log (56 / 81 : ℝ) := by
  have hboundary : ∀ y ∈ Set.uIcc y0 y1,
      regularizedCarlsonZeroDetector X
        ((4 : ℂ) + I * (y : ℂ)) ≠ 0 := by
    intro y _hy
    apply regularizedCarlsonZeroDetector_ne_zero_of_four_le_re hX
    simp
  have hrightInt :=
    intervalIntegrable_log_norm_regularizedCarlsonZeroDetector
      (X := X) (sigma := 4) (a := y0) (b := y1) (by norm_num) hboundary
  have hconstInt : IntervalIntegrable
      (fun _y : ℝ => Real.log (56 / 81 : ℝ))
      MeasureTheory.volume y0 y1 := intervalIntegrable_const
  have hpoint (y : ℝ) (_hy : y ∈ Set.Icc y0 y1) :
      Real.log (56 / 81 : ℝ) ≤
        Real.log ‖regularizedCarlsonZeroDetector X
          ((4 : ℂ) + I * (y : ℂ))‖ := by
    let s : ℂ := (4 : ℂ) + I * (y : ℂ)
    have hs : 4 ≤ s.re := by simp [s]
    have hbase :=
      log_fiftySix_div_eightyOne_le_log_norm_regularized_of_four_le_re hX hs
    have hnorm : 1 ≤ ‖s - 1‖ := by
      calc
        (1 : ℝ) ≤ 3 := by norm_num
        _ = |(s - 1).re| := by norm_num [s]
        _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
    have hlog : 0 ≤ Real.log ‖s - 1‖ := Real.log_nonneg hnorm
    dsimp [s] at hbase ⊢
    linarith
  have hlower := intervalIntegral.integral_mono_on
    hy01 hconstInt hrightInt hpoint
  have hlower' :
      (y1 - y0) * Real.log (56 / 81 : ℝ) ≤
        ∫ y in y0..y1,
          Real.log ‖regularizedCarlsonZeroDetector X
            ((4 : ℂ) + I * (y : ℂ))‖ := by
    simpa using hlower
  linarith

/-- The elementary regularization factor is no larger on a left edge in the
critical strip than on the fixed right edge `Re(s)=4`. -/
theorem integral_log_norm_subOne_left_le_fixedRight
    {x0 y0 y1 : ℝ} (hx0Half : 1 / 2 < x0) (hx0One : x0 < 1)
    (hy01 : y0 ≤ y1) :
    (∫ y in y0..y1,
        Real.log ‖(x0 : ℂ) + I * (y : ℂ) - 1‖) ≤
      ∫ y in y0..y1,
        Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖ := by
  have hcontinuous (a : ℝ) (ha : a ≠ 1) :
      Continuous (fun y : ℝ =>
        Real.log ‖(a : ℂ) + I * (y : ℂ) - 1‖) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hne : (a : ℂ) + I * (y : ℂ) - 1 ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
        zero_mul, one_mul, Complex.one_re, Complex.zero_re] at hre
      apply ha
      linarith
    have hmap : ContinuousAt
        (fun t : ℝ => (a : ℂ) + I * (t : ℂ) - 1) y := by
      fun_prop
    have hlog : ContinuousAt Real.log
        ‖(a : ℂ) + I * (y : ℂ) - 1‖ :=
      Real.continuousAt_log (norm_ne_zero_iff.mpr hne)
    exact hlog.comp_of_eq
      (continuous_norm.continuousAt.comp_of_eq hmap rfl) rfl
  have hleftInt : IntervalIntegrable (fun y : ℝ =>
      Real.log ‖(x0 : ℂ) + I * (y : ℂ) - 1‖)
      MeasureTheory.volume y0 y1 :=
    (hcontinuous x0 (ne_of_lt hx0One)).intervalIntegrable y0 y1
  have hrightInt : IntervalIntegrable (fun y : ℝ =>
      Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖)
      MeasureTheory.volume y0 y1 :=
    (hcontinuous 4 (by norm_num)).intervalIntegrable y0 y1
  apply intervalIntegral.integral_mono_on hy01 hleftInt hrightInt
  intro y _hy
  have hnorm :
      ‖(x0 : ℂ) + I * (y : ℂ) - 1‖ ≤
        ‖(4 : ℂ) + I * (y : ℂ) - 1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [Complex.sq_norm, Complex.sq_norm]
    norm_num [Complex.normSq_apply]
    nlinarith [sq_nonneg (x0 - 1)]
  have hleftPos : 0 < ‖(x0 : ℂ) + I * (y : ℂ) - 1‖ := by
    rw [norm_pos_iff]
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      zero_mul, one_mul, Complex.one_re, Complex.zero_re] at hre
    linarith
  exact Real.log_le_log hleftPos hnorm

/-- The fixed-right logarithmic lower bound with the full elementary
regularization factor retained for cancellation against the left edge. -/
theorem neg_integral_log_norm_regularizedCarlson_fixedRight_le_with_subOne
    {X : ℕ} (hX : 1 ≤ X) {y0 y1 : ℝ} (hy01 : y0 ≤ y1) :
    -(∫ y in y0..y1,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((4 : ℂ) + I * (y : ℂ))‖) ≤
      -2 * (∫ y in y0..y1,
        Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) -
        (y1 - y0) * Real.log (56 / 81 : ℝ) := by
  have hrightInt :=
    intervalIntegrable_log_norm_regularizedCarlsonZeroDetector
      (X := X) (sigma := 4) (a := y0) (b := y1) (by norm_num)
      (fun _ _ => regularizedCarlsonZeroDetector_ne_zero_of_four_le_re
        hX (by simp))
  have hgeomCont : Continuous (fun y : ℝ =>
      Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hne : (4 : ℂ) + I * (y : ℂ) - 1 ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      norm_num at hre
    have hmap : ContinuousAt
        (fun t : ℝ => (4 : ℂ) + I * (t : ℂ) - 1) y := by
      fun_prop
    have hlog : ContinuousAt Real.log
        ‖(4 : ℂ) + I * (y : ℂ) - 1‖ :=
      Real.continuousAt_log (norm_ne_zero_iff.mpr hne)
    exact hlog.comp_of_eq
      (continuous_norm.continuousAt.comp_of_eq hmap rfl) rfl
  have hgeomInt : IntervalIntegrable (fun y : ℝ =>
      Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖)
      MeasureTheory.volume y0 y1 := hgeomCont.intervalIntegrable y0 y1
  have hminorantInt : IntervalIntegrable (fun y : ℝ =>
      2 * Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖ +
        Real.log (56 / 81 : ℝ)) MeasureTheory.volume y0 y1 := by
    exact (hgeomInt.const_mul 2).add intervalIntegrable_const
  have hlower := intervalIntegral.integral_mono_on hy01 hminorantInt hrightInt
    (fun y _hy => by
      simpa [mul_comm] using
        (log_fiftySix_div_eightyOne_le_log_norm_regularized_of_four_le_re
          hX (s := (4 : ℂ) + I * (y : ℂ)) (by simp)))
  have hminorantEq :
      (∫ y in y0..y1,
          2 * Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖ +
            Real.log (56 / 81 : ℝ)) =
        2 * (∫ y in y0..y1,
          Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) +
          (y1 - y0) * Real.log (56 / 81 : ℝ) := by
    rw [intervalIntegral.integral_add (hgeomInt.const_mul 2)
        intervalIntegrable_const,
      intervalIntegral.integral_const_mul]
    simp
  rw [hminorantEq] at hlower
  have hlower' :
      2 * (∫ y in y0..y1,
          Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) +
          (y1 - y0) * Real.log (56 / 81 : ℝ) ≤
        ∫ y in y0..y1,
          Real.log ‖regularizedCarlsonZeroDetector X
            ((4 : ℂ) + (y : ℂ) * I)‖ := by
    simpa only [mul_comm I] using hlower
  have hneg := neg_le_neg hlower
  simpa only [neg_add, neg_mul] using hneg

/-- The inverse-square majorant used on the far-right horizontal extension
has an exact elementary integral. -/
theorem integral_inv_sq_sub_one_eq {R : ℝ} (hR : 4 ≤ R) :
    (∫ x : ℝ in 4..R, 1 / (x - 1) ^ 2) =
      1 / 3 - 1 / (R - 1) := by
  let F : ℝ → ℝ := fun x => -(x - 1)⁻¹
  have hderiv (x : ℝ) (hx : x ∈ Set.uIcc (4 : ℝ) R) :
      HasDerivAt F (1 / (x - 1) ^ 2) x := by
    have hx4 : 4 ≤ x := by
      rw [Set.uIcc_of_le hR] at hx
      exact hx.1
    have hxne : x - 1 ≠ 0 := by linarith
    have h := (((hasDerivAt_id x).sub_const 1).inv hxne).neg
    convert h using 1
    simp only [id_eq]
    field_simp
  have hint : IntervalIntegrable (fun x : ℝ => 1 / (x - 1) ^ 2)
      MeasureTheory.volume 4 R := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx4 : 4 ≤ x := by
      rw [Set.uIcc_of_le hR] at hx
      exact hx.1
    have hxne : x - 1 ≠ 0 := by linarith
    exact (continuousAt_const.div
      ((continuousAt_id.sub continuousAt_const).pow 2)
      (pow_ne_zero 2 hxne)).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  convert hFTC using 1 <;> norm_num [F, one_div] <;> ring

/-- The principal argument of the original Carlson detector has uniformly
bounded integral on every horizontal ray starting at `Re(s)=4`.  The key is
the quadratic decay of its complex logarithm, not a constant pointwise
argument bound. -/
theorem abs_integral_im_log_carlsonZeroDetector_horizontal_le
    {X : ℕ} (hX : 1 ≤ X) {R y : ℝ} (hR : 4 ≤ R) :
    |∫ x : ℝ in 4..R,
        (Complex.log (carlsonZeroDetector X
          ((x : ℂ) + (y : ℂ) * I))).im| ≤ 25 / 18 := by
  let g : ℝ → ℝ := fun x => 25 / (6 * (x - 1) ^ 2)
  have hgInt : IntervalIntegrable g MeasureTheory.volume 4 R := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx4 : 4 ≤ x := by
      rw [Set.uIcc_of_le hR] at hx
      exact hx.1
    have hxne : x - 1 ≠ 0 := by linarith
    dsimp [g]
    exact (continuousAt_const.div
      (continuousAt_const.mul
        ((continuousAt_id.sub continuousAt_const).pow 2))
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hxne))).continuousWithinAt
  have hpoint : ∀ᵐ x : ℝ, x ∈ Set.Ioc (4 : ℝ) R →
      ‖(Complex.log (carlsonZeroDetector X
        ((x : ℂ) + (y : ℂ) * I))).im‖ ≤ g x := by
    filter_upwards [] with x hx
    have hx4 : 4 ≤ x := hx.1.le
    have hlog := norm_log_carlsonZeroDetector_le_inv_sq_of_four_le_re
      hX (s := (x : ℂ) + (y : ℂ) * I) (by simpa using hx4)
    have hlog' : ‖Complex.log (carlsonZeroDetector X
        ((x : ℂ) + (y : ℂ) * I))‖ ≤ g x := by
      simpa [g] using hlog
    rw [Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans hlog'
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le hR hpoint hgInt
  have hgEq : (∫ x : ℝ in 4..R, g x) =
      (25 / 6 : ℝ) * (1 / 3 - 1 / (R - 1)) := by
    calc
      (∫ x : ℝ in 4..R, g x) =
          ∫ x : ℝ in 4..R, (25 / 6 : ℝ) * (1 / (x - 1) ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx4 : 4 ≤ x := by
          rw [Set.uIcc_of_le hR] at hx
          exact hx.1
        have hxne : x - 1 ≠ 0 := by linarith
        dsimp [g]
        field_simp
      _ = (25 / 6 : ℝ) * (1 / 3 - 1 / (R - 1)) := by
        rw [intervalIntegral.integral_const_mul,
          integral_inv_sq_sub_one_eq hR]
  have hRden : 0 ≤ 1 / (R - 1) := one_div_nonneg.mpr (by linarith)
  rw [hgEq] at hintegral
  simpa [Real.norm_eq_abs] using hintegral.trans (by nlinarith)

/-- The negative logarithmic integral of Carlson's original detector on the
fixed line `Re(s)=4` is bounded independently of the height.  We close a
zero-free rectangle at `Re(s)=4+(y1-y0)`: the far edge is small by quadratic
logarithmic decay, and both horizontal argument integrals are absolutely
convergent with the same decay. -/
theorem neg_integral_log_norm_carlsonZeroDetector_fixedRight_le_constant
    {X : ℕ} (hX : 1 ≤ X) {y0 y1 : ℝ} (hy01 : y0 ≤ y1) :
    -(∫ y in y0..y1,
        Real.log ‖carlsonZeroDetector X
          ((4 : ℂ) + (y : ℂ) * I)‖) ≤ 125 / 18 := by
  let R : ℝ := 4 + (y1 - y0)
  let G : ℂ → ℂ := fun s => Complex.log (carlsonZeroDetector X s)
  have hR : 4 ≤ R := by dsimp [R]; linarith
  have hdiff : DifferentiableOn ℂ G ([[4, R]] ×ℂ [[y0, y1]]) := by
    intro s hs
    rw [mem_reProdIm] at hs
    have hsRe : 4 ≤ s.re := by
      rw [Set.uIcc_of_le hR] at hs
      exact hs.1.1
    have hs1 : s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hanalytic := analyticAt_carlsonZeroDetector_of_ne_one X hs1
    have hdetRe :=
      fiftySix_div_eightyOne_le_re_carlsonZeroDetector_of_four_le_re hX hsRe
    have hslit : carlsonZeroDetector X s ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl ((by norm_num : (0 : ℝ) < 56 / 81).trans_le hdetRe)
    exact (hanalytic.clog hslit).differentiableAt.differentiableWithinAt
  have hcont : ContinuousOn G ([[4, R]] ×ℂ [[y0, y1]]) := hdiff.continuousOn
  have hbottom : IntervalIntegrable
      (fun x : ℝ => G ((x : ℂ) + (y0 : ℂ) * I))
      MeasureTheory.volume 4 R := by
    exact (hcont.comp
      (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const)).continuousOn (by
          intro x hx
          simpa [mem_reProdIm] using
            And.intro hx (left_mem_uIcc : y0 ∈ [[y0, y1]]))).intervalIntegrable
  have htop : IntervalIntegrable
      (fun x : ℝ => G ((x : ℂ) + (y1 : ℂ) * I))
      MeasureTheory.volume 4 R := by
    exact (hcont.comp
      (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const)).continuousOn (by
          intro x hx
          simpa [mem_reProdIm] using
            And.intro hx (right_mem_uIcc : y1 ∈ [[y0, y1]]))).intervalIntegrable
  have hright : IntervalIntegrable
      (fun y : ℝ => G ((R : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume y0 y1 := by
    exact (hcont.comp
      (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const)).continuousOn (by
          intro y hy
          simpa [mem_reProdIm] using
            And.intro (right_mem_uIcc : R ∈ [[4, R]]) hy)).intervalIntegrable
  have hleft : IntervalIntegrable
      (fun y : ℝ => G ((4 : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume y0 y1 := by
    exact (hcont.comp
      (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const)).continuousOn (by
          intro y hy
          simpa [mem_reProdIm] using
            And.intro (left_mem_uIcc : (4 : ℝ) ∈ [[4, R]]) hy)).intervalIntegrable
  have hzero := MathlibAux.boundaryRectIntegral_eq_zero_of_differentiableOn
    G 4 R y0 y1 hdiff
  have hedges := im_boundaryRectIntegral_eq_four_edges
    hbottom htop hright hleft
  rw [hzero] at hedges
  have hbottomAbs :
      |∫ x : ℝ in 4..R, (G ((x : ℂ) + (y0 : ℂ) * I)).im| ≤ 25 / 18 := by
    simpa [G] using
      abs_integral_im_log_carlsonZeroDetector_horizontal_le hX hR
  have htopAbs :
      |∫ x : ℝ in 4..R, (G ((x : ℂ) + (y1 : ℂ) * I)).im| ≤ 25 / 18 := by
    simpa [G] using
      abs_integral_im_log_carlsonZeroDetector_horizontal_le hX hR
  let C : ℝ := 25 / (6 * (R - 1) ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrightAbsRaw := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun y : ℝ =>
      Real.log ‖carlsonZeroDetector X ((R : ℂ) + (y : ℂ) * I)‖)
    (a := y0) (b := y1) (C := C) (fun y _hy => by
      change |Real.log ‖carlsonZeroDetector X
        ((R : ℂ) + (y : ℂ) * I)‖| ≤ C
      rw [← Complex.log_re]
      have hlog := norm_log_carlsonZeroDetector_le_inv_sq_of_four_le_re
        hX (s := (R : ℂ) + (y : ℂ) * I) (by simpa using hR)
      have hlog' : ‖Complex.log (carlsonZeroDetector X
          ((R : ℂ) + (y : ℂ) * I))‖ ≤ C := by
        simpa [C] using hlog
      exact (Complex.abs_re_le_norm _).trans hlog')
  have hlength : 0 ≤ y1 - y0 := sub_nonneg.mpr hy01
  have hCwidth : C * |y1 - y0| ≤ 25 / 6 := by
    rw [abs_of_nonneg hlength]
    dsimp [C, R]
    have hsquare : y1 - y0 ≤ (3 + (y1 - y0)) ^ 2 := by
      nlinarith [sq_nonneg (y1 - y0)]
    have hdenPos : 0 < 6 * (4 + (y1 - y0) - 1) ^ 2 := by
      have : 0 < 4 + (y1 - y0) - 1 := by linarith
      positivity
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hdenPos).2
    nlinarith
  have hrightAbs :
      |∫ y in y0..y1,
          Real.log ‖carlsonZeroDetector X
            ((R : ℂ) + (y : ℂ) * I)‖| ≤ 25 / 6 := by
    simpa [Real.norm_eq_abs] using hrightAbsRaw.trans hCwidth
  dsimp [G] at hedges hbottomAbs htopAbs
  simp only [Complex.zero_im, Complex.log_re] at hedges
  have hbottomLower := neg_le_of_abs_le hbottomAbs
  have htopUpper := le_of_abs_le htopAbs
  have hrightLower := neg_le_of_abs_le hrightAbs
  linarith

/-- Refined fixed-right bound retaining the elementary `(s-1)^2` term for
exact cancellation, with the original detector contributing only an absolute
constant instead of a term proportional to the edge height. -/
theorem
    neg_integral_log_norm_regularizedCarlson_fixedRight_le_with_subOne_constant
    {X : ℕ} (hX : 1 ≤ X) {y0 y1 : ℝ} (hy01 : y0 ≤ y1) :
    -(∫ y in y0..y1,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((4 : ℂ) + I * (y : ℂ))‖) ≤
      -2 * (∫ y in y0..y1,
        Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) + 125 / 18 := by
  have hgeomCont : Continuous (fun y : ℝ =>
      Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hne : (4 : ℂ) + I * (y : ℂ) - 1 ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      norm_num at hre
    have hmap : ContinuousAt
        (fun t : ℝ => (4 : ℂ) + I * (t : ℂ) - 1) y := by
      fun_prop
    have hlog : ContinuousAt Real.log
        ‖(4 : ℂ) + I * (y : ℂ) - 1‖ :=
      Real.continuousAt_log (norm_ne_zero_iff.mpr hne)
    exact hlog.comp_of_eq
      (continuous_norm.continuousAt.comp_of_eq hmap rfl) rfl
  have hgeomInt : IntervalIntegrable (fun y : ℝ =>
      Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖)
      MeasureTheory.volume y0 y1 := hgeomCont.intervalIntegrable y0 y1
  have hdetIntI := intervalIntegrable_log_norm_carlsonZeroDetector
    (X := X) (sigma := 4) (a := y0) (b := y1) (by norm_num)
    (fun _ _ => carlsonZeroDetector_ne_zero_of_four_le_re hX (by simp))
  have hdetInt : IntervalIntegrable (fun y : ℝ =>
      Real.log ‖carlsonZeroDetector X
        ((4 : ℂ) + I * (y : ℂ))‖)
      MeasureTheory.volume y0 y1 := hdetIntI
  have hsplit :
      (∫ y in y0..y1,
          Real.log ‖regularizedCarlsonZeroDetector X
            ((4 : ℂ) + I * (y : ℂ))‖) =
        2 * (∫ y in y0..y1,
          Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) +
        ∫ y in y0..y1,
          Real.log ‖carlsonZeroDetector X
            ((4 : ℂ) + I * (y : ℂ))‖ := by
    calc
      (∫ y in y0..y1,
          Real.log ‖regularizedCarlsonZeroDetector X
            ((4 : ℂ) + I * (y : ℂ))‖) =
          ∫ y in y0..y1,
            (2 * Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖ +
              Real.log ‖carlsonZeroDetector X
                ((4 : ℂ) + I * (y : ℂ))‖) := by
        apply intervalIntegral.integral_congr
        intro y _hy
        let s : ℂ := (4 : ℂ) + I * (y : ℂ)
        have hs0 : s ≠ 0 := by
          intro hz
          have hre := congrArg Complex.re hz
          norm_num [s] at hre
        have hs1 : s ≠ 1 := by
          intro hz
          have hre := congrArg Complex.re hz
          norm_num [s] at hre
        have hdet : carlsonZeroDetector X s ≠ 0 :=
          carlsonZeroDetector_ne_zero_of_four_le_re hX (by simp [s])
        simpa [s] using
          log_norm_regularizedCarlsonZeroDetector_eq_two_log_norm_sub_one_add
            X hs0 hs1 hdet
      _ = 2 * (∫ y in y0..y1,
            Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) +
          ∫ y in y0..y1,
            Real.log ‖carlsonZeroDetector X
              ((4 : ℂ) + I * (y : ℂ))‖ := by
        rw [intervalIntegral.integral_add (hgeomInt.const_mul 2) hdetInt,
          intervalIntegral.integral_const_mul]
  have hdetNeg :=
    neg_integral_log_norm_carlsonZeroDetector_fixedRight_le_constant
      hX hy01
  have hdetNeg' :
      -(∫ y in y0..y1,
          Real.log ‖carlsonZeroDetector X
            ((4 : ℂ) + I * (y : ℂ))‖) ≤ 125 / 18 := by
    simpa only [mul_comm I] using hdetNeg
  rw [hsplit]
  linarith

/-- The branch-free argument variation of Carlson's original detector on the
fixed line `Re(s) = 4`. -/
noncomputable def carlsonDetectorFixedRightArgumentVariation
    (X : ℕ) (y0 y1 : ℝ) : ℝ :=
  ∫ y in y0..y1,
    (logDeriv (carlsonZeroDetector X)
      ((4 : ℂ) + (y : ℂ) * I)).re

private theorem hasDerivAt_carlsonDetectorFixedRightArgument
    {X : ℕ} (hX : 1 ≤ X) (y : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        (Complex.log (carlsonZeroDetector X
          ((4 : ℂ) + (t : ℂ) * I))).im)
      (logDeriv (carlsonZeroDetector X)
        ((4 : ℂ) + (y : ℂ) * I)).re y := by
  let s : ℂ := (4 : ℂ) + (y : ℂ) * I
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have hanalytic : AnalyticAt ℂ (carlsonZeroDetector X) s :=
    analyticAt_carlsonZeroDetector_of_ne_one X hs1
  have hright : (56 / 81 : ℝ) ≤ (carlsonZeroDetector X s).re :=
    fiftySix_div_eightyOne_le_re_carlsonZeroDetector_of_four_le_re
      hX (by simp [s])
  have hslit : carlsonZeroDetector X s ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl ((by norm_num : (0 : ℝ) < 56 / 81).trans_le hright)
  have hanalytic' : AnalyticAt ℂ (carlsonZeroDetector X)
      ((4 : ℂ) + I * (y : ℂ)) := by
    simpa [s, mul_comm] using hanalytic
  have hslit' : carlsonZeroDetector X
      ((4 : ℂ) + I * (y : ℂ)) ∈ Complex.slitPlane := by
    simpa [s, mul_comm] using hslit
  simpa [mul_comm] using
    hasDerivAt_im_log_vertical_of_analyticAt hanalytic' hslit'

private theorem intervalIntegrable_carlsonDetectorFixedRightArgument
    {X : ℕ} (hX : 1 ≤ X) (y0 y1 : ℝ) :
    IntervalIntegrable
      (fun y : ℝ =>
        (logDeriv (carlsonZeroDetector X)
          ((4 : ℂ) + (y : ℂ) * I)).re)
      MeasureTheory.volume y0 y1 := by
  apply ContinuousOn.intervalIntegrable
  intro y _hy
  let s : ℂ := (4 : ℂ) + (y : ℂ) * I
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have hanalytic : AnalyticAt ℂ (carlsonZeroDetector X) s :=
    analyticAt_carlsonZeroDetector_of_ne_one X hs1
  have hne : carlsonZeroDetector X s ≠ 0 :=
    carlsonZeroDetector_ne_zero_of_four_le_re hX (by simp [s])
  have hlog : AnalyticAt ℂ (logDeriv (carlsonZeroDetector X)) s :=
    ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero hanalytic hne
  have hmap : ContinuousAt
      (fun t : ℝ => (4 : ℂ) + (t : ℂ) * I) y := by
    fun_prop
  have hcomp : ContinuousAt
      (fun t : ℝ => logDeriv (carlsonZeroDetector X)
        ((4 : ℂ) + (t : ℂ) * I)) y := by
    simpa [s, Function.comp_def] using
      hlog.continuousAt.comp_of_eq hmap rfl
  exact
    (Complex.continuous_re.continuousAt.comp_of_eq hcomp rfl).continuousWithinAt

/-- The original detector stays in the right half-plane on `Re(s) = 4`, so
its total argument variation between any two heights is at most `pi`. -/
theorem abs_carlsonDetectorFixedRightArgumentVariation_le_pi
    {X : ℕ} (hX : 1 ≤ X) (y0 y1 : ℝ) :
    |carlsonDetectorFixedRightArgumentVariation X y0 y1| ≤ Real.pi := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _hy => hasDerivAt_carlsonDetectorFixedRightArgument hX y)
    (intervalIntegrable_carlsonDetectorFixedRightArgument hX y0 y1)
  have hvariation : carlsonDetectorFixedRightArgumentVariation X y0 y1 =
      (carlsonZeroDetector X ((4 : ℂ) + (y1 : ℂ) * I)).arg -
        (carlsonZeroDetector X ((4 : ℂ) + (y0 : ℂ) * I)).arg := by
    rw [carlsonDetectorFixedRightArgumentVariation, hFTC]
    simp only [Complex.log_im]
  rw [hvariation]
  have harg (y : ℝ) :
      |(carlsonZeroDetector X ((4 : ℂ) + (y : ℂ) * I)).arg| <
        Real.pi / 2 := by
    apply Complex.abs_arg_lt_pi_div_two_iff.mpr
    apply Or.inl
    have hright :=
      fiftySix_div_eightyOne_le_re_carlsonZeroDetector_of_four_le_re
        hX (s := (4 : ℂ) + (y : ℂ) * I) (by simp)
    exact (by norm_num : (0 : ℝ) < 56 / 81).trans_le hright
  apply le_of_lt
  calc
    |(carlsonZeroDetector X ((4 : ℂ) + (y1 : ℂ) * I)).arg -
        (carlsonZeroDetector X ((4 : ℂ) + (y0 : ℂ) * I)).arg| ≤
      |(carlsonZeroDetector X ((4 : ℂ) + (y1 : ℂ) * I)).arg| +
        |(carlsonZeroDetector X ((4 : ℂ) + (y0 : ℂ) * I)).arg| :=
      abs_sub _ _
    _ < Real.pi / 2 + Real.pi / 2 := add_lt_add (harg y1) (harg y0)
    _ = Real.pi := by ring

/-- Argument variation of the linear pole-cancelling factor `s - 1` on the
fixed line `Re(s) = 4`. -/
noncomputable def subOneFixedRightArgumentVariation (y0 y1 : ℝ) : ℝ :=
  ∫ y in y0..y1,
    (((4 : ℂ) + (y : ℂ) * I - 1)⁻¹).re

private theorem hasDerivAt_subOneFixedRightArgument (y : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        (Complex.log ((4 : ℂ) + (t : ℂ) * I - 1)).im)
      (((4 : ℂ) + (y : ℂ) * I - 1)⁻¹).re y := by
  let s : ℂ := (4 : ℂ) + (y : ℂ) * I
  have hanalytic : AnalyticAt ℂ (fun z : ℂ => z - 1) s :=
    analyticAt_id.sub analyticAt_const
  have hslit : s - 1 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (by norm_num [s])
  have hanalytic' : AnalyticAt ℂ (fun z : ℂ => z - 1)
      ((4 : ℂ) + I * (y : ℂ)) := by
    simpa [s, mul_comm] using hanalytic
  have hslit' : (4 : ℂ) + I * (y : ℂ) - 1 ∈ Complex.slitPlane := by
    simpa [s, mul_comm] using hslit
  have h := hasDerivAt_im_log_vertical_of_analyticAt
    (f := fun z : ℂ => z - 1) (sigma := 4) hanalytic' hslit'
  simpa [logDeriv_apply, mul_comm] using h

private theorem intervalIntegrable_subOneFixedRightArgument
    (y0 y1 : ℝ) :
    IntervalIntegrable
      (fun y : ℝ => (((4 : ℂ) + (y : ℂ) * I - 1)⁻¹).re)
      MeasureTheory.volume y0 y1 := by
  apply ContinuousOn.intervalIntegrable
  intro y _hy
  let s : ℂ := (4 : ℂ) + (y : ℂ) * I
  have hanalytic : AnalyticAt ℂ (fun z : ℂ => z - 1) s :=
    analyticAt_id.sub analyticAt_const
  have hne : s - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have hlog : AnalyticAt ℂ (logDeriv (fun z : ℂ => z - 1)) s :=
    ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero hanalytic hne
  have hmap : ContinuousAt
      (fun t : ℝ => (4 : ℂ) + (t : ℂ) * I) y := by
    fun_prop
  have hcomp : ContinuousAt
      (fun t : ℝ => logDeriv (fun z : ℂ => z - 1)
        ((4 : ℂ) + (t : ℂ) * I)) y := by
    simpa [s, Function.comp_def] using
      hlog.continuousAt.comp_of_eq hmap rfl
  have hre : ContinuousWithinAt
      (fun t : ℝ =>
        (logDeriv (fun z : ℂ => z - 1)
          ((4 : ℂ) + (t : ℂ) * I)).re) [[y0, y1]] y :=
    (Complex.continuous_re.continuousAt.comp_of_eq hcomp rfl).continuousWithinAt
  simpa [logDeriv_apply] using hre

/-- The linear factor has positive real part on `Re(s) = 4`, so its argument
variation between arbitrary heights is at most `pi`. -/
theorem abs_subOneFixedRightArgumentVariation_le_pi (y0 y1 : ℝ) :
    |subOneFixedRightArgumentVariation y0 y1| ≤ Real.pi := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _hy => hasDerivAt_subOneFixedRightArgument y)
    (intervalIntegrable_subOneFixedRightArgument y0 y1)
  have hvariation : subOneFixedRightArgumentVariation y0 y1 =
      ((4 : ℂ) + (y1 : ℂ) * I - 1).arg -
        ((4 : ℂ) + (y0 : ℂ) * I - 1).arg := by
    rw [subOneFixedRightArgumentVariation, hFTC]
    simp only [Complex.log_im]
  rw [hvariation]
  have harg (y : ℝ) :
      |((4 : ℂ) + (y : ℂ) * I - 1).arg| < Real.pi / 2 := by
    apply Complex.abs_arg_lt_pi_div_two_iff.mpr
    exact Or.inl (by norm_num)
  apply le_of_lt
  calc
    |((4 : ℂ) + (y1 : ℂ) * I - 1).arg -
        ((4 : ℂ) + (y0 : ℂ) * I - 1).arg| ≤
      |((4 : ℂ) + (y1 : ℂ) * I - 1).arg| +
        |((4 : ℂ) + (y0 : ℂ) * I - 1).arg| := abs_sub _ _
    _ < Real.pi / 2 + Real.pi / 2 := add_lt_add (harg y1) (harg y0)
    _ = Real.pi := by ring

/-- Argument variation of the pole-free Carlson detector on the fixed line
`Re(s) = 4`. -/
noncomputable def regularizedCarlsonFixedRightArgumentVariation
    (X : ℕ) (y0 y1 : ℝ) : ℝ :=
  ∫ y in y0..y1,
    (logDeriv (regularizedCarlsonZeroDetector X)
      ((4 : ℂ) + (y : ℂ) * I)).re

private theorem intervalIntegrable_regularizedCarlsonFixedRightArgument
    {X : ℕ} (hX : 1 ≤ X) (y0 y1 : ℝ) :
    IntervalIntegrable
      (fun y : ℝ =>
        (logDeriv (regularizedCarlsonZeroDetector X)
          ((4 : ℂ) + (y : ℂ) * I)).re)
      MeasureTheory.volume y0 y1 := by
  apply ContinuousOn.intervalIntegrable
  intro y _hy
  let s : ℂ := (4 : ℂ) + (y : ℂ) * I
  have hanalytic : AnalyticAt ℂ (regularizedCarlsonZeroDetector X) s :=
    analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X s (by norm_num [s])
  have hne : regularizedCarlsonZeroDetector X s ≠ 0 :=
    regularizedCarlsonZeroDetector_ne_zero_of_four_le_re hX (by simp [s])
  have hlog :
      AnalyticAt ℂ (logDeriv (regularizedCarlsonZeroDetector X)) s :=
    ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero hanalytic hne
  have hmap : ContinuousAt
      (fun t : ℝ => (4 : ℂ) + (t : ℂ) * I) y := by
    fun_prop
  have hcomp : ContinuousAt
      (fun t : ℝ => logDeriv (regularizedCarlsonZeroDetector X)
        ((4 : ℂ) + (t : ℂ) * I)) y := by
    simpa [s, Function.comp_def] using
      hlog.continuousAt.comp_of_eq hmap rfl
  exact
    (Complex.continuous_re.continuousAt.comp_of_eq hcomp rfl).continuousWithinAt

private theorem regularizedCarlsonFixedRightArgumentVariation_eq
    {X : ℕ} (hX : 1 ≤ X) (y0 y1 : ℝ) :
    regularizedCarlsonFixedRightArgumentVariation X y0 y1 =
      2 * subOneFixedRightArgumentVariation y0 y1 +
        carlsonDetectorFixedRightArgumentVariation X y0 y1 := by
  have hlinearInt := intervalIntegrable_subOneFixedRightArgument y0 y1
  have hdetectorInt :=
    intervalIntegrable_carlsonDetectorFixedRightArgument hX y0 y1
  rw [regularizedCarlsonFixedRightArgumentVariation,
    subOneFixedRightArgumentVariation,
    carlsonDetectorFixedRightArgumentVariation]
  calc
    (∫ y in y0..y1,
        (logDeriv (regularizedCarlsonZeroDetector X)
          ((4 : ℂ) + (y : ℂ) * I)).re) =
        ∫ y in y0..y1,
          2 * (((4 : ℂ) + (y : ℂ) * I - 1)⁻¹).re +
            (logDeriv (carlsonZeroDetector X)
              ((4 : ℂ) + (y : ℂ) * I)).re := by
      apply intervalIntegral.integral_congr
      intro y _hy
      let s : ℂ := (4 : ℂ) + (y : ℂ) * I
      have hs0 : s ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        norm_num [s] at hre
      have hs1 : s ≠ 1 := by
        intro h
        have hre := congrArg Complex.re h
        norm_num [s] at hre
      have hdet : carlsonZeroDetector X s ≠ 0 :=
        carlsonZeroDetector_ne_zero_of_four_le_re hX (by simp [s])
      have hsplit := congrArg Complex.re
        (logDeriv_regularizedCarlsonZeroDetector_eq_two_inv_add
          X hs0 hs1 hdet)
      simpa [s, Complex.add_re, Complex.mul_re] using hsplit
    _ = 2 * (∫ y in y0..y1,
          (((4 : ℂ) + (y : ℂ) * I - 1)⁻¹).re) +
        ∫ y in y0..y1,
          (logDeriv (carlsonZeroDetector X)
            ((4 : ℂ) + (y : ℂ) * I)).re := by
      rw [intervalIntegral.integral_add
        (IntervalIntegrable.const_mul hlinearInt 2) hdetectorInt,
        intervalIntegral.integral_const_mul]

/-- The two pole-cancelling linear factors contribute at most `2*pi`, while
the original detector contributes at most `pi`; hence the regularized right
edge argument term is bounded independently of the rectangle height. -/
theorem abs_regularizedCarlsonFixedRightArgumentVariation_le_three_pi
    {X : ℕ} (hX : 1 ≤ X) (y0 y1 : ℝ) :
    |regularizedCarlsonFixedRightArgumentVariation X y0 y1| ≤
      3 * Real.pi := by
  rw [regularizedCarlsonFixedRightArgumentVariation_eq hX]
  have hlinear := abs_subOneFixedRightArgumentVariation_le_pi y0 y1
  have hdetector :=
    abs_carlsonDetectorFixedRightArgumentVariation_le_pi hX y0 y1
  calc
    |2 * subOneFixedRightArgumentVariation y0 y1 +
        carlsonDetectorFixedRightArgumentVariation X y0 y1| ≤
      |2 * subOneFixedRightArgumentVariation y0 y1| +
        |carlsonDetectorFixedRightArgumentVariation X y0 y1| :=
      abs_add_le _ _
    _ = 2 * |subOneFixedRightArgumentVariation y0 y1| +
        |carlsonDetectorFixedRightArgumentVariation X y0 y1| := by
      rw [abs_mul]
      norm_num
    _ ≤ 2 * Real.pi + Real.pi :=
      add_le_add (mul_le_mul_of_nonneg_left hlinear (by norm_num)) hdetector
    _ = 3 * Real.pi := by ring

/-- The complete fixed-right contribution in the endpoint-cancelled
Littlewood formula: argument variation minus the logarithmic norm integral. -/
noncomputable def regularizedCarlsonFixedRightBoundaryContribution
    (X : ℕ) (x0 y0 y1 : ℝ) : ℝ :=
  (4 - x0) * regularizedCarlsonFixedRightArgumentVariation X y0 y1 -
    ∫ y in y0..y1,
      Real.log ‖regularizedCarlsonZeroDetector X
        ((4 : ℂ) + (y : ℂ) * I)‖

/-- The entire fixed-right contribution has an explicit upper bound.  Its
argument part is `O(1)` and only the harmless logarithmic lower-bound term is
proportional to the edge length. -/
theorem regularizedCarlsonFixedRightBoundaryContribution_le
    {X : ℕ} (hX : 1 ≤ X) {x0 y0 y1 : ℝ}
    (hx0 : x0 ≤ 4) (hy01 : y0 ≤ y1) :
    regularizedCarlsonFixedRightBoundaryContribution X x0 y0 y1 ≤
      (4 - x0) * (3 * Real.pi) -
        (y1 - y0) * Real.log (56 / 81 : ℝ) := by
  have hargAbs :=
    abs_regularizedCarlsonFixedRightArgumentVariation_le_three_pi
      hX y0 y1
  have harg :
      regularizedCarlsonFixedRightArgumentVariation X y0 y1 ≤
        3 * Real.pi :=
    (le_abs_self _).trans hargAbs
  have hscaled :
      (4 - x0) * regularizedCarlsonFixedRightArgumentVariation X y0 y1 ≤
        (4 - x0) * (3 * Real.pi) :=
    mul_le_mul_of_nonneg_left harg (sub_nonneg.mpr hx0)
  have hlog :
      -(∫ y in y0..y1,
          Real.log ‖regularizedCarlsonZeroDetector X
            ((4 : ℂ) + (y : ℂ) * I)‖) ≤
        -(y1 - y0) * Real.log (56 / 81 : ℝ) := by
    simpa only [mul_comm I] using
      neg_integral_log_norm_regularizedCarlson_fixedRight_le hX hy01
  unfold regularizedCarlsonFixedRightBoundaryContribution
  linarith

/-- On a rectangle with fixed right edge `Re(s)=4`, all terms not belonging
to the left mean-square estimate split into two horizontal terms and the
explicitly controlled right-boundary contribution. -/
theorem regularizedCarlsonLittlewoodRemainingEdges_fixedRight_eq
    (X : ℕ) (x0 y0 y1 : ℝ) :
    regularizedCarlsonLittlewoodRemainingEdges X x0 4 y0 y1 =
      (∫ x in x0..4,
        (x - x0) *
          (logDeriv (regularizedCarlsonZeroDetector X)
            ((x : ℂ) + (y0 : ℂ) * I)).im) -
      (∫ x in x0..4,
        (x - x0) *
          (logDeriv (regularizedCarlsonZeroDetector X)
            ((x : ℂ) + (y1 : ℂ) * I)).im) +
      regularizedCarlsonFixedRightBoundaryContribution X x0 y0 y1 := by
  unfold regularizedCarlsonLittlewoodRemainingEdges
    regularizedCarlsonFixedRightBoundaryContribution
    regularizedCarlsonFixedRightArgumentVariation
  abel

/-- One of the two weighted horizontal argument terms in the endpoint-
cancelled Littlewood formula. -/
noncomputable def regularizedCarlsonHorizontalArgumentTerm
    (X : ℕ) (x0 y : ℝ) : ℝ :=
  ∫ x in x0..4,
    (x - x0) *
      (logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y : ℂ) * I)).im

/-- A uniform logarithmic-derivative bound on a horizontal edge controls its
weighted argument term by the square of the edge width. -/
theorem abs_regularizedCarlsonHorizontalArgumentTerm_le_sq_mul
    {X : ℕ} {x0 y M : ℝ}
    (hx0 : x0 ≤ 4) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ Set.Icc x0 4,
      ‖logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y : ℂ) * I)‖ ≤ M) :
    |regularizedCarlsonHorizontalArgumentTerm X x0 y| ≤
      (4 - x0) ^ 2 * M := by
  have hwidth : 0 ≤ 4 - x0 := sub_nonneg.mpr hx0
  have hpoint (x : ℝ) (hx : x ∈ Set.uIoc x0 4) :
      ‖(x - x0) *
        (logDeriv (regularizedCarlsonZeroDetector X)
          ((x : ℂ) + (y : ℂ) * I)).im‖ ≤
        (4 - x0) * M := by
    rw [Set.uIoc_of_le hx0] at hx
    have hxIcc : x ∈ Set.Icc x0 4 := ⟨hx.1.le, hx.2⟩
    have hxnonneg : 0 ≤ x - x0 := sub_nonneg.mpr hx.1.le
    have hxwidth : x - x0 ≤ 4 - x0 := by linarith [hx.2]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hxnonneg]
    calc
      (x - x0) *
          |(logDeriv (regularizedCarlsonZeroDetector X)
            ((x : ℂ) + (y : ℂ) * I)).im| ≤
        (x - x0) *
          ‖logDeriv (regularizedCarlsonZeroDetector X)
            ((x : ℂ) + (y : ℂ) * I)‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) hxnonneg
      _ ≤ (x - x0) * M :=
        mul_le_mul_of_nonneg_left (hbound x hxIcc) hxnonneg
      _ ≤ (4 - x0) * M :=
        mul_le_mul_of_nonneg_right hxwidth hM
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ =>
      (x - x0) *
        (logDeriv (regularizedCarlsonZeroDetector X)
          ((x : ℂ) + (y : ℂ) * I)).im)
    (a := x0) (b := 4) (C := (4 - x0) * M) hpoint
  have hterm :
      |regularizedCarlsonHorizontalArgumentTerm X x0 y| ≤
        ((4 - x0) * M) * (4 - x0) := by
    simpa [regularizedCarlsonHorizontalArgumentTerm, Real.norm_eq_abs,
      abs_of_nonneg hwidth] using hintegral
  calc
    |regularizedCarlsonHorizontalArgumentTerm X x0 y| ≤
        ((4 - x0) * M) * (4 - x0) := hterm
    _ = (4 - x0) ^ 2 * M := by ring

/-- Once uniform logarithmic-derivative bounds are available on the two
horizontal edges, every remaining term in the fixed-right Littlewood formula
has an explicit upper bound. -/
theorem regularizedCarlsonLittlewoodRemainingEdges_fixedRight_le_of_horizontalBounds
    {X : ℕ} (hX : 1 ≤ X) {x0 y0 y1 M0 M1 : ℝ}
    (hx0 : x0 ≤ 4) (hy01 : y0 ≤ y1)
    (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hbottom : ∀ x ∈ Set.Icc x0 4,
      ‖logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y0 : ℂ) * I)‖ ≤ M0)
    (htop : ∀ x ∈ Set.Icc x0 4,
      ‖logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y1 : ℂ) * I)‖ ≤ M1) :
    regularizedCarlsonLittlewoodRemainingEdges X x0 4 y0 y1 ≤
      (4 - x0) ^ 2 * (M0 + M1) +
        (4 - x0) * (3 * Real.pi) -
        (y1 - y0) * Real.log (56 / 81 : ℝ) := by
  let bottom := regularizedCarlsonHorizontalArgumentTerm X x0 y0
  let top := regularizedCarlsonHorizontalArgumentTerm X x0 y1
  let right := regularizedCarlsonFixedRightBoundaryContribution X x0 y0 y1
  have hbottomTerm : |bottom| ≤ (4 - x0) ^ 2 * M0 := by
    exact abs_regularizedCarlsonHorizontalArgumentTerm_le_sq_mul
      hx0 hM0 hbottom
  have htopTerm : |top| ≤ (4 - x0) ^ 2 * M1 := by
    exact abs_regularizedCarlsonHorizontalArgumentTerm_le_sq_mul
      hx0 hM1 htop
  have hright : right ≤
      (4 - x0) * (3 * Real.pi) -
        (y1 - y0) * Real.log (56 / 81 : ℝ) :=
    regularizedCarlsonFixedRightBoundaryContribution_le hX hx0 hy01
  rw [regularizedCarlsonLittlewoodRemainingEdges_fixedRight_eq]
  change bottom - top + right ≤ _
  calc
    bottom - top + right ≤ |bottom| + |top| + right := by
      linarith [le_abs_self bottom, neg_le_abs top]
    _ ≤ (4 - x0) ^ 2 * M0 + (4 - x0) ^ 2 * M1 +
        ((4 - x0) * (3 * Real.pi) -
          (y1 - y0) * Real.log (56 / 81 : ℝ)) :=
      add_le_add (add_le_add hbottomTerm htopTerm) hright
    _ = (4 - x0) ^ 2 * (M0 + M1) +
        (4 - x0) * (3 * Real.pi) -
        (y1 - y0) * Real.log (56 / 81 : ℝ) := by ring

/-- Refined remaining-edge bound retaining the fixed-right contribution of
the elementary factor `(s - 1)^2`. -/
theorem
    regularizedCarlsonLittlewoodRemainingEdges_fixedRight_le_of_horizontalBounds_with_subOne
    {X : ℕ} (hX : 1 ≤ X) {x0 y0 y1 M0 M1 : ℝ}
    (hx0 : x0 ≤ 4) (hy01 : y0 ≤ y1)
    (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hbottom : ∀ x ∈ Set.Icc x0 4,
      ‖logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y0 : ℂ) * I)‖ ≤ M0)
    (htop : ∀ x ∈ Set.Icc x0 4,
      ‖logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y1 : ℂ) * I)‖ ≤ M1) :
    regularizedCarlsonLittlewoodRemainingEdges X x0 4 y0 y1 ≤
      (4 - x0) ^ 2 * (M0 + M1) +
        (4 - x0) * (3 * Real.pi) -
        2 * (∫ y in y0..y1,
          Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) -
        (y1 - y0) * Real.log (56 / 81 : ℝ) := by
  let bottom := regularizedCarlsonHorizontalArgumentTerm X x0 y0
  let top := regularizedCarlsonHorizontalArgumentTerm X x0 y1
  let right := regularizedCarlsonFixedRightBoundaryContribution X x0 y0 y1
  have hbottomTerm : |bottom| ≤ (4 - x0) ^ 2 * M0 :=
    abs_regularizedCarlsonHorizontalArgumentTerm_le_sq_mul hx0 hM0 hbottom
  have htopTerm : |top| ≤ (4 - x0) ^ 2 * M1 :=
    abs_regularizedCarlsonHorizontalArgumentTerm_le_sq_mul hx0 hM1 htop
  have hargAbs :=
    abs_regularizedCarlsonFixedRightArgumentVariation_le_three_pi
      hX y0 y1
  have harg :
      regularizedCarlsonFixedRightArgumentVariation X y0 y1 ≤
        3 * Real.pi := (le_abs_self _).trans hargAbs
  have hscaled :
      (4 - x0) * regularizedCarlsonFixedRightArgumentVariation X y0 y1 ≤
        (4 - x0) * (3 * Real.pi) :=
    mul_le_mul_of_nonneg_left harg (sub_nonneg.mpr hx0)
  have hrightLog :=
    neg_integral_log_norm_regularizedCarlson_fixedRight_le_with_subOne
      hX hy01
  have hrightLog' :
      -(∫ y in y0..y1,
          Real.log ‖regularizedCarlsonZeroDetector X
            ((4 : ℂ) + (y : ℂ) * I)‖) ≤
        -2 * (∫ y in y0..y1,
          Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) -
          (y1 - y0) * Real.log (56 / 81 : ℝ) := by
    simpa only [mul_comm I] using hrightLog
  have hright : right ≤
      (4 - x0) * (3 * Real.pi) -
        2 * (∫ y in y0..y1,
          Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) -
        (y1 - y0) * Real.log (56 / 81 : ℝ) := by
    dsimp [right]
    unfold regularizedCarlsonFixedRightBoundaryContribution
    linarith
  rw [regularizedCarlsonLittlewoodRemainingEdges_fixedRight_eq]
  change bottom - top + right ≤ _
  calc
    bottom - top + right ≤ |bottom| + |top| + right := by
      linarith [le_abs_self bottom, neg_le_abs top]
    _ ≤ (4 - x0) ^ 2 * M0 + (4 - x0) ^ 2 * M1 +
        ((4 - x0) * (3 * Real.pi) -
          2 * (∫ y in y0..y1,
            Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) -
          (y1 - y0) * Real.log (56 / 81 : ℝ)) :=
      add_le_add (add_le_add hbottomTerm htopTerm) hright
    _ = (4 - x0) ^ 2 * (M0 + M1) +
        (4 - x0) * (3 * Real.pi) -
        2 * (∫ y in y0..y1,
          Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) -
        (y1 - y0) * Real.log (56 / 81 : ℝ) := by ring

/-- Height-uniform refinement of the remaining-edge estimate.  The
elementary factor is still retained for exact left/right cancellation, while
the original detector's fixed-right logarithmic integral is absorbed into an
absolute constant. -/
theorem
    regularizedCarlsonLittlewoodRemainingEdges_fixedRight_le_of_horizontalBounds_with_subOne_constant
    {X : ℕ} (hX : 1 ≤ X) {x0 y0 y1 M0 M1 : ℝ}
    (hx0 : x0 ≤ 4) (hy01 : y0 ≤ y1)
    (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hbottom : ∀ x ∈ Set.Icc x0 4,
      ‖logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y0 : ℂ) * I)‖ ≤ M0)
    (htop : ∀ x ∈ Set.Icc x0 4,
      ‖logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y1 : ℂ) * I)‖ ≤ M1) :
    regularizedCarlsonLittlewoodRemainingEdges X x0 4 y0 y1 ≤
      (4 - x0) ^ 2 * (M0 + M1) +
        (4 - x0) * (3 * Real.pi) -
        2 * (∫ y in y0..y1,
          Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) + 125 / 18 := by
  let bottom := regularizedCarlsonHorizontalArgumentTerm X x0 y0
  let top := regularizedCarlsonHorizontalArgumentTerm X x0 y1
  let right := regularizedCarlsonFixedRightBoundaryContribution X x0 y0 y1
  have hbottomTerm : |bottom| ≤ (4 - x0) ^ 2 * M0 :=
    abs_regularizedCarlsonHorizontalArgumentTerm_le_sq_mul hx0 hM0 hbottom
  have htopTerm : |top| ≤ (4 - x0) ^ 2 * M1 :=
    abs_regularizedCarlsonHorizontalArgumentTerm_le_sq_mul hx0 hM1 htop
  have hargAbs :=
    abs_regularizedCarlsonFixedRightArgumentVariation_le_three_pi
      hX y0 y1
  have harg :
      regularizedCarlsonFixedRightArgumentVariation X y0 y1 ≤
        3 * Real.pi := (le_abs_self _).trans hargAbs
  have hscaled :
      (4 - x0) * regularizedCarlsonFixedRightArgumentVariation X y0 y1 ≤
        (4 - x0) * (3 * Real.pi) :=
    mul_le_mul_of_nonneg_left harg (sub_nonneg.mpr hx0)
  have hrightLog :=
    neg_integral_log_norm_regularizedCarlson_fixedRight_le_with_subOne_constant
      hX hy01
  have hrightLog' :
      -(∫ y in y0..y1,
          Real.log ‖regularizedCarlsonZeroDetector X
            ((4 : ℂ) + (y : ℂ) * I)‖) ≤
        -2 * (∫ y in y0..y1,
          Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) + 125 / 18 := by
    simpa only [mul_comm I] using hrightLog
  have hright : right ≤
      (4 - x0) * (3 * Real.pi) -
        2 * (∫ y in y0..y1,
          Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) + 125 / 18 := by
    dsimp [right]
    unfold regularizedCarlsonFixedRightBoundaryContribution
    linarith
  rw [regularizedCarlsonLittlewoodRemainingEdges_fixedRight_eq]
  change bottom - top + right ≤ _
  calc
    bottom - top + right ≤ |bottom| + |top| + right := by
      linarith [le_abs_self bottom, neg_le_abs top]
    _ ≤ (4 - x0) ^ 2 * M0 + (4 - x0) ^ 2 * M1 +
        ((4 - x0) * (3 * Real.pi) -
          2 * (∫ y in y0..y1,
            Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) + 125 / 18) :=
      add_le_add (add_le_add hbottomTerm htopTerm) hright
    _ = (4 - x0) ^ 2 * (M0 + M1) +
        (4 - x0) * (3 * Real.pi) -
        2 * (∫ y in y0..y1,
          Real.log ‖(4 : ℂ) + I * (y : ℂ) - 1‖) + 125 / 18 := by ring

/-- The endpoint terms from the four edge integrations cancel.  This is the
detector-specific Littlewood lemma in the form used for quantitative bounds:
two horizontal argument terms, one right-edge argument term, and the
difference of the left and right logarithmic norm integrals. -/
theorem regularizedCarlsonLittlewoodFourEdges_eq_logNormForm
    {X : ℕ} {x0 x1 y0 y1 : ℝ}
    (hx0 : 0 < x0) (hx01 : x0 < x1) (hy01 : y0 < y1)
    (hleft : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x1 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hbottom : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    regularizedCarlsonLittlewoodFourEdges X x0 x1 y0 y1 =
      (∫ x in x0..x1,
        (x - x0) *
          (logDeriv (regularizedCarlsonZeroDetector X)
            ((x : ℂ) + (y0 : ℂ) * I)).im) -
      (∫ x in x0..x1,
        (x - x0) *
          (logDeriv (regularizedCarlsonZeroDetector X)
            ((x : ℂ) + (y1 : ℂ) * I)).im) +
      (x1 - x0) *
        (∫ y in y0..y1,
          (logDeriv (regularizedCarlsonZeroDetector X)
            ((x1 : ℂ) + (y : ℂ) * I)).re) +
      (∫ y in y0..y1,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I)‖) -
      (∫ y in y0..y1,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y : ℂ) * I)‖) := by
  have horizontalAnalytic (y : ℝ) : ∀ x ∈ [[x0, x1]],
      AnalyticAt ℂ (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y : ℂ) * I) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc x0 x1 := by
      simpa only [uIcc_of_le hx01.le] using hx
    exact analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X _ (by
        simpa using hx0.trans_le hxIcc.1)
  have hbottom' : ∀ x ∈ [[x0, x1]],
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y0 : ℂ) * I) ≠ 0 := by
    intro x hx
    exact hbottom x (by simpa only [uIcc_of_le hx01.le] using hx)
  have htop' : ∀ x ∈ [[x0, x1]],
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y1 : ℂ) * I) ≠ 0 := by
    intro x hx
    exact htop x (by simpa only [uIcc_of_le hx01.le] using hx)
  have hbottomEq :=
    intervalIntegral_im_weighted_logDeriv_horizontal_eq_of_analytic
      (f := regularizedCarlsonZeroDetector X) (anchor := x0)
      (horizontalAnalytic y0) hbottom'
  have htopEq :=
    intervalIntegral_im_weighted_logDeriv_horizontal_eq_of_analytic
      (f := regularizedCarlsonZeroDetector X) (anchor := x0)
      (horizontalAnalytic y1) htop'
  have hrightEq := regularizedCarlsonLittlewood_rightEdge_eq_logNorm
    (x0 := x0) (hx0.trans hx01) hy01 hright
  have hleftEq := regularizedCarlsonLittlewood_leftEdge_eq_logNorm
    hx0 hy01 hleft
  unfold regularizedCarlsonLittlewoodFourEdges
  rw [hbottomEq, htopEq, hrightEq, hleftEq]
  ring

/-- Named-form wrapper for the endpoint-cancelled Littlewood identity. -/
theorem regularizedCarlsonLittlewoodFourEdges_eq_logNormFormDef
    {X : ℕ} {x0 x1 y0 y1 : ℝ}
    (hx0 : 0 < x0) (hx01 : x0 < x1) (hy01 : y0 < y1)
    (hleft : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x1 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hbottom : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    regularizedCarlsonLittlewoodFourEdges X x0 x1 y0 y1 =
      regularizedCarlsonLittlewoodLogNormForm X x0 x1 y0 y1 := by
  simpa [regularizedCarlsonLittlewoodLogNormForm] using
    regularizedCarlsonLittlewoodFourEdges_eq_logNormForm
      hx0 hx01 hy01 hleft hright hbottom htop

/-- The weighted detector-zero sum dominates Carlson's target zeta-zero
count.  Each target zero lies strictly to the right of `sigma`, and detector
multiplicity dominates zeta multiplicity. -/
theorem sub_mul_zeroDensityCount_le_regularizedCarlsonWeightedZeroSum
    {X : ℕ} (hX : 1 ≤ X) {sigma T x0 x1 y0 y1 : ℝ}
    (hx0 : 0 < x0) (hx0sigma : x0 < sigma)
    (hx1 : 1 < x1) (hy0 : y0 < 0) (hy1 : T < y1) :
    (sigma - x0) * (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
      ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
          X x0 x1 y0 y1,
        (rho.re - x0) *
          (analyticOrderNatAt
            (regularizedCarlsonZeroDetector X) rho : ℝ) := by
  classical
  let S := ZeroDensity.zeroDensityZerosFinset sigma T
  let P := regularizedCarlsonDetectorRectangleDivisorSupport
    X x0 x1 y0 y1
  have hSsub : S ⊆ P := by
    intro rho hrhoS
    have hrho := ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoS
    have hrhoMem : rho ∈ carlsonDetectorRectangle x0 x1 y0 y1 := by
      dsimp [carlsonDetectorRectangle]
      constructor
      · constructor
        · exact (hx0sigma.trans hrho.2.2.2).le
        · exact (hrho.1.2.2.trans hx1).le
      · constructor
        · exact (hy0.trans hrho.2.1).le
        · exact hrho.2.2.1.trans hy1.le
    have hdetectorPos :
        0 < analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho :=
      (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        (by
          intro hone
          have hre := congrArg Complex.re hone
          simp at hre
          linarith [hrho.1.2.2]) hrho.1.1).trans_le
        (analyticOrderNatAt_riemannZeta_le_regularizedCarlsonZeroDetector
          hX hrho.1)
    have hanalytic : AnalyticAt ℂ (regularizedCarlsonZeroDetector X) rho :=
      analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
        (theta := (0 : ℝ)) le_rfl X rho
          (hx0.trans_le hrhoMem.1.1)
    have hdetectorZero : regularizedCarlsonZeroDetector X rho = 0 := by
      apply hanalytic.analyticOrderAt_ne_zero.mp
      intro horderZero
      have hnatZero :
          analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho = 0 := by
        simp [analyticOrderNatAt, horderZero]
      omega
    dsimp [P]
    exact
      (mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
        hX hx0 hrhoMem).mpr hdetectorZero
  have hPnonneg : ∀ rho ∈ P,
      0 ≤ (rho.re - x0) *
        (analyticOrderNatAt
          (regularizedCarlsonZeroDetector X) rho : ℝ) := by
    intro rho hrhoP
    let K := carlsonDetectorRectangle x0 x1 y0 y1
    let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X) K
    have hrhoSupport : rho ∈ D.support := by
      dsimp [P, regularizedCarlsonDetectorRectangleDivisorSupport] at hrhoP
      exact (D.finiteSupport
        (isCompact_carlsonDetectorRectangle x0 x1 y0 y1)).mem_toFinset.mp hrhoP
    have hrhoK : rho ∈ K := D.supportWithinDomain hrhoSupport
    exact mul_nonneg (sub_nonneg.mpr hrhoK.1.1) (Nat.cast_nonneg _)
  calc
    (sigma - x0) * (ZeroDensity.zeroDensityCount sigma T : ℝ) =
        ∑ rho ∈ S, (sigma - x0) *
          (analyticOrderNatAt riemannZeta rho : ℝ) := by
      simp [S, ZeroDensity.zeroDensityCount, Finset.mul_sum]
    _ ≤ ∑ rho ∈ S, (rho.re - x0) *
          (analyticOrderNatAt
            (regularizedCarlsonZeroDetector X) rho : ℝ) := by
      apply Finset.sum_le_sum
      intro rho hrhoS
      have hrho := ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoS
      have hweight : sigma - x0 ≤ rho.re - x0 := by linarith [hrho.2.2.2]
      have hmult :
          (analyticOrderNatAt riemannZeta rho : ℝ) ≤
            (analyticOrderNatAt
              (regularizedCarlsonZeroDetector X) rho : ℝ) := by
        exact_mod_cast
          analyticOrderNatAt_riemannZeta_le_regularizedCarlsonZeroDetector
            hX hrho.1
      exact mul_le_mul hweight hmult (Nat.cast_nonneg _) (by linarith)
    _ ≤ ∑ rho ∈ P, (rho.re - x0) *
          (analyticOrderNatAt
            (regularizedCarlsonZeroDetector X) rho : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSsub
        (fun rho hrhoP _ => hPnonneg rho hrhoP)

/-- A Carlson rectangle whose bottom edge lies above zero still controls the
full zero-density count after adding the fixed low-height zero contribution.
Zeros of ordinate at most `U` are charged to the global multiplicity count;
all remaining target zeros lie in the rectangle when `y0 <= U`. -/
theorem
    sub_mul_zeroDensityCount_le_low_global_add_regularizedCarlsonWeightedZeroSum
    {X : ℕ} (hX : 1 ≤ X) {sigma T U x0 x1 y0 y1 : ℝ}
    (hx0 : 0 < x0) (hx0sigma : x0 < sigma)
    (hx1 : 1 < x1) (hy0U : y0 ≤ U) (hy1 : T < y1) :
    (sigma - x0) * (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
      (sigma - x0) * ExplicitFormulaAux.globalZeroMultiplicity U +
        ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
            X x0 x1 y0 y1,
          (rho.re - x0) *
            (analyticOrderNatAt
              (regularizedCarlsonZeroDetector X) rho : ℝ) := by
  classical
  let S := ZeroDensity.zeroDensityZerosFinset sigma T
  let Slow := S.filter fun rho : ℂ => rho.im ≤ U
  let Shigh := S.filter fun rho : ℂ => ¬rho.im ≤ U
  let P := regularizedCarlsonDetectorRectangleDivisorSupport
    X x0 x1 y0 y1
  have hSlowSub : Slow ⊆ nontrivialZerosFinset U := by
    intro rho hrho
    rcases Finset.mem_filter.mp hrho with ⟨hrhoS, himU⟩
    have htarget := ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoS
    exact mem_nontrivialZerosFinset.mpr
      ⟨htarget.1, by simpa [abs_of_pos htarget.2.1] using himU⟩
  have hLowMultiplicity :
      (∑ rho ∈ Slow, (analyticOrderNatAt riemannZeta rho : ℝ)) ≤
        ExplicitFormulaAux.globalZeroMultiplicity U := by
    calc
      (∑ rho ∈ Slow, (analyticOrderNatAt riemannZeta rho : ℝ)) ≤
          ∑ rho ∈ nontrivialZerosFinset U,
            (analyticOrderNatAt riemannZeta rho : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hSlowSub
          (fun _ _ _ => Nat.cast_nonneg _)
      _ = ExplicitFormulaAux.globalZeroMultiplicity U := rfl
  have hweightNonneg : 0 ≤ sigma - x0 := sub_nonneg.mpr hx0sigma.le
  have hlow :
      (∑ rho ∈ Slow,
          (sigma - x0) * (analyticOrderNatAt riemannZeta rho : ℝ)) ≤
        (sigma - x0) * ExplicitFormulaAux.globalZeroMultiplicity U := by
    simpa [Finset.mul_sum] using
      mul_le_mul_of_nonneg_left hLowMultiplicity hweightNonneg
  have hShighSub : Shigh ⊆ P := by
    intro rho hrhoHigh
    rcases Finset.mem_filter.mp hrhoHigh with ⟨hrhoS, himNot⟩
    have hrho := ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoS
    have himU : U < rho.im := lt_of_not_ge himNot
    have hrhoMem : rho ∈ carlsonDetectorRectangle x0 x1 y0 y1 := by
      dsimp [carlsonDetectorRectangle]
      constructor
      · constructor
        · exact (hx0sigma.trans hrho.2.2.2).le
        · exact (hrho.1.2.2.trans hx1).le
      · constructor
        · exact (hy0U.trans himU.le)
        · exact hrho.2.2.1.trans hy1.le
    have hdetectorPos :
        0 < analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho :=
      (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        (by
          intro hone
          have hre := congrArg Complex.re hone
          simp at hre
          linarith [hrho.1.2.2]) hrho.1.1).trans_le
        (analyticOrderNatAt_riemannZeta_le_regularizedCarlsonZeroDetector
          hX hrho.1)
    have hanalytic : AnalyticAt ℂ (regularizedCarlsonZeroDetector X) rho :=
      analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
        (theta := (0 : ℝ)) le_rfl X rho
          (hx0.trans_le hrhoMem.1.1)
    have hdetectorZero : regularizedCarlsonZeroDetector X rho = 0 := by
      apply hanalytic.analyticOrderAt_ne_zero.mp
      intro horderZero
      have hnatZero :
          analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho = 0 := by
        simp [analyticOrderNatAt, horderZero]
      omega
    dsimp [P]
    exact
      (mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
        hX hx0 hrhoMem).mpr hdetectorZero
  have hPnonneg : ∀ rho ∈ P,
      0 ≤ (rho.re - x0) *
        (analyticOrderNatAt
          (regularizedCarlsonZeroDetector X) rho : ℝ) := by
    intro rho hrhoP
    let K := carlsonDetectorRectangle x0 x1 y0 y1
    let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X) K
    have hrhoSupport : rho ∈ D.support := by
      dsimp [P, regularizedCarlsonDetectorRectangleDivisorSupport] at hrhoP
      exact (D.finiteSupport
        (isCompact_carlsonDetectorRectangle x0 x1 y0 y1)).mem_toFinset.mp hrhoP
    have hrhoK : rho ∈ K := D.supportWithinDomain hrhoSupport
    exact mul_nonneg (sub_nonneg.mpr hrhoK.1.1) (Nat.cast_nonneg _)
  have hhigh :
      (∑ rho ∈ Shigh,
          (sigma - x0) * (analyticOrderNatAt riemannZeta rho : ℝ)) ≤
        ∑ rho ∈ P, (rho.re - x0) *
          (analyticOrderNatAt
            (regularizedCarlsonZeroDetector X) rho : ℝ) := by
    calc
      (∑ rho ∈ Shigh,
          (sigma - x0) * (analyticOrderNatAt riemannZeta rho : ℝ)) ≤
          ∑ rho ∈ Shigh, (rho.re - x0) *
            (analyticOrderNatAt
              (regularizedCarlsonZeroDetector X) rho : ℝ) := by
        apply Finset.sum_le_sum
        intro rho hrhoHigh
        have hrhoS := (Finset.mem_filter.mp hrhoHigh).1
        have hrho := ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoS
        have hweight : sigma - x0 ≤ rho.re - x0 := by
          linarith [hrho.2.2.2]
        have hmult :
            (analyticOrderNatAt riemannZeta rho : ℝ) ≤
              (analyticOrderNatAt
                (regularizedCarlsonZeroDetector X) rho : ℝ) := by
          exact_mod_cast
            analyticOrderNatAt_riemannZeta_le_regularizedCarlsonZeroDetector
              hX hrho.1
        exact mul_le_mul hweight hmult (Nat.cast_nonneg _) (by linarith)
      _ ≤ ∑ rho ∈ P, (rho.re - x0) *
          (analyticOrderNatAt
            (regularizedCarlsonZeroDetector X) rho : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hShighSub
          (fun rho hrhoP _ => hPnonneg rho hrhoP)
  calc
    (sigma - x0) * (ZeroDensity.zeroDensityCount sigma T : ℝ) =
        ∑ rho ∈ S,
          (sigma - x0) * (analyticOrderNatAt riemannZeta rho : ℝ) := by
      simp [S, ZeroDensity.zeroDensityCount, Finset.mul_sum]
    _ = (∑ rho ∈ Slow,
          (sigma - x0) * (analyticOrderNatAt riemannZeta rho : ℝ)) +
        ∑ rho ∈ Shigh,
          (sigma - x0) * (analyticOrderNatAt riemannZeta rho : ℝ) := by
      simpa [Slow, Shigh] using
        (Finset.sum_filter_add_sum_filter_not S
          (fun rho : ℂ => rho.im ≤ U)
          (fun rho : ℂ =>
            (sigma - x0) * (analyticOrderNatAt riemannZeta rho : ℝ))).symm
    _ ≤ (sigma - x0) * ExplicitFormulaAux.globalZeroMultiplicity U +
        ∑ rho ∈ P, (rho.re - x0) *
          (analyticOrderNatAt
            (regularizedCarlsonZeroDetector X) rho : ℝ) :=
      add_le_add hlow hhigh
    _ = (sigma - x0) * ExplicitFormulaAux.globalZeroMultiplicity U +
        ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
            X x0 x1 y0 y1,
          (rho.re - x0) *
            (analyticOrderNatAt
              (regularizedCarlsonZeroDetector X) rho : ℝ) := rfl

/-- Carlson's zero-density count is reduced to the four Littlewood edge
integrals with the left edge selected in `(theta, sigma)`. -/
theorem exists_regularizedCarlson_goodRectangle_zeroDensity_certificate_of_leftWindow
    {X : ℕ} (hX : 1 ≤ X) {theta sigma T : ℝ}
    (htheta : 0 < theta) (hthetaSigma : theta < sigma)
    (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      theta < x0 ∧ x0 < sigma ∧
      1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y0 : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) ∧
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        regularizedCarlsonLittlewoodFourEdges X x0 x1 y0 y1 := by
  obtain ⟨x0, x1, y0, y1,
      hx0Lower, hx0Upper, hx1Lower, hx1Upper, hx01,
      hy0Lower, hy0Upper, hy1Lower, hy1Upper, hy01,
      hleft, hright, hbottom, htop⟩ :=
    exists_regularizedCarlsonZeroDetector_goodRectangle_of_leftWindow
      hX htheta hthetaSigma hsigmaOne hT
  have hx0 : 0 < x0 := htheta.trans hx0Lower
  have hcount :=
    sub_mul_zeroDensityCount_le_regularizedCarlsonWeightedZeroSum
      hX hx0 hx0Upper hx1Lower hy0Upper hy1Lower
  have htwoPi : 0 ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hscaled :
      (2 * Real.pi) *
          ((sigma - x0) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) ≤
        (2 * Real.pi) *
          ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
              X x0 x1 y0 y1,
            (rho.re - x0) *
              (analyticOrderNatAt
                (regularizedCarlsonZeroDetector X) rho : ℝ) :=
    mul_le_mul_of_nonneg_left hcount htwoPi
  have hedges :=
    two_pi_mul_regularizedCarlsonZeroMultiplicityWeightedRealSum_eq_four_edges
      hX hx0 hx01 hy01 hleft hright hbottom htop
  refine ⟨x0, x1, y0, y1,
    hx0Lower, hx0Upper, hx1Lower, hx1Upper, hx01,
    hy0Lower, hy0Upper, hy1Lower, hy1Upper, hy01,
    hleft, hright, hbottom, htop, ?_⟩
  calc
    (2 * Real.pi) * (sigma - x0) *
        (ZeroDensity.zeroDensityCount sigma T : ℝ) =
        (2 * Real.pi) *
          ((sigma - x0) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) := by ring
    _ ≤ (2 * Real.pi) *
        ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
            X x0 x1 y0 y1,
          (rho.re - x0) *
            (analyticOrderNatAt
              (regularizedCarlsonZeroDetector X) rho : ℝ) := hscaled
    _ = regularizedCarlsonLittlewoodFourEdges X x0 x1 y0 y1 := by
      simpa [regularizedCarlsonLittlewoodFourEdges] using hedges

/-- The zero-density counting certificate with the quantitative fixed right
edge `Re(s) = 4`. -/
theorem exists_regularizedCarlson_goodRectangle_fixedRight_zeroDensity_certificate_of_leftWindow
    {X : ℕ} (hX : 1 ≤ X) {theta sigma T : ℝ}
    (htheta : 0 < theta) (hthetaSigma : theta < sigma)
    (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      theta < x0 ∧ x0 < sigma ∧ x1 = 4 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y0 : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) ∧
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        regularizedCarlsonLittlewoodFourEdges X x0 x1 y0 y1 := by
  obtain ⟨x0, x1, y0, y1,
      hx0Lower, hx0Upper, hx1Eq, hx01,
      hy0Lower, hy0Upper, hy1Lower, hy1Upper, hy01,
      hleft, hright, hbottom, htop⟩ :=
    exists_regularizedCarlsonZeroDetector_goodRectangle_fixedRight_of_leftWindow
      hX htheta hthetaSigma hsigmaOne hT
  subst x1
  have hx0 : 0 < x0 := htheta.trans hx0Lower
  have hcount :
      (sigma - x0) * (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
            X x0 4 y0 y1,
          (rho.re - x0) *
            (analyticOrderNatAt
              (regularizedCarlsonZeroDetector X) rho : ℝ) :=
    sub_mul_zeroDensityCount_le_regularizedCarlsonWeightedZeroSum
      (x1 := 4) hX hx0 hx0Upper (by norm_num) hy0Upper hy1Lower
  have htwoPi : 0 ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hscaled :
      (2 * Real.pi) *
          ((sigma - x0) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) ≤
        (2 * Real.pi) *
          ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
              X x0 4 y0 y1,
            (rho.re - x0) *
              (analyticOrderNatAt
                (regularizedCarlsonZeroDetector X) rho : ℝ) :=
    mul_le_mul_of_nonneg_left hcount htwoPi
  have hedges :=
    two_pi_mul_regularizedCarlsonZeroMultiplicityWeightedRealSum_eq_four_edges
      hX hx0 hx01 hy01 hleft hright hbottom htop
  refine ⟨x0, 4, y0, y1,
    hx0Lower, hx0Upper, rfl, hx01,
    hy0Lower, hy0Upper, hy1Lower, hy1Upper, hy01,
    hleft, hright, hbottom, htop, ?_⟩
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

/-- Backwards-compatible counting certificate with left window
`(sigma / 2, sigma)`. -/
theorem exists_regularizedCarlson_goodRectangle_zeroDensity_certificate
    {X : ℕ} (hX : 1 ≤ X) {sigma T : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      sigma / 2 < x0 ∧ x0 < sigma ∧
      1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y0 : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) ∧
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        regularizedCarlsonLittlewoodFourEdges X x0 x1 y0 y1 := by
  exact
    exists_regularizedCarlson_goodRectangle_zeroDensity_certificate_of_leftWindow
      hX (by linarith) (by linarith) hsigmaOne hT

/-- Carlson-ready counting certificate whose left edge lies in
`(1/2, sigma)`. -/
theorem exists_regularizedCarlson_goodRectangle_zeroDensity_certificate_half
    {X : ℕ} (hX : 1 ≤ X) {sigma T : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      1 / 2 < x0 ∧ x0 < sigma ∧
      1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y0 : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) ∧
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        regularizedCarlsonLittlewoodFourEdges X x0 x1 y0 y1 := by
  exact
    exists_regularizedCarlson_goodRectangle_zeroDensity_certificate_of_leftWindow
      hX (by norm_num) hsigma hsigmaOne hT

/-- Projection of the certified good rectangle to the four-edge counting
inequality used by earlier callers. -/
theorem exists_regularizedCarlson_goodRectangle_zeroDensity_le_fourEdges
    {X : ℕ} (hX : 1 ≤ X) {sigma T : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      sigma / 2 < x0 ∧ x0 < sigma ∧
      1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        regularizedCarlsonLittlewoodFourEdges X x0 x1 y0 y1 := by
  obtain ⟨x0, x1, y0, y1,
      hx0Lower, hx0Upper, hx1Lower, hx1Upper, hx01,
      hy0Lower, hy0Upper, hy1Lower, hy1Upper, hy01,
      _hleft, _hright, _hbottom, _htop, hbound⟩ :=
    exists_regularizedCarlson_goodRectangle_zeroDensity_certificate
      hX hsigma hsigmaOne hT
  exact ⟨x0, x1, y0, y1,
    hx0Lower, hx0Upper, hx1Lower, hx1Upper, hx01,
    hy0Lower, hy0Upper, hy1Lower, hy1Upper, hy01, hbound⟩

/-- The complete endpoint-cancelled Carlson reduction with a prescribed left
window. -/
theorem exists_regularizedCarlson_goodRectangle_zeroDensity_le_logNormForm_of_leftWindow
    {X : ℕ} (hX : 1 ≤ X) {theta sigma T : ℝ}
    (htheta : 0 < theta) (hthetaSigma : theta < sigma)
    (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      theta < x0 ∧ x0 < sigma ∧
      1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        regularizedCarlsonLittlewoodLogNormForm X x0 x1 y0 y1 := by
  obtain ⟨x0, x1, y0, y1,
      hx0Lower, hx0Upper, hx1Lower, hx1Upper, hx01,
      hy0Lower, hy0Upper, hy1Lower, hy1Upper, hy01,
      hleft, hright, hbottom, htop, hbound⟩ :=
    exists_regularizedCarlson_goodRectangle_zeroDensity_certificate_of_leftWindow
      hX htheta hthetaSigma hsigmaOne hT
  have hx0 : 0 < x0 := htheta.trans hx0Lower
  have hformula :=
    regularizedCarlsonLittlewoodFourEdges_eq_logNormFormDef
      hx0 hx01 hy01 hleft hright hbottom htop
  refine ⟨x0, x1, y0, y1,
    hx0Lower, hx0Upper, hx1Lower, hx1Upper, hx01,
    hy0Lower, hy0Upper, hy1Lower, hy1Upper, hy01, ?_⟩
  exact hbound.trans_eq hformula

/-- Backwards-compatible endpoint-cancelled reduction. -/
theorem exists_regularizedCarlson_goodRectangle_zeroDensity_le_logNormForm
    {X : ℕ} (hX : 1 ≤ X) {sigma T : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      sigma / 2 < x0 ∧ x0 < sigma ∧
      1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        regularizedCarlsonLittlewoodLogNormForm X x0 x1 y0 y1 := by
  exact
    exists_regularizedCarlson_goodRectangle_zeroDensity_le_logNormForm_of_leftWindow
      hX (by linarith) (by linarith) hsigmaOne hT

/-- Carlson-ready endpoint-cancelled reduction with `1/2 < x0 < sigma`, so
the existing left-edge mean-square estimates apply to the selected
rectangle. -/
theorem exists_regularizedCarlson_goodRectangle_zeroDensity_le_logNormForm_half
    {X : ℕ} (hX : 1 ≤ X) {sigma T : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      1 / 2 < x0 ∧ x0 < sigma ∧
      1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        regularizedCarlsonLittlewoodLogNormForm X x0 x1 y0 y1 := by
  exact
    exists_regularizedCarlson_goodRectangle_zeroDensity_le_logNormForm_of_leftWindow
      hX (by norm_num) hsigma hsigmaOne hT

/-- Explicit upper endpoint for the selected Carlson left edge.  The only
integral left in this expression is the fixed low-height segment `[y0, 1]`;
all growth above height one is a finite dyadic sum. -/
noncomputable def regularizedCarlsonLeftEdgeExplicitBound
    (A : ℝ) (X : ℕ) (x0 y0 y1 : ℝ) (n : ℕ) : ℝ :=
  (∫ t in y0..1,
    Real.log ‖regularizedCarlsonZeroDetector X
      ((x0 : ℂ) + Complex.I * t)‖) +
  (∑ k ∈ Finset.range n,
    regularizedCarlsonLogNormEndpointExplicit
      A 4 X x0 ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
        (4 * (2 : ℝ) ^ k)) +
  regularizedCarlsonLogNormEndpointExplicit
    A 4 X x0 ((2 : ℝ) ^ n) y1 (4 * (2 : ℝ) ^ n)

/-- On every dyadic base height `2^n`, one selected Carlson rectangle now
simultaneously carries the counting inequality and the explicit left-edge
bound.  Consequently only the two horizontal terms and the right-edge terms
in `regularizedCarlsonLittlewoodLogNormForm` remain to be bounded. -/
theorem exists_regularizedCarlson_dyadicRectangle_count_and_leftEdgeExplicit :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma : ℝ) (n : ℕ),
      1 ≤ X → 1 / 2 < sigma → sigma < 1 →
      ∃ x0 x1 y0 y1 : ℝ,
        1 / 2 < x0 ∧ x0 < sigma ∧
        1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
        -1 < y0 ∧ y0 < 0 ∧
        (2 : ℝ) ^ n < y1 ∧ y1 < (2 : ℝ) ^ n + 1 ∧ y0 < y1 ∧
        (∀ y ∈ Set.Icc y0 y1,
          regularizedCarlsonZeroDetector X
            ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
        (∀ y ∈ Set.Icc y0 y1,
          regularizedCarlsonZeroDetector X
            ((x1 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
        (∀ x ∈ Set.Icc x0 x1,
          regularizedCarlsonZeroDetector X
            ((x : ℂ) + (y0 : ℂ) * I) ≠ 0) ∧
        (∀ x ∈ Set.Icc x0 x1,
          regularizedCarlsonZeroDetector X
            ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) ∧
        (2 * Real.pi) * (sigma - x0) *
            (ZeroDensity.zeroDensityCount sigma ((2 : ℝ) ^ n) : ℝ) ≤
          regularizedCarlsonLittlewoodLogNormForm X x0 x1 y0 y1 ∧
        (∫ y in y0..y1,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((x0 : ℂ) + (y : ℂ) * I)‖) ≤
          regularizedCarlsonLeftEdgeExplicitBound A X x0 y0 y1 n := by
  obtain ⟨A, hA, hleftBound⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_low_add_dyadicCoverExplicit
  refine ⟨A, hA, ?_⟩
  intro X sigma n hX hsigma hsigma1
  obtain ⟨x0, x1, y0, y1,
      hx0Lower, hx0Upper, hx1Lower, hx1Upper, hx01,
      hy0Lower, hy0Upper, hy1Lower, hy1Upper, hy01,
      hleft, hright, hbottom, htop, hcount⟩ :=
    exists_regularizedCarlson_goodRectangle_zeroDensity_certificate_half
      hX hsigma hsigma1 (T := (2 : ℝ) ^ n) (by positivity)
  have hx0Pos : 0 < x0 := by linarith
  have hformula :=
    regularizedCarlsonLittlewoodFourEdges_eq_logNormFormDef
      hx0Pos hx01 hy01 hleft hright hbottom htop
  have hcountLog :
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma ((2 : ℝ) ^ n) : ℝ) ≤
        regularizedCarlsonLittlewoodLogNormForm X x0 x1 y0 y1 :=
    hcount.trans_eq hformula
  have hpowOne : 1 ≤ (2 : ℝ) ^ n :=
    one_le_pow₀ (by norm_num)
  have hy1Step : y1 ≤ (2 : ℝ) ^ (n + 1) := by
    have hstep : (2 : ℝ) ^ n + 1 ≤ (2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      nlinarith
    exact hy1Upper.le.trans hstep
  have hleft' : ∀ t ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht
    simpa [mul_comm] using hleft t ht
  have hleftExplicit := hleftBound X x0 y0 y1 n hX hx0Lower
    (hx0Upper.trans hsigma1) (by linarith) hy1Lower.le hy1Step hleft'
  refine ⟨x0, x1, y0, y1,
    hx0Lower, hx0Upper, hx1Lower, hx1Upper, hx01,
    hy0Lower, hy0Upper, hy1Lower, hy1Upper, hy01,
    hleft, hright, hbottom, htop, hcountLog, ?_⟩
  simpa [regularizedCarlsonLeftEdgeExplicitBound, mul_comm] using hleftExplicit

end CarlsonZeroDensity
end PrimeNumberTheorem
