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

/-- Carlson's zero-density count is reduced to the four Littlewood edge
integrals on an automatically selected zero-free rectangle. -/
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
      hleft, hright, hbottom, htop⟩ :=
    exists_regularizedCarlsonZeroDetector_goodRectangle
      hX hsigma hsigmaOne hT
  have hx0 : 0 < x0 := (by linarith : 0 < sigma / 2).trans hx0Lower
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
    hy0Lower, hy0Upper, hy1Lower, hy1Upper, hy01, ?_⟩
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

end CarlsonZeroDensity
end PrimeNumberTheorem
