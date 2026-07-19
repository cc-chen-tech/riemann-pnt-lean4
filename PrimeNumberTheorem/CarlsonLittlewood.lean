import PrimeNumberTheorem.CarlsonDetectorCount
import PrimeNumberTheorem.LittlewoodRectangle

open Complex Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

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

end CarlsonZeroDensity
end PrimeNumberTheorem
