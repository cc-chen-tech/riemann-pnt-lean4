import PrimeNumberTheorem.CarlsonTwoScaleRectangle
import PrimeNumberTheorem.LittlewoodRectangleZeroCount

/-! Littlewood's identity for the actual two-scale detector-zero support.
Regularization preserves multiplicities away from 0 and 1. -/

open Complex Filter Set
open scoped BigOperators Topology

namespace PrimeNumberTheorem.CarlsonZeroDensity

theorem analyticOrderNatAt_regularizedTwoScale_eq {Y0 Y1 : ℕ} {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    analyticOrderNatAt (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) s =
      analyticOrderNatAt (twoScaleCarlsonZeroDetector Y0 Y1) s := by
  let p : ℂ → ℂ := fun z => (z - 1) ^ (2 : ℕ)
  have hp : AnalyticAt ℂ p s := (analyticAt_id.sub analyticAt_const).pow 2
  have hp0 : analyticOrderAt p s = 0 :=
    hp.analyticOrderAt_eq_zero.mpr (pow_ne_zero 2 (sub_ne_zero.mpr hs1))
  have hfactor : regularizedTwoScaleCarlsonZeroDetector Y0 Y1 =ᶠ[𝓝 s]
      p * twoScaleCarlsonZeroDetector Y0 Y1 := by
    filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with z hz0 hz1
    exact regularizedTwoScaleCarlsonZeroDetector_eq_sub_one_sq_mul hz0 hz1
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr hfactor,
    analyticOrderAt_mul hp (analyticAt_twoScaleCarlsonZeroDetector_of_ne_one Y0 Y1 hs1),
    hp0, zero_add]

theorem analyticOrderNatAt_riemannZeta_le_regularizedTwoScale
    {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) {rho : ℂ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    analyticOrderNatAt riemannZeta rho ≤
      analyticOrderNatAt (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) rho := by
  have hrho0 : rho ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    linarith [hrho.2.1]
  have hrho1 : rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.one_re] at hre
    linarith [hrho.2.2]
  rw [analyticOrderNatAt_regularizedTwoScale_eq hrho0 hrho1]
  exact analyticOrderNatAt_riemannZeta_le_twoScaleCarlsonZeroDetector hY0 hY01 hrho

/-- The finite support is the actual detector support, not arbitrary
user-supplied zero data.  The only boundary premises are nonvanishing. -/
theorem two_pi_mul_twoScaleRectangleZeroSum_eq_logNormForm
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {x0 x1 y0 y1 : ℝ} (hx0 : 0 < x0) (hx : x0 ≤ x1) (hy : y0 ≤ y1)
    (hleft : ∀ y ∈ Icc y0 y1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x0 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ Icc y0 y1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x1 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hbottom : ∀ x ∈ Icc x0 x1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Icc x0 x1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    (2 * Real.pi) * ∑ z ∈ regularizedTwoScaleCarlsonRectangleDivisorSupport Y0 Y1 x0 x1 y0 y1,
      (z.re - x0) * (analyticOrderNatAt (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) z : ℝ) =
      rectangleLittlewoodLogNormForm (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) x0 x1 y0 y1 := by
  let f := regularizedTwoScaleCarlsonZeroDetector Y0 Y1
  let K := carlsonDetectorRectangle x0 x1 y0 y1
  let D := MeromorphicOn.divisor f K
  let P := regularizedTwoScaleCarlsonRectangleDivisorSupport Y0 Y1 x0 x1 y0 y1
  have hmem {z : ℂ} (hz : z ∈ P) : z ∈ K := by
    have hsupp : z ∈ D.support :=
      (D.finiteSupport (isCompact_carlsonDetectorRectangle x0 x1 y0 y1)).mem_toFinset.mp hz
    exact D.supportWithinDomain hsupp
  have hf : AnalyticOnNhd ℂ f K := by
    intro z hz
    exact analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl Y0 Y1 z (hx0.trans_le hz.1.1)
  have hzero : ∀ z ∈ K, f z = 0 ↔ z ∈ P := by
    intro z hz
    exact (mem_regularizedTwoScaleCarlsonRectangleDivisorSupport_iff_zero hY0 hY01 hx0 hz).symm
  have horder : ∀ z ∈ P, analyticOrderAt f z = analyticOrderNatAt f z := by
    intro z hz
    exact (Nat.cast_analyticOrderNatAt
      (analyticOrderAt_regularizedTwoScaleCarlsonZeroDetector_ne_top hY0 hY01
        (hx0.trans_le (hmem hz).1.1))).symm
  have hinterior : ∀ z ∈ P, x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1 := by
    intro z hz
    have hzK := hmem hz
    have hfzero := (hzero z hzK).mpr hz
    have hre0 : z.re ≠ x0 := by
      intro heq
      apply hleft z.im hzK.2
      have hzEq : (x0 : ℂ) + (z.im : ℂ) * I = z := by apply Complex.ext <;> simp [heq]
      rw [hzEq]
      exact hfzero
    have hre1 : z.re ≠ x1 := by
      intro heq
      apply hright z.im hzK.2
      have hzEq : (x1 : ℂ) + (z.im : ℂ) * I = z := by apply Complex.ext <;> simp [heq]
      rw [hzEq]
      exact hfzero
    have him0 : z.im ≠ y0 := by
      intro heq
      apply hbottom z.re hzK.1
      have hzEq : (z.re : ℂ) + (y0 : ℂ) * I = z := by apply Complex.ext <;> simp [heq]
      rw [hzEq]
      exact hfzero
    have him1 : z.im ≠ y1 := by
      intro heq
      apply htop z.re hzK.1
      have hzEq : (z.re : ℂ) + (y1 : ℂ) * I = z := by apply Complex.ext <;> simp [heq]
      rw [hzEq]
      exact hfzero
    exact ⟨lt_of_le_of_ne hzK.1.1 (Ne.symm hre0), lt_of_le_of_ne hzK.1.2 hre1,
      lt_of_le_of_ne hzK.2.1 (Ne.symm him0), lt_of_le_of_ne hzK.2.2 him1⟩
  exact two_pi_mul_zeroMultiplicityWeightedRealSum_eq_logNormForm hx hy P
    (analyticOrderNatAt f) hf hzero horder hinterior

/-- Any finite family of actual zeta zeros is counted with its zeta
multiplicities.  The real threshold is closed (`sigma ≤ rho.re`), so this
comparison does not discard zeros on the target vertical line. -/
theorem two_pi_mul_twoScaleZetaFamilyCount_le_logNormForm
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {sigma x0 x1 y0 y1 : ℝ} (hx0 : 0 < x0) (hx : x0 ≤ x1)
    (hxSigma : x0 ≤ sigma) (hx1 : 1 ≤ x1) (hy : y0 ≤ y1)
    (S : Finset ℂ)
    (hS : ∀ rho ∈ S, RiemannHypothesis.IsNontrivialZero rho ∧
      sigma ≤ rho.re ∧ y0 ≤ rho.im ∧ rho.im ≤ y1)
    (hleft : ∀ y ∈ Icc y0 y1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x0 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ Icc y0 y1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x1 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hbottom : ∀ x ∈ Icc x0 x1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Icc x0 x1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    (2 * Real.pi) * ((sigma - x0) * ∑ rho ∈ S, (analyticOrderNatAt riemannZeta rho : ℝ)) ≤
      rectangleLittlewoodLogNormForm (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) x0 x1 y0 y1 := by
  classical
  let f := regularizedTwoScaleCarlsonZeroDetector Y0 Y1
  let K := carlsonDetectorRectangle x0 x1 y0 y1
  let P := regularizedTwoScaleCarlsonRectangleDivisorSupport Y0 Y1 x0 x1 y0 y1
  have hSsub : S ⊆ P := by
    intro rho hrhoS
    obtain ⟨hrho, hre, him0, him1⟩ := hS rho hrhoS
    have hrhoK : rho ∈ K :=
      ⟨⟨hxSigma.trans hre, hrho.2.2.le.trans hx1⟩, him0, him1⟩
    have hrho0 : rho ≠ 0 := by
      intro heq
      have hre0 := hrho.2.1
      simpa [heq] using hre0
    have hrho1 : rho ≠ 1 := by
      intro heq
      have hre1 := hrho.2.2
      simpa [heq] using hre1
    apply (mem_regularizedTwoScaleCarlsonRectangleDivisorSupport_iff_zero
      hY0 hY01 hx0 hrhoK).mpr
    rw [regularizedTwoScaleCarlsonZeroDetector_eq_sub_one_sq_mul hrho0 hrho1,
      twoScaleCarlsonZeroDetector_eq_zero_of_zeta_eq_zero hrho.1, mul_zero]
  have hPnonneg : ∀ rho ∈ P, 0 ≤ (rho.re - x0) * (analyticOrderNatAt f rho : ℝ) := by
    intro rho hrho
    let D := MeromorphicOn.divisor f K
    have hsupp : rho ∈ D.support :=
      (D.finiteSupport (isCompact_carlsonDetectorRectangle x0 x1 y0 y1)).mem_toFinset.mp hrho
    have hrhoK := D.supportWithinDomain hsupp
    exact mul_nonneg (sub_nonneg.mpr hrhoK.1.1) (Nat.cast_nonneg _)
  have hsum : (sigma - x0) * ∑ rho ∈ S, (analyticOrderNatAt riemannZeta rho : ℝ) ≤
      ∑ rho ∈ P, (rho.re - x0) * (analyticOrderNatAt f rho : ℝ) := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ rho ∈ S, (rho.re - x0) * (analyticOrderNatAt f rho : ℝ) := by
        apply Finset.sum_le_sum
        intro rho hrhoS
        obtain ⟨hrho, hre, _, _⟩ := hS rho hrhoS
        have hmult : (analyticOrderNatAt riemannZeta rho : ℝ) ≤
            (analyticOrderNatAt f rho : ℝ) := by
          exact_mod_cast analyticOrderNatAt_riemannZeta_le_regularizedTwoScale
            (by omega : 1 ≤ Y0) hY01 hrho
        exact mul_le_mul (sub_le_sub_right hre x0) hmult (Nat.cast_nonneg _)
          (sub_nonneg.mpr (hxSigma.trans hre))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun rho hrho _ => hPnonneg rho hrho)
  calc
    _ ≤ (2 * Real.pi) * ∑ rho ∈ P, (rho.re - x0) * (analyticOrderNatAt f rho : ℝ) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := two_pi_mul_twoScaleRectangleZeroSum_eq_logNormForm
      hY0 hY01 hx0 hx hy hleft hright hbottom htop

end PrimeNumberTheorem.CarlsonZeroDensity
