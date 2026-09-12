import PrimeNumberTheorem.MWKFCubicEulerAnalytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Separate holomorphy of the cubic Euler correction

The locally uniform Euler product is pulled back along analytic one-dimensional
slices.  The complex Weierstrass theorem then proves analyticity of the global
product on each coordinate half-plane.  This is the sequential contour-shift
interface; it does not assert a multivariable locally-uniform-limit theorem.
-/

/-- The one-variable half-plane used by each coordinate slice. -/
def mwkfEulerHalfPlane (eta : ℝ) : Set ℂ :=
  {z | -eta < z.re}

theorem isOpen_mwkfEulerHalfPlane (eta : ℝ) :
    IsOpen (mwkfEulerHalfPlane eta) := by
  exact isOpen_lt continuous_const (by fun_prop)

/-- An analytic slice of the three-variable Euler product is analytic whenever
it stays in a strip on which the correction product converges locally
uniformly. -/
theorem analyticOnNhd_mwkfEulerCorrection_comp
    {eta : ℝ} (hetaQuarter : eta < 1 / 4) {U : Set ℂ}
    (hU : IsOpen U) {slice : ℂ → ℂ × ℂ × ℂ}
    (hslice : AnalyticOnNhd ℂ slice U)
    (hmaps : Set.MapsTo slice U (mwkfEulerOpenStrip eta)) :
    AnalyticOnNhd ℂ
      (fun z ↦ mwkfEulerCorrection (slice z).1 (slice z).2.1 (slice z).2.2) U := by
  have hprod :=
    (hasProdLocallyUniformlyOn_mwkfPrimeCorrectionFactor hetaQuarter).comp
      slice hmaps hslice.continuousOn
  have hfinite : ∀ S : Finset Nat.Primes,
      DifferentiableOn ℂ
        (fun z ↦ ∏ p ∈ S,
          mwkfPrimeCorrectionFactor p (slice z).1 (slice z).2.1 (slice z).2.2) U := by
    intro S
    apply AnalyticOnNhd.differentiableOn
    apply S.analyticOnNhd_fun_prod (A := ℂ)
    intro p hp
    change AnalyticOnNhd ℂ
      ((fun z : ℂ × ℂ × ℂ ↦
        mwkfPrimeCorrectionFactor p z.1 z.2.1 z.2.2) ∘ slice) U
    exact (analyticOnNhd_mwkfPrimeCorrectionFactor_openStrip p
      (by linarith : eta < 1 / 2)).comp hslice hmaps
  apply (Complex.analyticOnNhd_iff_differentiableOn hU).2
  exact hprod.differentiableOn (Filter.Eventually.of_forall hfinite) hU

/-- With the other two variables fixed inside the strip, the global correction
is analytic in its first variable on the corresponding half-plane. -/
theorem analyticOnNhd_mwkfEulerCorrection_in_first
    {eta : ℝ} (hetaQuarter : eta < 1 / 4) {t w : ℂ}
    (ht : -eta < t.re) (hw : -eta < w.re) :
    AnalyticOnNhd ℂ (fun s ↦ mwkfEulerCorrection s t w)
      (mwkfEulerHalfPlane eta) := by
  let slice : ℂ → ℂ × ℂ × ℂ := fun s ↦ (s, t, w)
  have hslice : AnalyticOnNhd ℂ slice (mwkfEulerHalfPlane eta) := by
    dsimp [slice]
    exact analyticOnNhd_id.prod (analyticOnNhd_const.prod analyticOnNhd_const)
  have hmaps : Set.MapsTo slice (mwkfEulerHalfPlane eta)
      (mwkfEulerOpenStrip eta) := by
    intro s hs
    exact ⟨hs, ht, hw⟩
  simpa [slice] using analyticOnNhd_mwkfEulerCorrection_comp
    hetaQuarter (isOpen_mwkfEulerHalfPlane eta) hslice hmaps

/-- With the other two variables fixed inside the strip, the global correction
is analytic in its second variable on the corresponding half-plane. -/
theorem analyticOnNhd_mwkfEulerCorrection_in_second
    {eta : ℝ} (hetaQuarter : eta < 1 / 4) {s w : ℂ}
    (hs : -eta < s.re) (hw : -eta < w.re) :
    AnalyticOnNhd ℂ (fun t ↦ mwkfEulerCorrection s t w)
      (mwkfEulerHalfPlane eta) := by
  let slice : ℂ → ℂ × ℂ × ℂ := fun t ↦ (s, t, w)
  have hslice : AnalyticOnNhd ℂ slice (mwkfEulerHalfPlane eta) := by
    dsimp [slice]
    exact analyticOnNhd_const.prod (analyticOnNhd_id.prod analyticOnNhd_const)
  have hmaps : Set.MapsTo slice (mwkfEulerHalfPlane eta)
      (mwkfEulerOpenStrip eta) := by
    intro t ht
    exact ⟨hs, ht, hw⟩
  simpa [slice] using analyticOnNhd_mwkfEulerCorrection_comp
    hetaQuarter (isOpen_mwkfEulerHalfPlane eta) hslice hmaps

/-- With the other two variables fixed inside the strip, the global correction
is analytic in its third variable on the corresponding half-plane. -/
theorem analyticOnNhd_mwkfEulerCorrection_in_third
    {eta : ℝ} (hetaQuarter : eta < 1 / 4) {s t : ℂ}
    (hs : -eta < s.re) (ht : -eta < t.re) :
    AnalyticOnNhd ℂ (fun w ↦ mwkfEulerCorrection s t w)
      (mwkfEulerHalfPlane eta) := by
  let slice : ℂ → ℂ × ℂ × ℂ := fun w ↦ (s, t, w)
  have hslice : AnalyticOnNhd ℂ slice (mwkfEulerHalfPlane eta) := by
    dsimp [slice]
    exact analyticOnNhd_const.prod (analyticOnNhd_const.prod analyticOnNhd_id)
  have hmaps : Set.MapsTo slice (mwkfEulerHalfPlane eta)
      (mwkfEulerOpenStrip eta) := by
    intro w hw
    exact ⟨hs, ht, hw⟩
  simpa [slice] using analyticOnNhd_mwkfEulerCorrection_comp
    hetaQuarter (isOpen_mwkfEulerHalfPlane eta) hslice hmaps

end PrimeNumberTheorem.MWKFCubic
