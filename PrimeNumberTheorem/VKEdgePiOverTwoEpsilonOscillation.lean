import PrimeNumberTheorem.VKEdgePiOverTwoCenteredMissingHarmonicContour
import PrimeNumberTheorem.VKEdgePiOverTwoEpsilonWindow

open Complex Filter Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The epsilon-window Gaussian center is uniformly large enough for the
centered contour estimates. -/
theorem epsilonCenterCoefficient_ge_sixteen {ε : ℝ} (hε : 0 < ε) :
    16 ≤ epsilonCenterCoefficient ε := by
  unfold epsilonCenterCoefficient
  field_simp [hε.ne']
  nlinarith

/-- The epsilon-window radius satisfies the margin needed to control the
centered contour and the true Chebyshev-error tails. -/
theorem epsilonRadius_sq_ge_sixteen_mul {ε : ℝ} (hε : 0 < ε) :
    16 * (epsilonCenterCoefficient ε + epsilonRadiusCoefficient ε) ≤
      epsilonRadiusCoefficient ε ^ 2 := by
  have hd := epsilonRadiusCoefficient_pos hε
  have hdq := epsilonRadiusCoefficient_lt_center hε
  have hstrong := epsilonRadius_sq_ge_thirtyTwo_mul hε
  nlinarith

/-- The Gaussian scale attached to a fixed positive epsilon tends to infinity
with the lower endpoint of the power window. -/
theorem tendsto_epsilonGaussianScale_atTop {ε : ℝ} (hε : 0 < ε) :
    Tendsto (epsilonGaussianScale ε) atTop atTop := by
  have hgap :
      0 <
        epsilonCenterCoefficient ε -
          epsilonRadiusCoefficient ε :=
    sub_pos.mpr (epsilonRadiusCoefficient_lt_center hε)
  have h :=
    Real.tendsto_log_atTop.const_mul_atTop
      (show 0 <
          (epsilonCenterCoefficient ε -
            epsilonRadiusCoefficient ε)⁻¹ by
        exact inv_pos.mpr hgap)
  change Tendsto (fun Y : ℝ => epsilonGaussianScale ε Y) atTop atTop
  simpa [epsilonGaussianScale, div_eq_mul_inv, mul_comm] using h

/--
A fixed missing odd harmonic forces a multiplicity-sensitive oscillation
strictly larger than `pi / 2` in every sufficiently late power window
`[Y, Y^(1+ε)]`.
-/
theorem
    eventually_exists_psiError_in_powerOnePlusEpsilonWindow_gt_strictPiOverTwo
    {ε : ℝ} {rho : ℂ} {k : ℕ}
    (hε : 0 < ε)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hmissing :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0) :
    ∀ᶠ Y : ℝ in atTop,
      ∃ x ∈ powerOnePlusEpsilonWindow ε Y,
        (analyticOrderNatAt riemannZeta rho : ℝ) *
              strictPiOverTwoOscillationConstant k *
              (x ^ rho.re / ‖rho‖) <
            |chebyshevPsi x - x| := by
  have hrho0 : rho ≠ 0 := ne_zero_of_re_pos hrhoRe0
  have hrho1 : rho ≠ 1 := by
    intro hrho
    have hre := congrArg Complex.re hrho
    norm_num at hre
    linarith
  have hmultiplicity :
      0 < (analyticOrderNatAt riemannZeta rho : ℝ) := by
    exact_mod_cast
      ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        hrho1 hzero
  have hconstant :
      (analyticOrderNatAt riemannZeta rho : ℝ) *
          strictPiOverTwoOscillationConstant k <
        (analyticOrderNatAt riemannZeta rho : ℝ) /
          sharpenedMissingHarmonicDenominator k := by
    rw [show
        (analyticOrderNatAt riemannZeta rho : ℝ) /
              sharpenedMissingHarmonicDenominator k =
            (analyticOrderNatAt riemannZeta rho : ℝ) *
              sharpenedMissingHarmonicLowerBound k by
      unfold sharpenedMissingHarmonicLowerBound
      ring]
    exact mul_lt_mul_of_pos_left
      (strictPiOverTwoOscillationConstant_lt_lowerBound k)
      hmultiplicity
  have hlocalAtTop :
      ∀ᶠ m : ℝ in atTop,
        ∃ y ∈ localizedGaussianLogWindow
            (epsilonCenterCoefficient ε)
            (epsilonRadiusCoefficient ε) m,
          (analyticOrderNatAt riemannZeta rho : ℝ) *
              strictPiOverTwoOscillationConstant k <
            |normalizedPsiError rho y| :=
    eventually_exists_normalizedPsiError_in_centeredWindow_gt
      (epsilonCenterCoefficient_ge_sixteen hε)
      (epsilonRadiusCoefficient_pos hε)
      (epsilonRadiusCoefficient_lt_center hε)
      (epsilonRadius_sq_ge_sixteen_mul hε)
      hrhoRe0 hrhoRe1 hgamma hzero hmissing hconstant
  have hlocalY :=
    (tendsto_epsilonGaussianScale_atTop hε).eventually hlocalAtTop
  filter_upwards [hlocalY, eventually_ge_atTop (1 : ℝ)] with Y hlocal hY
  exact
    exists_psiError_in_powerOnePlusEpsilonWindow_of_normalizedPsiError
      hrho0 hε hY hlocal

/--
Carlson zero density selects the missing odd harmonic. The resulting
conditional oscillation theorem retains the exact analytic multiplicity and
the strict fixed-harmonic constant in every late epsilon power window.
-/
theorem
    exists_eventually_psiError_in_powerOnePlusEpsilonWindow_gt_strictPiOverTwo
    {ε : ℝ} {rho : ℂ} {sigma : ℝ}
    (hε : 0 < ε)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hσ : 1 / 2 < sigma)
    (hσrho : sigma < rho.re)
    (hrhoRe1 : rho.re < 1) :
    ∃ k : ℕ,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      Real.pi / 2 < strictPiOverTwoOscillationConstant k ∧
      ∀ᶠ Y : ℝ in atTop,
        ∃ x ∈ powerOnePlusEpsilonWindow ε Y,
          (analyticOrderNatAt riemannZeta rho : ℝ) *
                strictPiOverTwoOscillationConstant k *
                (x ^ rho.re / ‖rho‖) <
              |chebyshevPsi x - x| := by
  have hrhoRe0 : 0 < rho.re := by linarith
  rcases
      exists_missing_oddHarmonic_with_strict_gap_of_carlson
        hrhoRe1 hgamma hσ hσrho with
    ⟨k, hmissing, _hOldGap⟩
  have hmissing' :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 := by
    simpa [missingHarmonicContourCenter] using hmissing
  exact
    ⟨k, hmissing',
      pi_div_two_lt_strictPiOverTwoOscillationConstant k,
      eventually_exists_psiError_in_powerOnePlusEpsilonWindow_gt_strictPiOverTwo
        hε hrhoRe0 hrhoRe1 hgamma hzero hmissing'⟩

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
