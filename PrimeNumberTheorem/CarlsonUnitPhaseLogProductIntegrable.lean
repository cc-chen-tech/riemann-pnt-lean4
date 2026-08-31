import HardyTheorem.AFECriticalUnitPhaseLogWindow
import PrimeNumberTheorem.CarlsonHalfRangeProductIntegrable

/-!
# Full-line Carlson product moment from the weaker critical AFE

The central window uses only an existential unit phase and a
`t^(-1/4) (1 + log t)` remainder.  The existing unconditional Gaussian tail
estimate supplies the complement.  Thus the sharp phase and sharp
logarithm-free AFE are not analytic gates for the half-range Carlson route.
-/

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Conditional full-line critical product bound at the simple Carlson
scale, assuming only the weaker unit-phase logarithmic AFE target. -/
theorem integral_gaussian_product_le_halfRange_simpleScale_of_unitPhase_log_target
    (hAFE : HardyTheorem.AFE.zeta_critical_unitPhase_logAfe_target) :
    ∃ R > (0 : ℝ), ∀ᶠ V : ℝ in atTop, ∀ (w : ℝ) (X : ℕ),
      2 * V ≤ w → w ≤ 3 * V → 2 ≤ X →
      (X : ℝ) ≤ V ^ (9 / 20 : ℝ) →
      (∫ t : ℝ,
        carlsonGaussianWeight (16 * V ^ (19 / 20 : ℝ)) w t *
          ‖linearLogSelbergMollifiedZetaProduct X
            ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) ≤
        3 * Real.sqrt
          (Real.pi / (1 / (16 * V ^ (19 / 20 : ℝ)) ^ 2)) *
          (256 * MathlibAux.gaussianBucketSchurConstant *
              (1 + Real.log (4 * V)) ^ 6 + 4 * R ^ 2) + 1 := by
  obtain ⟨R, T0, hR, hT0, hwindow⟩ :=
    HardyTheorem.AFE.setIntegral_gaussian_normSq_criticalAfeProduct_le_of_unitPhase_log_target
      hAFE
  refine ⟨R, hR, ?_⟩
  filter_upwards
      [eventually_ge_atTop (max T0 2),
        exists_eventually_carlsonHalfRangeProductTail_le_one_simpleScale,
        HardyTheorem.AFE.eventually_halfRange_logRemainderFactor_le_one]
      with V hV htail hlogRemainder
  intro w X hwLower hwUpper hX hXscale
  have hT0V : T0 ≤ V := (le_max_left T0 2).trans hV
  have hVtwo : 2 ≤ V := (le_max_right T0 2).trans hV
  have hVone : 1 ≤ V := by linarith
  have hVgt : 1 < V := by linarith
  have hVpos : 0 < V := by linarith
  have hFourV : 4 ≤ 4 * V := by nlinarith
  have hTwoPi : 2 * Real.pi ≤ 4 * V := by
    nlinarith [Real.pi_lt_four]
  obtain ⟨hSqrtOne, hSqrtUpper⟩ :=
    HardyTheorem.AFE.criticalHalfRange_sqrt_scale_bounds hTwoPi hFourV
  obtain ⟨K, hKlower, hKupper⟩ :=
    HardyTheorem.AFE.exists_dyadic_strict_upper_le_two_mul hSqrtOne
  have hDeltaFrequency :
      4 * Real.sqrt ((4 * V) / (2 * Real.pi)) * (X : ℝ) ≤
        16 * V ^ (19 / 20 : ℝ) :=
    four_mul_sqrt_fourV_scale_mul_length_le_simpleScale hVone hXscale
  have hseparation :
      2 * (((2 ^ K * X : ℕ) : ℝ)) ≤
        16 * V ^ (19 / 20 : ℝ) := by
    calc
      2 * (((2 ^ K * X : ℕ) : ℝ)) =
          2 * (((2 ^ K : ℕ) : ℝ)) * (X : ℝ) := by
        rw [Nat.cast_mul]
        ring
      _ ≤ 2 * (2 * Real.sqrt ((4 * V) / (2 * Real.pi))) *
          (X : ℝ) := by
        gcongr
      _ = 4 * Real.sqrt ((4 * V) / (2 * Real.pi)) *
          (X : ℝ) := by ring
      _ ≤ 16 * V ^ (19 / 20 : ℝ) := hDeltaFrequency
  have hcentralRaw := hwindow (K := K) (X := X) (L := V) (U := 4 * V)
    (Delta := 16 * V ^ (19 / 20 : ℝ)) hT0V hVgt hX hKlower
      hseparation w
  have hKU : (((2 ^ K : ℕ) : ℝ)) ≤ 4 * V :=
    hKupper.trans hSqrtUpper
  have hXFourV : (X : ℝ) ≤ (4 * V) ^ (9 / 20 : ℝ) :=
    hXscale.trans
      (Real.rpow_le_rpow hVpos.le (by nlinarith) (by norm_num))
  have hdyadic := HardyTheorem.AFE.dyadicCriticalGaussianBound_le_halfRange_log
    (show 1 ≤ 4 * V by nlinarith) (show 1 ≤ X by omega) hKU hXFourV
      (Delta := 16 * V ^ (19 / 20 : ℝ))
  have hremRaw :=
    HardyTheorem.AFE.criticalAfeLogRemainderWindowBound_le_halfRange
      (R := R) (U := 4 * V) hVone hXscale
  have hrem :
      HardyTheorem.AFE.criticalAfeLogRemainderWindowBound R V (4 * V) X ≤
        4 * R ^ 2 := by
    calc
      _ ≤ 4 * R ^ 2 * V ^ (-1 / 20 : ℝ) *
          (1 + Real.log (4 * V)) ^ 2 := hremRaw
      _ = 4 * R ^ 2 *
          (V ^ (-1 / 20 : ℝ) * (1 + Real.log (4 * V)) ^ 2) := by ring
      _ ≤ 4 * R ^ 2 * 1 := by
        gcongr
      _ = 4 * R ^ 2 := by ring
  have hcentral :
      (∫ t : ℝ in Icc V (4 * V),
        Real.exp (-((t - w) ^ 2) /
            (16 * V ^ (19 / 20 : ℝ)) ^ 2) *
          Complex.normSq
            (riemannZeta ((1 / 2 : ℂ) + I * t) *
              HardyTheorem.selbergMoebiusMollifier X
                ((1 / 2 : ℂ) + I * t))) ≤
        3 * Real.sqrt
          (Real.pi / (1 / (16 * V ^ (19 / 20 : ℝ)) ^ 2)) *
          (256 * MathlibAux.gaussianBucketSchurConstant *
              (1 + Real.log (4 * V)) ^ 6 + 4 * R ^ 2) := by
    calc
      _ ≤ 3 *
          (2 * HardyTheorem.AFE.dyadicCriticalGaussianBound K X
              (16 * V ^ (19 / 20 : ℝ)) +
            Real.sqrt
                (Real.pi / (1 / (16 * V ^ (19 / 20 : ℝ)) ^ 2)) *
              HardyTheorem.AFE.criticalAfeLogRemainderWindowBound
                R V (4 * V) X) := hcentralRaw
      _ ≤ 3 *
          (2 *
              (128 * Real.sqrt
                  (Real.pi / (1 / (16 * V ^ (19 / 20 : ℝ)) ^ 2)) *
                MathlibAux.gaussianBucketSchurConstant *
                  (1 + Real.log (4 * V)) ^ 6) +
            Real.sqrt
                (Real.pi / (1 / (16 * V ^ (19 / 20 : ℝ)) ^ 2)) *
              (4 * R ^ 2)) := by
        gcongr
      _ = _ := by ring
  have hcentral' :
      (∫ t : ℝ in Icc V (4 * V),
        carlsonGaussianWeight (16 * V ^ (19 / 20 : ℝ)) w t *
          ‖linearLogSelbergMollifiedZetaProduct X
            ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) ≤
        3 * Real.sqrt
          (Real.pi / (1 / (16 * V ^ (19 / 20 : ℝ)) ^ 2)) *
          (256 * MathlibAux.gaussianBucketSchurConstant *
              (1 + Real.log (4 * V)) ^ 6 + 4 * R ^ 2) := by
    simpa only [carlsonGaussianWeight,
      linearLogSelbergMollifiedZetaProduct,
      HardyTheorem.linearLogSelbergMollifier_eq_selbergMoebiusMollifier,
      Complex.normSq_eq_norm_sq] using hcentral
  have hDelta : 0 < 16 * V ^ (19 / 20 : ℝ) := by positivity
  calc
    (∫ t : ℝ,
        carlsonGaussianWeight (16 * V ^ (19 / 20 : ℝ)) w t *
          ‖linearLogSelbergMollifiedZetaProduct X
            ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) =
      (∫ t : ℝ in Icc V (4 * V),
        carlsonGaussianWeight (16 * V ^ (19 / 20 : ℝ)) w t *
          ‖linearLogSelbergMollifiedZetaProduct X
            ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) +
        carlsonHalfRangeProductTail
          (16 * V ^ (19 / 20 : ℝ)) w X V (4 * V) :=
      integral_gaussian_product_eq_setIntegral_add_tail
        (L := V) (U := 4 * V) hDelta hX
    _ ≤ 3 * Real.sqrt
          (Real.pi / (1 / (16 * V ^ (19 / 20 : ℝ)) ^ 2)) *
          (256 * MathlibAux.gaussianBucketSchurConstant *
              (1 + Real.log (4 * V)) ^ 6 + 4 * R ^ 2) + 1 :=
      add_le_add hcentral' (htail w X hwLower hwUpper hX hXscale)

end CarlsonZeroDensity
end PrimeNumberTheorem
