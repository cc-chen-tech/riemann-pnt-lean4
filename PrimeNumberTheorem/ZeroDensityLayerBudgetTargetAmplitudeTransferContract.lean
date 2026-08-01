import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeTransfer

open Filter Topology

namespace PrimeNumberTheorem

/-! Public contract for target-amplitude normalized remainder transfer. -/

example
    {amplitude remainder : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in atTop, 0 < amplitude x)
    (hnegligible : TargetAmplitudeNegligible amplitude remainder)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ x in atTop, |remainder x| < epsilon * amplitude x :=
  eventually_abs_lt_mul_of_targetAmplitudeNegligible
    hamplitude hnegligible hepsilon

example
    {amplitude realAxis contour complement : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in atTop, 0 < amplitude x)
    (hrealAxis : TargetAmplitudeNegligible amplitude realAxis)
    (hcontour : TargetAmplitudeNegligible amplitude contour)
    (hcomplement : TargetAmplitudeNegligible amplitude complement) :
    ∀ᶠ x in atTop,
      |realAxis x + contour x + complement x| < amplitude x / 2 :=
  eventually_abs_realAxis_add_contour_add_complement_lt_half
    hamplitude hrealAxis hcontour hcomplement

example
    {amplitude main remainder error : ℝ}
    (hmain : amplitude ≤ |main|)
    (hremainder : |remainder| ≤ amplitude / 2)
    (hdecomp : error = main + remainder) :
    amplitude / 2 ≤ |error| :=
  half_targetAmplitude_le_abs_error hmain hremainder hdecomp

example
    {amplitude main realAxis contour complement error : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in atTop, 0 < amplitude x)
    (hrealAxis : TargetAmplitudeNegligible amplitude realAxis)
    (hcontour : TargetAmplitudeNegligible amplitude contour)
    (hcomplement : TargetAmplitudeNegligible amplitude complement)
    (hmain : HasFarTargetAmplitudeWitness main amplitude)
    (hdecomp :
      ∀ x : ℝ,
        error x = main x + (realAxis x + contour x + complement x)) :
    HasFarTargetAmplitudeWitness error (fun x => amplitude x / 2) :=
  hasFarTargetAmplitudeWitness_of_three_normalized_remainders
    hamplitude hrealAxis hcontour hcomplement hmain hdecomp

end PrimeNumberTheorem
