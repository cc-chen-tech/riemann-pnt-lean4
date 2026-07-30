import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTThresholdOptimization

open Filter Topology

namespace PrimeNumberTheorem

/-!
# Target-amplitude normalized remainder transfer

Ordinary convergence `remainder x -> 0` is insufficient for a zero-forced
oscillation argument when the target-zero amplitude also tends to zero.  The
correct input is the normalized statement

`|remainder x| / amplitude x -> 0`.

This module combines normalized real-axis, contour, and complementary-zero
remainders and transfers a far main-term witness to the actual error.  It does
not prove the complementary-zero normalized estimate; that remains the
explicit mathematical input required from the complementary-zero analysis.
-/

/-- A remainder is negligible relative to a scale-dependent target amplitude
when its absolute ratio tends to zero. -/
def TargetAmplitudeNegligible
    (amplitude remainder : ℝ → ℝ) : Prop :=
  Tendsto
    (fun x : ℝ => |remainder x| / amplitude x)
    atTop (𝓝 0)

/-- A normalized little remainder is eventually smaller than every positive
fraction of the target amplitude. -/
theorem eventually_abs_lt_mul_of_targetAmplitudeNegligible
    {amplitude remainder : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in atTop, 0 < amplitude x)
    (hnegligible : TargetAmplitudeNegligible amplitude remainder)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ x in atTop, |remainder x| < epsilon * amplitude x := by
  have hratio :
      ∀ᶠ x in atTop,
        |remainder x| / amplitude x < epsilon :=
    (tendsto_order.mp hnegligible).2 epsilon hepsilon
  filter_upwards [hamplitude, hratio] with x hax hratiox
  exact (div_lt_iff₀ hax).mp hratiox

/-- If the real-axis term, contour remainder, and complementary zero layer are
each negligible relative to the same target amplitude, their sum is
eventually smaller than half that amplitude. -/
theorem eventually_abs_realAxis_add_contour_add_complement_lt_half
    {amplitude realAxis contour complement : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in atTop, 0 < amplitude x)
    (hrealAxis : TargetAmplitudeNegligible amplitude realAxis)
    (hcontour : TargetAmplitudeNegligible amplitude contour)
    (hcomplement : TargetAmplitudeNegligible amplitude complement) :
    ∀ᶠ x in atTop,
      |realAxis x + contour x + complement x| < amplitude x / 2 := by
  have hrealAxisSmall :=
    eventually_abs_lt_mul_of_targetAmplitudeNegligible
      hamplitude hrealAxis (epsilon := (1 / 6 : ℝ)) (by norm_num)
  have hcontourSmall :=
    eventually_abs_lt_mul_of_targetAmplitudeNegligible
      hamplitude hcontour (epsilon := (1 / 6 : ℝ)) (by norm_num)
  have hcomplementSmall :=
    eventually_abs_lt_mul_of_targetAmplitudeNegligible
      hamplitude hcomplement (epsilon := (1 / 6 : ℝ)) (by norm_num)
  filter_upwards
      [hrealAxisSmall, hcontourSmall, hcomplementSmall] with
      x hrealAxisX hcontourX hcomplementX
  have htriangle :=
    abs_add_three (realAxis x) (contour x) (complement x)
  linarith

/-- Pointwise reverse-triangle assembly: a main term of target size survives a
remainder bounded by half that target size. -/
theorem half_targetAmplitude_le_abs_error
    {amplitude main remainder error : ℝ}
    (hmain : amplitude ≤ |main|)
    (hremainder : |remainder| ≤ amplitude / 2)
    (hdecomp : error = main + remainder) :
    amplitude / 2 ≤ |error| := by
  have hmainIdentity : main = error - remainder := by
    linarith
  have htriangle : |main| ≤ |error| + |remainder| := by
    calc
      |main| = |error - remainder| := by rw [hmainIdentity]
      _ ≤ |error| + |remainder| := abs_sub error remainder
  linarith

/-- A scale-dependent unsigned witness occurring beyond every starting point. -/
def HasFarTargetAmplitudeWitness
    (f amplitude : ℝ → ℝ) : Prop :=
  ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧ amplitude x ≤ |f x|

/-- Three normalized remainder estimates transfer every far target-amplitude
main-term witness to a half-amplitude witness for the actual error. -/
theorem hasFarTargetAmplitudeWitness_of_three_normalized_remainders
    {amplitude main realAxis contour complement error : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in atTop, 0 < amplitude x)
    (hrealAxis : TargetAmplitudeNegligible amplitude realAxis)
    (hcontour : TargetAmplitudeNegligible amplitude contour)
    (hcomplement : TargetAmplitudeNegligible amplitude complement)
    (hmain : HasFarTargetAmplitudeWitness main amplitude)
    (hdecomp :
      ∀ x : ℝ,
        error x = main x + (realAxis x + contour x + complement x)) :
    HasFarTargetAmplitudeWitness error (fun x => amplitude x / 2) := by
  have hsmall :=
    eventually_abs_realAxis_add_contour_add_complement_lt_half
      hamplitude hrealAxis hcontour hcomplement
  rw [eventually_atTop] at hsmall
  rcases hsmall with ⟨X₀, hX₀⟩
  intro X
  rcases hmain (max X X₀) with ⟨x, hx, hmainX⟩
  have hxX : X ≤ x := le_trans (le_max_left X X₀) hx
  have hxX₀ : X₀ ≤ x := le_trans (le_max_right X X₀) hx
  refine ⟨x, hxX, ?_⟩
  exact
    half_targetAmplitude_le_abs_error hmainX (hX₀ x hxX₀).le
      (hdecomp x)

end PrimeNumberTheorem
