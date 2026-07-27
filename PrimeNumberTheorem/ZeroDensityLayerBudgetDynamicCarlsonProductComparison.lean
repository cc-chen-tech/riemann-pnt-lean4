import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonDensityTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicLogHeightActualLayerTransfer

/-!
# Dynamic Carlson product comparison

This module performs the arithmetic comparison left explicit by the dynamic
actual-layer transfer.  Carlson's raw count at `H(x)`, the actual endpoint
kernel, and the target-zero power are converted to the same logarithmic
majorant.  The only geometric height condition needed for the logarithmic
factor is the eventual window `1 < H(x) ≤ x`.
-/

namespace PrimeNumberTheorem

open Filter

/-- A raw Carlson count bound at a genuinely dynamic height converts to the
explicit target-normalized logarithmic majorant. -/
theorem
    eventually_dynamicCarlsonProduct_le_dynamicLogHeightMajorant
    {height : ℝ → ℝ} {beta sigma tau kappa C : ℝ}
    (hC : 0 ≤ C)
    (hkappa : 0 < kappa)
    (hheightWindow : ∀ᶠ x in atTop, 1 < height x ∧ height x ≤ x)
    (hcount :
      ∀ᶠ x in atTop,
        dynamicCarlsonLayerCount sigma height x ≤
          C * height x ^
              actualSelectedHeightStripCarlsonSlope sigma *
            Real.log (height x) ^ (4 : ℕ)) :
    ∀ᶠ x in atTop,
      dynamicCarlsonLayerCount sigma height x *
              stripEndpointRelativeKernelBudget kappa tau x /
            targetZeroPowerAmplitude beta x
          ≤
        (C * kappa⁻¹) *
          dynamicLogHeightMajorant height
            (tau - beta)
            (actualSelectedHeightStripCarlsonSlope sigma) x := by
  filter_upwards [hheightWindow, hcount] with x hxHeight hxCount
  have hheightPos : 0 < height x := lt_trans zero_lt_one hxHeight.1
  have hxPos : 0 < x :=
    lt_of_lt_of_le hheightPos hxHeight.2
  have hlogHeightNonneg : 0 ≤ Real.log (height x) :=
    Real.log_nonneg hxHeight.1.le
  have hlogLe : Real.log (height x) ≤ Real.log x :=
    Real.strictMonoOn_log.monotoneOn hheightPos hxPos hxHeight.2
  have hlogPow :
      Real.log (height x) ^ (4 : ℕ) ≤
        Real.log x ^ (4 : ℕ) := by
    gcongr
  have hcountLog :
      dynamicCarlsonLayerCount sigma height x ≤
        C * height x ^
            actualSelectedHeightStripCarlsonSlope sigma *
          Real.log x ^ (4 : ℕ) := by
    calc
      dynamicCarlsonLayerCount sigma height x ≤
          C * height x ^
              actualSelectedHeightStripCarlsonSlope sigma *
            Real.log (height x) ^ (4 : ℕ) :=
        hxCount
      _ ≤
          C * height x ^
              actualSelectedHeightStripCarlsonSlope sigma *
            Real.log x ^ (4 : ℕ) := by
        exact
          mul_le_mul_of_nonneg_left hlogPow
            (mul_nonneg hC (Real.rpow_nonneg hheightPos.le _))
  have hkernelNonneg :
      0 ≤ stripEndpointRelativeKernelBudget kappa tau x :=
    stripEndpointRelativeKernelBudget_nonneg hxPos.le hkappa.le
  have hamplitudePos :
      0 < targetZeroPowerAmplitude beta x := by
    simp only [targetZeroPowerAmplitude]
    exact Real.rpow_pos_of_pos hxPos _
  have hbasePower :
      x ^ (tau - 1) / x ^ (beta - 1) =
        x ^ (tau - beta) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hxPos.le]
    rw [← Real.rpow_add hxPos]
    congr 1
    ring
  have hexponentialPower :
      height x ^ actualSelectedHeightStripCarlsonSlope sigma *
          x ^ (tau - beta) =
        Real.exp
          ((tau - beta) * Real.log x +
            actualSelectedHeightStripCarlsonSlope sigma *
              Real.log (height x)) := by
    rw [Real.rpow_def_of_pos hheightPos, Real.rpow_def_of_pos hxPos,
      ← Real.exp_add]
    congr 1
    ring
  calc
    dynamicCarlsonLayerCount sigma height x *
              stripEndpointRelativeKernelBudget kappa tau x /
            targetZeroPowerAmplitude beta x
        ≤
      (C * height x ^
              actualSelectedHeightStripCarlsonSlope sigma *
            Real.log x ^ (4 : ℕ)) *
              stripEndpointRelativeKernelBudget kappa tau x /
            targetZeroPowerAmplitude beta x :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcountLog hkernelNonneg)
        hamplitudePos.le
    _ =
        (C * kappa⁻¹) *
          dynamicLogHeightMajorant height
            (tau - beta)
            (actualSelectedHeightStripCarlsonSlope sigma) x := by
      simp only [stripEndpointRelativeKernelBudget,
        targetZeroPowerAmplitude, dynamicLogHeightMajorant]
      rw [show
        (C * height x ^
                actualSelectedHeightStripCarlsonSlope sigma *
              Real.log x ^ (4 : ℕ)) *
                (kappa⁻¹ * x ^ (tau - 1)) /
              x ^ (beta - 1) =
            (C * kappa⁻¹) *
              ((height x ^
                    actualSelectedHeightStripCarlsonSlope sigma *
                  (x ^ (tau - 1) / x ^ (beta - 1))) *
                Real.log x ^ (4 : ℕ)) by ring]
      rw [hbasePower, hexponentialPower]

/-- Carlson's proved density estimate automatically supplies all coefficients
needed by the dynamic actual-zeta finite-layer transfer.

This closes the count-kernel product hypothesis: under logarithmic height
growth, the elementary window `1 < H(x) ≤ x`, and strict strip margins, the
actual multiplicity-weighted finite zeta-layer norm sum is negligible on the
target-zero power scale. -/
theorem
    actualZetaFiniteStrips_dynamicCarlsonLogHeight_layerNormSum_negligible
    {n : ℕ} {height : ℝ → ℝ} {beta alpha : ℝ}
    (input : (x : ℝ) → PositiveZeroBucketInput (height x) (n + 1))
    (sigma tau kappa : Fin (n + 1) → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hheight : Tendsto height atTop atTop)
    (hheightWindow : ∀ᶠ x in atTop, 1 < height x ∧ height x ≤ x)
    (hlogGrowth :
      Tendsto
        (fun x : ℝ => Real.log (height x) / Real.log x)
        atTop (nhds alpha))
    (hmargin :
      ∀ i,
        tau i - beta +
            actualSelectedHeightStripCarlsonSlope (sigma i) * alpha <
          0) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (fun x =>
        ∑ i,
          dynamicPositivePNTLayerNorm height input i x) := by
  obtain ⟨C, hC, hcount⟩ :=
    exists_finiteCarlsonCoefficients_along_dynamicHeight
      (Finset.univ : Finset (Fin (n + 1)))
      sigma hsigma hsigmaOne height hheight
  apply
    actualZetaFiniteStrips_dynamicLogHeight_layerNormSum_negligible
      input sigma tau kappa (fun i => C i * (kappa i)⁻¹)
      hfixedSigma hkappa hnorm hre hlogGrowth hmargin
  intro i
  apply
    eventually_dynamicCarlsonProduct_le_dynamicLogHeightMajorant
      (hC i (Finset.mem_univ i)) (hkappa i) hheightWindow
  simpa [dynamicCarlsonLayerCount,
    actualSelectedHeightStripCarlsonSlope] using
      hcount i (Finset.mem_univ i)

end PrimeNumberTheorem
