import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightCubicCapDeficitAsymptotic
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightCanonicalStrictTargetExponent

/-!
# Theta-only target exponent asymptotics

The cubic improved-cap asymptotic is transported through the canonical inverse
target exponent. The inverse boundary has cubic excess over `theta`, whereas
the midpoint strict target introduces a linear excess.
-/

namespace PrimeNumberTheorem

open Filter Set
open scoped Topology

/-- The canonical inverse target exponent tends to one from below as the cap
`theta` tends to one from below. -/
theorem tendsto_jointTwoHeightOptimalTargetExponent_one :
    Tendsto jointTwoHeightOptimalTargetExponent
      (𝓝[<] (1 : ℝ)) (𝓝[<] (1 : ℝ)) := by
  have hthetaLower :
      ∀ᶠ theta : ℝ in 𝓝[<] (1 : ℝ), 1 / 2 < theta :=
    (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)).filter_mono
      inf_le_left
  have hthetaUpper :
      ∀ᶠ theta : ℝ in 𝓝[<] (1 : ℝ), theta < 1 :=
    self_mem_nhdsWithin
  have hbetaBounds :
      ∀ᶠ theta : ℝ in 𝓝[<] (1 : ℝ),
        0 ≤ 1 - jointTwoHeightOptimalTargetExponent theta ∧
          1 - jointTwoHeightOptimalTargetExponent theta ≤ 1 - theta ∧
          jointTwoHeightOptimalTargetExponent theta < 1 := by
    filter_upwards [hthetaLower, hthetaUpper] with theta hthetaHalf hthetaOne
    have hspec :=
      jointTwoHeightOptimalTargetExponent_spec hthetaHalf hthetaOne
    rcases hspec with ⟨hbetaLower, hbetaOne, hthreshold⟩
    have hthetaBeta : theta < jointTwoHeightOptimalTargetExponent theta := by
      have hcapLt :=
        (jointTwoHeightImprovedGlobalCapThreshold_spec
          hbetaLower hbetaOne).2
      linarith
    constructor
    · linarith
    · constructor <;> linarith
  have hthetaGap :
      Tendsto (fun theta : ℝ => 1 - theta)
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hfull :
        Tendsto (fun theta : ℝ => 1 - theta)
          (𝓝 (1 : ℝ)) (𝓝 0) := by
      have hcontinuous :
          ContinuousAt (fun theta : ℝ => 1 - theta) 1 := by
        fun_prop
      simpa using hcontinuous.tendsto
    exact hfull.mono_left inf_le_left
  have hbetaGap :
      Tendsto
        (fun theta : ℝ =>
          1 - jointTwoHeightOptimalTargetExponent theta)
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    apply squeeze_zero'
    · exact hbetaBounds.mono fun theta htheta => htheta.1
    · exact hbetaBounds.mono fun theta htheta => htheta.2.1
    · exact hthetaGap
  have hbetaNhds :
      Tendsto jointTwoHeightOptimalTargetExponent
        (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hone :
        Tendsto (fun _ : ℝ => (1 : ℝ))
          (𝓝[<] (1 : ℝ)) (𝓝 1) :=
      tendsto_const_nhds
    have h := hone.sub hbetaGap
    convert h using 1 <;> ring
  exact tendsto_nhdsWithin_iff.mpr
    ⟨hbetaNhds, hbetaBounds.mono fun theta htheta => htheta.2.2⟩

/-- The inverse target gap and the original cap gap are asymptotically equal. -/
theorem tendsto_jointTwoHeightOptimalTargetExponent_gapRatio_one :
    Tendsto
      (fun theta : ℝ =>
        (1 - jointTwoHeightOptimalTargetExponent theta) / (1 - theta))
      (𝓝[<] (1 : ℝ)) (𝓝 1) := by
  let beta := jointTwoHeightOptimalTargetExponent
  have hthetaLower :
      ∀ᶠ theta : ℝ in 𝓝[<] (1 : ℝ), 1 / 2 < theta :=
    (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)).filter_mono
      inf_le_left
  have hthetaUpper :
      ∀ᶠ theta : ℝ in 𝓝[<] (1 : ℝ), theta < 1 :=
    self_mem_nhdsWithin
  have hbetaTendsto :
      Tendsto beta (𝓝[<] (1 : ℝ)) (𝓝[<] (1 : ℝ)) := by
    simpa [beta] using tendsto_jointTwoHeightOptimalTargetExponent_one
  have hbetaGap :
      Tendsto (fun theta : ℝ => 1 - beta theta)
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hbetaNhds :
        Tendsto beta (𝓝[<] (1 : ℝ)) (𝓝 1) :=
      tendsto_nhds_of_tendsto_nhdsWithin hbetaTendsto
    convert tendsto_const_nhds.sub hbetaNhds using 1 <;> norm_num
  have hcubicComposed :=
    tendsto_jointTwoHeightImprovedGlobalCapThreshold_cubicDeficit.comp
      hbetaTendsto
  have hcubic :
      Tendsto
        (fun theta : ℝ =>
          (beta theta - theta) / (1 - beta theta) ^ 3)
        (𝓝[<] (1 : ℝ)) (𝓝 36) := by
    apply hcubicComposed.congr'
    filter_upwards [hthetaLower, hthetaUpper] with theta hthetaHalf hthetaOne
    have hspec :=
      jointTwoHeightOptimalTargetExponent_spec hthetaHalf hthetaOne
    simpa [beta, hspec.2.2]
  have hrelativeExcess :
      Tendsto
        (fun theta : ℝ => (beta theta - theta) / (1 - beta theta))
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hproduct := hcubic.mul (hbetaGap.pow 2)
    have hbetaUpper :
        ∀ᶠ theta : ℝ in 𝓝[<] (1 : ℝ), beta theta < 1 := by
      filter_upwards [hthetaLower, hthetaUpper] with theta hthetaHalf hthetaOne
      simpa [beta] using
        (jointTwoHeightOptimalTargetExponent_spec
          hthetaHalf hthetaOne).2.1
    have hproductZero :
        Tendsto
          (fun theta : ℝ =>
            ((beta theta - theta) / (1 - beta theta) ^ 3) *
              (1 - beta theta) ^ 2)
          (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      simpa using hproduct
    apply hproductZero.congr'
    filter_upwards [hbetaUpper] with theta hbetaOne
    have hne : 1 - beta theta ≠ 0 := by linarith
    field_simp [hne]
  have honePlus :
      Tendsto (fun theta : ℝ => 1 + (beta theta - theta) / (1 - beta theta))
        (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    convert tendsto_const_nhds.add hrelativeExcess using 1 <;> norm_num
  have hinverse :
      Tendsto
        (fun theta : ℝ =>
          1 / (1 + (beta theta - theta) / (1 - beta theta)))
        (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    convert tendsto_const_nhds.div honePlus (by norm_num : (1 : ℝ) ≠ 0)
      using 1 <;> norm_num
  apply hinverse.congr'
  filter_upwards [hthetaLower, hthetaUpper] with theta hthetaHalf hthetaOne
  have hspec :=
    jointTwoHeightOptimalTargetExponent_spec hthetaHalf hthetaOne
  have hbetaOne : beta theta < 1 := by simpa [beta] using hspec.2.1
  have hthetaNe : 1 - theta ≠ 0 := by linarith
  have hbetaNe : 1 - beta theta ≠ 0 := by linarith
  field_simp [hthetaNe, hbetaNe]
  ring

/-- The inverse optimal target exceeds `theta` by
`36 * (1 - theta)^3` to first order. -/
theorem tendsto_jointTwoHeightOptimalTargetExponent_cubicExcess :
    Tendsto
      (fun theta : ℝ =>
        (jointTwoHeightOptimalTargetExponent theta - theta) /
          (1 - theta) ^ 3)
      (𝓝[<] (1 : ℝ)) (𝓝 36) := by
  let beta := jointTwoHeightOptimalTargetExponent
  have hthetaLower :
      ∀ᶠ theta : ℝ in 𝓝[<] (1 : ℝ), 1 / 2 < theta :=
    (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)).filter_mono
      inf_le_left
  have hthetaUpper :
      ∀ᶠ theta : ℝ in 𝓝[<] (1 : ℝ), theta < 1 :=
    self_mem_nhdsWithin
  have hbetaTendsto :
      Tendsto beta (𝓝[<] (1 : ℝ)) (𝓝[<] (1 : ℝ)) := by
    simpa [beta] using tendsto_jointTwoHeightOptimalTargetExponent_one
  have hcubicComposed :=
    tendsto_jointTwoHeightImprovedGlobalCapThreshold_cubicDeficit.comp
      hbetaTendsto
  have hcubic :
      Tendsto
        (fun theta : ℝ =>
          (beta theta - theta) / (1 - beta theta) ^ 3)
        (𝓝[<] (1 : ℝ)) (𝓝 36) := by
    apply hcubicComposed.congr'
    filter_upwards [hthetaLower, hthetaUpper] with theta hthetaHalf hthetaOne
    have hspec :=
      jointTwoHeightOptimalTargetExponent_spec hthetaHalf hthetaOne
    simpa [beta, hspec.2.2]
  have hratio :
      Tendsto (fun theta : ℝ => (1 - beta theta) / (1 - theta))
        (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    simpa [beta] using
      tendsto_jointTwoHeightOptimalTargetExponent_gapRatio_one
  have hproduct := hcubic.mul (hratio.pow 3)
  have hlimit : (36 : ℝ) * 1 ^ 3 = 36 := by norm_num
  rw [hlimit] at hproduct
  apply hproduct.congr'
  filter_upwards [hthetaLower, hthetaUpper] with theta hthetaHalf hthetaOne
  have hspec :=
    jointTwoHeightOptimalTargetExponent_spec hthetaHalf hthetaOne
  have hbetaOne : beta theta < 1 := by simpa [beta] using hspec.2.1
  have hthetaNe : 1 - theta ≠ 0 := by linarith
  have hbetaNe : 1 - beta theta ≠ 0 := by linarith
  field_simp [hthetaNe, hbetaNe]
  ring

/-- The midpoint strict target loses the cubic boundary precision: its excess
over `theta` is asymptotic to `(1 / 2) * (1 - theta)`. -/
theorem
    tendsto_jointTwoHeightCanonicalStrictTargetExponent_linearExcess :
    Tendsto
      (fun theta : ℝ =>
        (jointTwoHeightCanonicalStrictTargetExponent theta - theta) /
          (1 - theta))
      (𝓝[<] (1 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  let beta := jointTwoHeightOptimalTargetExponent
  have hthetaUpper :
      ∀ᶠ theta : ℝ in 𝓝[<] (1 : ℝ), theta < 1 :=
    self_mem_nhdsWithin
  have hthetaGap :
      Tendsto (fun theta : ℝ => 1 - theta)
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hfull :
        Tendsto (fun theta : ℝ => 1 - theta)
          (𝓝 (1 : ℝ)) (𝓝 0) := by
      have hcontinuous :
          ContinuousAt (fun theta : ℝ => 1 - theta) 1 := by
        fun_prop
      simpa using hcontinuous.tendsto
    exact hfull.mono_left inf_le_left
  have hcubic :
      Tendsto
        (fun theta : ℝ => (beta theta - theta) / (1 - theta) ^ 3)
        (𝓝[<] (1 : ℝ)) (𝓝 36) := by
    simpa [beta] using
      tendsto_jointTwoHeightOptimalTargetExponent_cubicExcess
  have hlinearRemainder :
      Tendsto
        (fun theta : ℝ => (beta theta - theta) / (1 - theta))
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hproduct := hcubic.mul (hthetaGap.pow 2)
    have hproductZero :
        Tendsto
          (fun theta : ℝ =>
            ((beta theta - theta) / (1 - theta) ^ 3) *
              (1 - theta) ^ 2)
          (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      simpa using hproduct
    apply hproductZero.congr'
    filter_upwards [hthetaUpper] with theta hthetaOne
    have hne : 1 - theta ≠ 0 := by linarith
    field_simp [hne]
  have hmidpoint :
      Tendsto
        (fun theta : ℝ =>
          (1 / 2 : ℝ) + (1 / 2 : ℝ) *
            ((beta theta - theta) / (1 - theta)))
        (𝓝[<] (1 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
    convert
      tendsto_const_nhds.add (tendsto_const_nhds.mul hlinearRemainder)
      using 1 <;> norm_num
  apply hmidpoint.congr'
  filter_upwards [hthetaUpper] with theta hthetaOne
  have hne : 1 - theta ≠ 0 := by linarith
  dsimp [jointTwoHeightCanonicalStrictTargetExponent, beta]
  field_simp [hne]
  ring

end PrimeNumberTheorem
