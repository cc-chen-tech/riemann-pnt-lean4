import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTDynamicUpper
import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonDensityTransfer

/-!
# Good heights below an exact Pintz--Carlson ceiling

The contour theorem chooses a good height in a unit interval, whereas the
proved Carlson transfer is evaluated at the exact adaptive height
`pintzCarlsonHeight k x`.  Choosing the base of the unit interval to be one
less than that adaptive height makes the good height no larger than the
Carlson height.  Monotonicity of the multiplicity-weighted zero count then
transfers every density term to the exact adaptive height.

This module does not claim that Carlson strips cover zeros with real part at
most `1 / 2`; such a low-real-part layer still requires a separate global
zero-count estimate.
-/

open Filter Topology
open scoped BigOperators

namespace PrimeNumberTheorem

/-- Base of the unit good-height interval whose upper endpoint is the exact
Pintz--Carlson height. -/
noncomputable def pintzCarlsonGoodHeightBase (rate x : ℝ) : ℝ :=
  pintzCarlsonHeight rate x - 1

theorem goodHeightInterval_le_pintzCarlsonHeight
    {rate x T : ℝ}
    (hT : T ∈ Set.Icc (pintzCarlsonGoodHeightBase rate x)
      (pintzCarlsonGoodHeightBase rate x + 1)) :
    T ≤ pintzCarlsonHeight rate x := by
  simpa only [pintzCarlsonGoodHeightBase, sub_add_cancel] using hT.2

/-- The concrete aggregated Carlson density layer is monotone in its height
argument. -/
theorem pintzCarlsonClassicalAggregatedDensityLayerTerm_mono_height
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι) (sigma : ι → ℝ) (x : ℝ)
    {T U : ℝ} (hTU : T ≤ U) :
    pintzCarlsonClassicalAggregatedDensityLayerTerm
        layers sigma () x T ≤
      pintzCarlsonClassicalAggregatedDensityLayerTerm
        layers sigma () x U := by
  simp only [pintzCarlsonClassicalAggregatedDensityLayerTerm,
    pintzCarlsonAggregatedDensityLayerTerm]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast ZeroDensity.zeroDensityCount_mono_height hTU
  · exact Real.exp_nonneg _

/-- Absolute PNT budget with every density count evaluated at the exact
Pintz--Carlson ceiling, while contour and real-ordinate residual terms retain
the actual good height `T`. -/
noncomputable def naturalPointPintzPNTCeilingDensityUpperBudget
    (C A T rate : ℝ) (m N : ℕ) {n : ℕ}
    (input : PositiveZeroBucketInput T n) : ℝ :=
  (m : ℝ) *
        (2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
              Finset.univ input.sigma () (m : ℝ)
              (pintzCarlsonHeight rate (m : ℝ)) +
          ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
              pntRelativeZeroContribution (m : ℝ) rho‖) +
      ‖deriv riemannZeta 0 / riemannZeta 0‖ +
    ‖cofinalTrivialZeroContribution m N‖ +
    cofinalPNTFormulaRemainderBound C A T m N

/-- Relative version of `naturalPointPintzPNTCeilingDensityUpperBudget`. -/
noncomputable def naturalPointPintzPNTCeilingDensityRelativeUpperBudget
    (C A T rate : ℝ) (m N : ℕ) {n : ℕ}
    (input : PositiveZeroBucketInput T n) : ℝ :=
  2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
        Finset.univ input.sigma () (m : ℝ)
        (pintzCarlsonHeight rate (m : ℝ)) +
    ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
        pntRelativeZeroContribution (m : ℝ) rho‖ +
    (‖deriv riemannZeta 0 / riemannZeta 0‖ +
        ‖cofinalTrivialZeroContribution m N‖ +
        cofinalPNTFormulaRemainderBound C A T m N) / (m : ℝ)

theorem naturalPointPintzPNTUpperBudget_le_ceilingDensity
    {C A T rate : ℝ} {m N n : ℕ}
    (input : PositiveZeroBucketInput T n)
    (hT : T ≤ pintzCarlsonHeight rate (m : ℝ)) :
    naturalPointPintzPNTUpperBudget C A T m N input ≤
      naturalPointPintzPNTCeilingDensityUpperBudget
        C A T rate m N input := by
  have hdensity :=
    pintzCarlsonClassicalAggregatedDensityLayerTerm_mono_height
      (Finset.univ : Finset (Fin n)) input.sigma (m : ℝ) hT
  simp only [naturalPointPintzPNTUpperBudget,
    naturalPointPintzPNTCeilingDensityUpperBudget]
  gcongr

theorem naturalPointPintzPNTRelativeUpperBudget_le_ceilingDensity
    {C A T rate : ℝ} {m N n : ℕ}
    (input : PositiveZeroBucketInput T n)
    (hT : T ≤ pintzCarlsonHeight rate (m : ℝ)) :
    naturalPointPintzPNTRelativeUpperBudget C A T m N input ≤
      naturalPointPintzPNTCeilingDensityRelativeUpperBudget
        C A T rate m N input := by
  have hdensity :=
    pintzCarlsonClassicalAggregatedDensityLayerTerm_mono_height
      (Finset.univ : Finset (Fin n)) input.sigma (m : ℝ) hT
  simp only [naturalPointPintzPNTRelativeUpperBudget,
    naturalPointPintzPNTCeilingDensityRelativeUpperBudget]
  gcongr

/-- Dynamic natural-point PNT transfer whose density part is evaluated at the
exact adaptive Pintz--Carlson height.  The selected contour height remains a
genuine good height in the unit interval immediately below it. -/
theorem exists_naturalPoint_pintzCarlson_goodHeight_ceiling_PNT_upper
    (selectRate : ℝ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m N : ℕ), 3 ≤ m →
        8 ≤ pintzCarlsonGoodHeightBase
          (selectRate (m : ℝ)) (m : ℝ) →
        ∃ T ∈ Set.Icc
            (pintzCarlsonGoodHeightBase
              (selectRate (m : ℝ)) (m : ℝ))
            (pintzCarlsonGoodHeightBase
              (selectRate (m : ℝ)) (m : ℝ) + 1),
          ExplicitFormulaAux.goodHeight T ∧
            ∃ certificate : TruncatedPNTErrorCertificate (m : ℝ) T,
              certificate.trivialContribution =
                  cofinalTrivialZeroContribution m N ∧
                certificate.remainderBound =
                  cofinalPNTFormulaRemainderBound C
                    (pintzCarlsonGoodHeightBase
                      (selectRate (m : ℝ)) (m : ℝ)) T m N ∧
                ∀ {n : ℕ} (input : PositiveZeroBucketInput T n),
                  |chebyshevPsi0 (m : ℝ) - (m : ℝ)| ≤
                      naturalPointPintzPNTCeilingDensityUpperBudget C
                        (pintzCarlsonGoodHeightBase
                          (selectRate (m : ℝ)) (m : ℝ))
                        T (selectRate (m : ℝ)) m N input ∧
                    |relativeChebyshevPsi0Error (m : ℝ)| ≤
                      naturalPointPintzPNTCeilingDensityRelativeUpperBudget C
                        (pintzCarlsonGoodHeightBase
                          (selectRate (m : ℝ)) (m : ℝ))
                        T (selectRate (m : ℝ)) m N input := by
  let heightBase : ℕ → ℝ := fun m =>
    pintzCarlsonGoodHeightBase (selectRate (m : ℝ)) (m : ℝ)
  rcases exists_naturalPoint_dynamic_goodHeight_pintz_PNT_upper heightBase with
    ⟨C, hC, htransfer⟩
  refine ⟨C, hC, ?_⟩
  intro m N hm hbase
  rcases htransfer m N hm hbase with
    ⟨T, hT, hgood, certificate, htrivial, hremainder, hbounds⟩
  refine ⟨T, hT, hgood, certificate, htrivial, hremainder, ?_⟩
  intro n input
  rcases hbounds input with ⟨habsolute, hrelative⟩
  have hceiling :
      T ≤ pintzCarlsonHeight (selectRate (m : ℝ)) (m : ℝ) :=
    goodHeightInterval_le_pintzCarlsonHeight hT
  exact
    ⟨habsolute.trans
        (naturalPointPintzPNTUpperBudget_le_ceilingDensity input hceiling),
      hrelative.trans
        (naturalPointPintzPNTRelativeUpperBudget_le_ceilingDensity
          input hceiling)⟩

/-- Carlson's proved fixed-strip estimate makes the exact-height density term
appearing in the ceiling PNT budget tend to zero for every admissible finite
rate selector. -/
theorem exists_pintzConstant_exactHeight_classicalDensityTerm_tendsto
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι)
    (sigma : ι → ℝ)
    (hσ : ∀ i, 1 / 2 < sigma i)
    (hσ1 : ∀ i, sigma i < 1)
    (rates : Finset ℝ) :
    ∃ c > 0, ∀ (selectRate : ℝ → ℝ),
      (∀ x, selectRate x ∈ rates) →
      (∀ k ∈ rates, 0 < k) →
      (∀ k ∈ rates, k < 2 * Real.sqrt c) →
      Tendsto
        (fun x =>
          pintzCarlsonClassicalAggregatedDensityLayerTerm
            layers sigma () x
              (pintzCarlsonHeight (selectRate x) x))
        atTop (𝓝 0) := by
  rcases exists_pintzConstant_adaptiveClassicalCarlsonDensity_tendsto
      layers sigma hσ hσ1 rates with ⟨c, hc, htransfer⟩
  refine ⟨c, hc, ?_⟩
  intro selectRate hselect hratesPos hratesGap
  change Tendsto
    (fun x => pintzCarlsonActualDensityBudget layers
      (fun i T => (ZeroDensity.zeroDensityCount (sigma i) T : ℝ))
      selectRate x) atTop (𝓝 0)
  exact htransfer selectRate hselect hratesPos hratesGap

end PrimeNumberTheorem
