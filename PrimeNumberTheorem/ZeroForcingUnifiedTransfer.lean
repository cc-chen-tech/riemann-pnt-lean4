import PrimeNumberTheorem.PNTFiniteZeroSum
import PrimeNumberTheorem.PintzEnvelope
import PrimeNumberTheorem.ZeroDensityLayerBudgetAntiCancellation
import PrimeNumberTheorem.ZeroDensityLayerBudgetAsymptoticTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetBidirectional
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonKernelAdapter
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonUnified
import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicOptimization
import PrimeNumberTheorem.ZeroDensityLayerBudgetEventuallyZeroFreeUnified
import PrimeNumberTheorem.ZeroDensityLayerBudgetFiniteDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetKernelDensity
import PrimeNumberTheorem.ZeroDensityLayerBudgetOmegaTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetOptimization
import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzGrid
import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonGap
import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonUnified
import PrimeNumberTheorem.ZeroDensityLayerBudgetUnifiedMachine
import PrimeNumberTheorem.ZeroDensityLayerBudgetZeroFreeUnified

open Complex Filter Set
open scoped BigOperators

namespace PrimeNumberTheorem

open ZeroForcedOscillation

/-- Compatibility predicate for explicit-formula heights bounded below by `4`. -/
def dynamicExplicitFormulaHeight (T : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 4 ≤ T x

/--
The classical zero-free-region finite-zero-sum bound evaluated at a dynamic
height.  This compatibility theorem keeps the earlier public interface while
the layer-budget modules provide the finer density-sensitive cost.
-/
theorem dynamic_zero_free_upper_bound
    (T : ℝ → ℝ) (hT : dynamicExplicitFormulaHeight T) :
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧
      ∀ x : ℝ, 1 < x →
        ‖finiteNontrivialZeroSumWithMultiplicity x (T x)‖ ≤
          C * x ^ (1 - b / Real.log (T x + 6)) *
            (1 + Real.log (T x + 6)) ^ 2 := by
  rcases
      ExplicitFormulaAux.exists_norm_finiteNontrivialZeroSumWithMultiplicity_le_zeroFree_mul_log_sq
    with ⟨b, C, hb, hC, hbound⟩
  refine ⟨b, C, hb, hC, ?_⟩
  intro x hx
  exact hbound x (T x) hx (hT x)

/--
Pintz's envelope is eventually an admissible dynamic height for every fixed
height threshold.
-/
theorem eventually_admissible_pintzZeroEnvelope (heightThreshold : ℝ) :
    ∀ᶠ x in atTop,
      AdmissibleHeight heightThreshold x (Pintz.pintzZeroEnvelope x) := by
  filter_upwards [eventually_ge_atTop (2 : ℝ),
      Pintz.tendsto_pintzZeroEnvelope_atTop.eventually
        (eventually_ge_atTop heightThreshold)] with x hx hheight
  exact ⟨hx, hheight⟩

/-- Auditable upper conclusion produced by a dynamic explicit-formula cost. -/
structure DynamicUpperConclusion
    (pntError : ℝ → ℂ) (upperCost : ℝ → ℝ) (x₀ : ℝ) : Type where
  bound : ∀ x, x₀ ≤ x → ‖pntError x‖ ≤ upperCost x

/-- Unsigned oscillation conclusion with witnesses beyond every starting scale. -/
structure OscillationLowerConclusion
    (pntError : ℝ → ℂ) (amplitude : ℝ → ℝ) : Type where
  witnesses : ∀ X, ∃ x, X ≤ x ∧ amplitude x ≤ ‖pntError x‖

/-- Package a fixed-height estimate specialized along a dynamic schedule. -/
def dynamic_upper_conclusion
    {pntError : ℝ → ℂ}
    {layerCost truncationCost compactCost : ℝ → ℝ → ℝ}
    {x₀ heightThreshold : ℝ}
    (schedule : DynamicHeightSchedule x₀ heightThreshold)
    (hformula :
      ∀ x T, AdmissibleHeight heightThreshold x T →
        ‖pntError x‖ ≤
          explicitFormulaCost layerCost truncationCost compactCost x T) :
    DynamicUpperConclusion pntError
      (fun x =>
        explicitFormulaCost layerCost truncationCost compactCost x
          (schedule.height x))
      x₀ :=
  ⟨dynamic_explicit_formula_upper schedule hformula⟩

/-- The equal-real-part cluster itself, in logarithmic scale. -/
noncomputable def equalRealPartClusterPackage
    (S : Finset ℂ) (multiplicity : ℂ → ℕ) (y : ℝ) : ℂ :=
  ∑ ρ ∈ S,
    (multiplicity ρ : ℂ) * ((Real.exp y : ℝ) : ℂ) ^ ρ / ρ

/-- Diagonal energy minus the explicit off-diagonal budget for interval length `L`. -/
noncomputable def equalRealPartClusterAmplitude
    (S : Finset ℂ) (multiplicity : ℂ → ℕ)
    (β L y : ℝ) : ℝ :=
  Real.exp (β * y) ^ 2 *
    ((∑ ρ ∈ S, ‖(multiplicity ρ : ℂ) * ρ⁻¹‖ ^ 2) -
      offDiagonalBound S
          (fun ρ => (multiplicity ρ : ℂ) * ρ⁻¹) Complex.im / L)

/--
Transfer finite-cluster anti-cancellation to the actual error after subtracting
abstract complementary and remainder budgets.

The complementary-bound owner supplies `hcomplement`; this module does not
import or duplicate that theorem.
-/
noncomputable def zero_cluster_oscillation_lower
    (S : Finset ℂ) (multiplicity : ℂ → ℕ) (β L : ℝ)
    (hL : 0 < L) (hre : ∀ ρ ∈ S, ρ.re = β)
    (pntError complement remainder : ℝ → ℂ)
    (hdecomp :
      ∀ y, pntError y =
        equalRealPartClusterPackage S multiplicity y +
          complement y + remainder y)
    (complementBudget remainderBudget : ℝ → ℝ)
    (hcomplement : ∀ y, ‖complement y‖ ≤ complementBudget y)
    (hremainder : ∀ y, ‖remainder y‖ ≤ remainderBudget y) :
    OscillationLowerConclusion pntError
      (fun y =>
        Real.sqrt
            (equalRealPartClusterAmplitude S multiplicity β L y) -
          complementBudget y - remainderBudget y) := by
  constructor
  intro X
  rcases exists_far_norm_equalRealPart_zeroPackage_ge
      S multiplicity β L hL hre X with
    ⟨y, hy, hmain⟩
  refine ⟨y, hy.1.le, ?_⟩
  have hmain' :
      Real.sqrt
          (equalRealPartClusterAmplitude S multiplicity β L y) ≤
        ‖equalRealPartClusterPackage S multiplicity y‖ := by
    simpa [equalRealPartClusterAmplitude,
      equalRealPartClusterPackage] using hmain
  have htransfer :=
    norm_error_ge_main_sub_complement_remainder
      (pntError y)
      (equalRealPartClusterPackage S multiplicity y)
      (complement y) (remainder y) (hdecomp y)
  linarith [hcomplement y, hremainder y]

/-- Pair independently proved upper and lower transfer conclusions. -/
def unified_dynamic_transfer
    {pntError : ℝ → ℂ}
    {upperCost amplitude : ℝ → ℝ}
    {x₀ : ℝ}
    (hupper : ∀ x, x₀ ≤ x → ‖pntError x‖ ≤ upperCost x)
    (hlower : ∀ X, ∃ x, X ≤ x ∧ amplitude x ≤ ‖pntError x‖) :
    DynamicUpperConclusion pntError upperCost x₀ ×
      OscillationLowerConclusion pntError amplitude :=
  ⟨⟨hupper⟩, ⟨hlower⟩⟩

/--
Unified dynamic transfer theorem.

The same error term receives a dynamic explicit-formula upper bound and an
unsigned finite-cluster oscillation lower bound.  Upper and lower hypotheses
remain logically separate and are joined only in the returned certificate.
-/
noncomputable def unified_dynamic_zero_transfer
    {pntError : ℝ → ℂ}
    {layerCost truncationCost compactCost : ℝ → ℝ → ℝ}
    {x₀ heightThreshold : ℝ}
    (schedule : DynamicHeightSchedule x₀ heightThreshold)
    (hformula :
      ∀ x T, AdmissibleHeight heightThreshold x T →
        ‖pntError x‖ ≤
          explicitFormulaCost layerCost truncationCost compactCost x T)
    (S : Finset ℂ) (multiplicity : ℂ → ℕ) (β L : ℝ)
    (hL : 0 < L) (hre : ∀ ρ ∈ S, ρ.re = β)
    (complement remainder : ℝ → ℂ)
    (hdecomp :
      ∀ y, pntError y =
        equalRealPartClusterPackage S multiplicity y +
          complement y + remainder y)
    (complementBudget remainderBudget : ℝ → ℝ)
    (hcomplement : ∀ y, ‖complement y‖ ≤ complementBudget y)
    (hremainder : ∀ y, ‖remainder y‖ ≤ remainderBudget y) :
    DynamicUpperConclusion pntError
        (fun x =>
          explicitFormulaCost layerCost truncationCost compactCost x
            (schedule.height x))
        x₀ ×
      OscillationLowerConclusion pntError
        (fun y =>
          Real.sqrt
              (equalRealPartClusterAmplitude S multiplicity β L y) -
            complementBudget y - remainderBudget y) :=
  ⟨dynamic_upper_conclusion schedule hformula,
    zero_cluster_oscillation_lower S multiplicity β L hL hre
      pntError complement remainder hdecomp complementBudget remainderBudget
      hcomplement hremainder⟩

end PrimeNumberTheorem
