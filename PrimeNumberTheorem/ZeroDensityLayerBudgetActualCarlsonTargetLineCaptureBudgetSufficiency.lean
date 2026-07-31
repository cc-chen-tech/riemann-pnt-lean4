import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryMassFiniteComparison
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonConjugateCapturedMass
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonPositiveCoefficientMassUpper
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryAutomaticCoefficientCap
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedTargetLineSelector
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonConjugateFiniteSeedBarrier

namespace PrimeNumberTheorem

open scoped BigOperators
open Complex

noncomputable section

 theorem positiveCoefficientMass_eq_capturedBoundaryMass_of_targetLine
    {sigma beta : ℝ} {E : Finset ℂ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hsigmaBeta : sigma < beta)
    (hzero : ∀ rho ∈ E, RiemannHypothesis.IsNontrivialZero rho)
    (htarget : ∀ rho ∈ E, rho.re = beta) :
    finiteVisibleClusterCoefficientMass (positiveFiniteVisibleClusterPart E) =
      actualCarlsonCapturedBoundaryMass (sigma := sigma) beta E := by
  classical
  let Epos := positiveFiniteVisibleClusterPart E
  let lift : {rho : ℂ // rho ∈ Epos} ↪ ActualCarlsonHighPositiveZero sigma :=
    ⟨fun rho =>
      ⟨rho.1,
        hzero rho.1 (positiveFiniteVisibleClusterPart_subset E rho.2),
        (Finset.mem_filter.mp rho.2).2,
        by rw [htarget rho.1 (positiveFiniteVisibleClusterPart_subset E rho.2)]; exact hsigmaBeta⟩,
      by
        intro rho₁ rho₂ heq
        apply Subtype.ext
        exact congrArg (fun z : ActualCarlsonHighPositiveZero sigma => z.1) heq⟩
  let s : Finset (ActualCarlsonHighPositiveZero sigma) := Epos.attach.map lift
  have hvalues :
      s.map (actualCarlsonHighPositiveZeroValueEmbedding sigma) = Epos := by
    ext rho
    simp [s, lift, actualCarlsonHighPositiveZeroValueEmbedding]
  have hfinite :
      finiteVisibleClusterCoefficientMass Epos =
        ∑ rho ∈ s,
          actualCarlsonPositiveZeroWeight
            (actualCarlsonPositiveZeroIndexOf rho) := by
    rw [← hvalues]
    exact finiteVisibleClusterCoefficientMass_map_highPositive_eq s
  let e : ActualCarlsonHighPositiveZero sigma ↪
      ActualCarlsonPositiveZeroIndex sigma :=
    ⟨actualCarlsonPositiveZeroIndexOf,
      actualCarlsonPositiveZeroIndexOf_injective⟩
  have hsum :
      (∑ rho ∈ s,
          actualCarlsonPositiveZeroWeight
            (actualCarlsonPositiveZeroIndexOf rho)) =
        ∑ index ∈ s.map e,
          actualCarlsonCapturedBoundaryTerm beta E index := by
    calc
      _ = ∑ rho ∈ s,
          actualCarlsonCapturedBoundaryTerm beta E (e rho) := by
        apply Finset.sum_congr rfl
        intro rho hrho
        have hrhoEpos : rho.1 ∈ Epos := by
          rw [← hvalues]
          exact Finset.mem_map.mpr ⟨rho, hrho, rfl⟩
        have hrhoE : rho.1 ∈ E :=
          positiveFiniteVisibleClusterPart_subset E hrhoEpos
        have hre : rho.1.re = beta := htarget rho.1 hrhoE
        simp [e, actualCarlsonCapturedBoundaryTerm,
          actualCarlsonPositiveZeroRealPart,
          actualCarlsonPositiveZero_indexOf, hre, hrhoE]
      _ = _ := (Finset.sum_map s e
        (actualCarlsonCapturedBoundaryTerm beta E)).symm
  have hle :
      finiteVisibleClusterCoefficientMass Epos ≤
        actualCarlsonCapturedBoundaryMass (sigma := sigma) beta E := by
    rw [hfinite, hsum]
    exact
      (summable_actualCarlsonCapturedBoundaryTerm E hhalf hone).sum_le_tsum
        (s.map e)
        (fun index _ => actualCarlsonCapturedBoundaryTerm_nonneg E index)
  have hge :
      actualCarlsonCapturedBoundaryMass (sigma := sigma) beta E ≤
        finiteVisibleClusterCoefficientMass Epos := by
    rw [← actualCarlsonCapturedBoundaryMass_positivePart E]
    exact
      actualCarlsonCapturedBoundaryMass_le_finiteVisibleClusterCoefficientMass
        (positiveFiniteVisibleClusterPart E) hhalf hone
  exact le_antisymm hle hge

theorem coefficientMass_eq_two_mul_capturedBoundaryMass_of_targetLine
    {sigma beta : ℝ} {E : Finset ℂ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hsigmaBeta : sigma < beta)
    (hstable :
      ∀ rho : ℂ, rho ∈ E ↔ (starRingEnd ℂ) rho ∈ E)
    (hzero : ∀ rho ∈ E, RiemannHypothesis.IsNontrivialZero rho)
    (htarget : ∀ rho ∈ E, rho.re = beta)
    (hnoreal : ∀ rho ∈ E, rho.im ≠ 0) :
    finiteVisibleClusterCoefficientMass E =
      2 * actualCarlsonCapturedBoundaryMass
        (sigma := sigma) beta E := by
  have hrealEmpty : realFiniteVisibleClusterPart E = ∅ := by
    ext rho
    constructor
    · intro hrho
      have hrhoData := Finset.mem_filter.mp hrho
      exact False.elim (hnoreal rho hrhoData.1 hrhoData.2)
    · intro hrho
      simp at hrho
  have hemptyMass : finiteVisibleClusterCoefficientMass (∅ : Finset ℂ) = 0 := by
    simp [finiteVisibleClusterCoefficientMass]
  rw [finiteVisibleClusterCoefficientMass_eq_positive_add_negative_add_real]
  rw [finiteVisibleClusterCoefficientMass_negative_eq_positive hstable hzero]
  rw [hrealEmpty]
  rw [hemptyMass, add_zero]
  rw [positiveCoefficientMass_eq_capturedBoundaryMass_of_targetLine
    hhalf hone hsigmaBeta hzero htarget]
  ring

theorem exists_targetLine_actualCarlsonFiniteSeedCanonicalBudgets_of_seedOutside_lt_half
    {S₀ : Finset ℂ} {sigma beta c : ℝ}
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S₀)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hsigmaBeta : sigma < beta)
    (hcap : OutsideClusterRealPartCap S₀ beta)
    (hrealStrict :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
          rho.im = 0 → rho.re < beta)
    (hseedOutside :
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S₀ < c / 2) :
    ∃ loss : ℝ, ∃ S : Finset ℂ,
      0 < loss ∧
      0 < c - loss ∧
      (∀ rho ∈ S₀, rho ∈ S) ∧
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      IsTargetRealPartNontrivialZeroSeed beta S ∧
      OutsideClusterRealPartCap S beta ∧
      (∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta) ∧
      (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) ∧
      finiteVisibleClusterCoefficientMass (S \ S₀) < loss ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
        (c - loss) - (c - loss) / 2 := by
  let B₀ := actualCarlsonOutsideClusterBoundaryMass
    (sigma := sigma) beta S₀
  let d := c - 2 * B₀
  have hd : 0 < d := by
    dsimp [d, B₀]
    linarith
  rcases
      exists_targetLine_actualCarlsonFiniteSeedGapTransferCluster
        (sigma := sigma) (beta := beta) (c := d) (q := 0)
        hS₀ hseed hhalf hone hd hcap with
    ⟨S, hS₀S, hS, htarget, hcapS, hreHigh, hreReal, hsmall⟩
  let E := S \ S₀
  have hsub : S₀ ⊆ S := fun rho hrho => hS₀S rho hrho
  have hstableE :
      ∀ rho : ℂ, rho ∈ E ↔ (starRingEnd ℂ) rho ∈ E :=
    finiteSeedExtension_sdiff_conjugationStable hS₀ hS
  have hzeroE :
      ∀ rho ∈ E, RiemannHypothesis.IsNontrivialZero rho := by
    intro rho hrho
    exact (htarget rho (Finset.mem_sdiff.mp hrho).1).1
  have htargetE : ∀ rho ∈ E, rho.re = beta := by
    intro rho hrho
    exact (htarget rho (Finset.mem_sdiff.mp hrho).1).2
  have hnorealE : ∀ rho ∈ E, rho.im ≠ 0 := by
    intro rho hrho him
    have hlt := hrealStrict rho (hzeroE rho hrho) him
    have hre := htargetE rho hrho
    linarith
  have hcoefficient :=
    coefficientMass_eq_two_mul_capturedBoundaryMass_of_targetLine
      (E := E) hhalf hone hsigmaBeta hstableE hzeroE htargetE hnorealE
  have hallocation :=
    actualCarlsonCapturedBoundaryMass_extension_add_outside_eq_seedOutside
      (beta := beta) hsub hhalf hone
  have houtNonneg :
      0 ≤ actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S := by
    unfold actualCarlsonOutsideClusterBoundaryMass weightedPowerBoundaryMass
    apply tsum_nonneg
    intro index
    by_cases heq : actualCarlsonOutsideClusterRealPart beta S index = beta
    · simp [heq, actualCarlsonOutsideClusterWeight_nonneg]
    · simp [heq]
  let upper := c - 4 * actualCarlsonOutsideClusterBoundaryMass
    (sigma := sigma) beta S
  have hcoefficientUpper :
      finiteVisibleClusterCoefficientMass E < upper := by
    dsimp [upper, d, B₀] at hsmall ⊢
    rw [hcoefficient]
    linarith
  let loss := (finiteVisibleClusterCoefficientMass E + upper) / 2
  have hadded : finiteVisibleClusterCoefficientMass E < loss := by
    dsimp [loss]
    linarith
  have hlossUpper : loss < upper := by
    dsimp [loss]
    linarith
  have hcoefficientNonneg : 0 ≤ finiteVisibleClusterCoefficientMass E :=
    finiteVisibleClusterCoefficientMass_nonneg E
  have hloss : 0 < loss := by linarith
  have hnet : 0 < c - loss := by
    dsimp [upper] at hlossUpper
    linarith
  have hcanonical :
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
        (c - loss) - (c - loss) / 2 := by
    dsimp [upper] at hlossUpper
    linarith
  exact
    ⟨loss, S, hloss, hnet, hS₀S, hS, htarget, hcapS,
      hreHigh, hreReal, by simpa [E] using hadded, hcanonical⟩

end
end PrimeNumberTheorem
