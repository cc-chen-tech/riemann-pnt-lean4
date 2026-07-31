import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTSharpSignedOmega
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageNaturalWitness

namespace PrimeNumberTheorem

 theorem HasFarNaturalPointTargetAmplitudeWitness.signAlternative
    {f amplitude : ℕ → ℝ}
    (h : HasFarNaturalPointTargetAmplitudeWitness f amplitude) :
    HasFarNaturalPointPositiveTargetAmplitudeWitness f amplitude ∨
      HasFarNaturalPointNegativeTargetAmplitudeWitness f amplitude := by
  classical
  by_cases hpos : HasFarNaturalPointPositiveTargetAmplitudeWitness f amplitude
  · exact Or.inl hpos
  · right
    have hposFail :
        ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → ¬ amplitude m ≤ f m := by
      simpa [HasFarNaturalPointPositiveTargetAmplitudeWitness] using hpos
    rcases hposFail with ⟨M₀, hM₀⟩
    intro M
    rcases h (max M M₀) with ⟨m, hm, habs⟩
    refine ⟨m, le_trans (le_max_left M M₀) hm, ?_⟩
    have hnotPos : ¬ amplitude m ≤ f m :=
      hM₀ m (le_trans (le_max_right M M₀) hm)
    have habsCases : f m ≤ -amplitude m ∨ amplitude m ≤ f m := by
      rcases (le_abs.mp habs) with hpositive | hnegative
      · exact Or.inr hpositive
      · exact Or.inl (by linarith)
    exact habsCases.resolve_right hnotPos

theorem actualZeroPackage_visibleCluster_naturalPoint_signAlternative
    (H : ℝ → ℝ) (hH : Filter.Tendsto H Filter.atTop Filter.atTop)
    (T beta L q : ℝ) (hL : 0 < L)
    (henergy : 0 < actualEqualRealPartZeroPackageEnergy T beta L)
    (hq : q < 1) :
    HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain H
            (ZeroForcedOscillation.equalRealPartZeroPackage T beta) m)
        (fun m =>
          q * (Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
            targetZeroPowerAmplitude beta m)) ∨
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain H
            (ZeroForcedOscillation.equalRealPartZeroPackage T beta) m)
        (fun m =>
          q * (Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
            targetZeroPowerAmplitude beta m)) := by
  apply HasFarNaturalPointTargetAmplitudeWitness.signAlternative
    (h := hasFarNaturalPointTargetAmplitudeWitness_actualZeroPackage_visibleCluster
      H hH T beta L q hL henergy hq)

end PrimeNumberTheorem
