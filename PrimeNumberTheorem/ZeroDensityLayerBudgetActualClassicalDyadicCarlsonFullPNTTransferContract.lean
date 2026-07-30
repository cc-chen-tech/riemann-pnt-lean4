import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonFullPNTTransfer

open Filter
open scoped Topology

namespace PrimeNumberTheorem

#check @eventually_pintzCarlsonHeight_add_one_le_real_rpow
#check @tendsto_selectedClassicalAdmissibleGoodHeight_atTop
#check @eventually_selectedClassicalAdmissibleGoodHeight_le_polynomialHeight_real
#check @tendsto_actualSelectedClassicalAdmissibleCriticalHalfPNTLayerNorm_zero
#check @tendsto_dynamicRealOrdinatePNTZeroTailNorm_of_height_tendsto
#check @actualSelectedHeightMovingCarlsonStripMass_le_dyadicFixedAnchor
#check @tendsto_actualSelectedClassicalAdmissibleMovingStripMass_zero_of_dyadic
#check @tendsto_dynamicFullPNTZeroTailNorm_of_selectedClassicalAdmissibleDyadicCarlson
#check @selectedClassicalAdmissibleGoodHeight_actualNaturalRemainderCertificate

example :
    ∃ b rate : ℝ,
      0 < b ∧ 0 < rate ∧
        IsCarlsonMovingDyadicLogPowerGap
          (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
        ∀ selection : UniformNaturalPointGoodHeightSelection,
          IsSelectedHeightDynamicZeroFree
              (selectedClassicalAdmissibleGoodHeight b selection)
              (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
            Tendsto
              (fun m : ℕ => dynamicFullPNTZeroTailNorm
                (selectedClassicalAdmissibleGoodHeight b selection) (m : ℝ))
              atTop (𝓝 0) ∧
            ActualSelectedHeightNaturalPointRemainderCertificate 1
              (selectedClassicalAdmissibleGoodHeight b selection) ∧
            Tendsto (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
              atTop (𝓝 0) :=
  exists_selectedClassicalAdmissibleDyadicCarlsonFullPNTTransfer

end PrimeNumberTheorem
