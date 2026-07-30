import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonMiddleMass

open Filter
open scoped Topology

namespace PrimeNumberTheorem

example {k alpha : ℝ} (hk : 0 ≤ k) (halpha : 0 < alpha) :
    ∀ᶠ m : ℕ in atTop,
      pintzCarlsonHeight k (m : ℝ) + 1 ≤ (m : ℝ) ^ alpha :=
  eventually_pintzCarlsonHeight_add_one_le_nat_rpow hk halpha

example {b alpha : ℝ} (hb : 0 < b) (halpha : 0 < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ m : ℕ in atTop,
      selectedClassicalAdmissibleGoodHeight b selection (m : ℝ) ≤
        selectedUniformGoodHeight alpha selection (m : ℝ) :=
  eventually_selectedClassicalAdmissibleGoodHeight_le_selectedUniformGoodHeight
    hb halpha selection

example {b alpha : ℝ} {delta : ℕ → ℝ}
    (hb : 0 < b) (halpha : 0 < alpha) (halpha_lt : alpha < 1 / 16)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hdelta_nonneg : ∀ m, 0 ≤ delta m)
    (hdelta_pos : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdelta_le : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hgap : IsCarlsonMovingDyadicLogPowerGap delta) :
    Tendsto
      (actualSelectedHeightMovingCarlsonMiddleMass
        (selectedClassicalAdmissibleGoodHeight b selection) delta)
      atTop (𝓝 0) :=
  tendsto_actualSelectedClassicalAdmissibleMovingMiddleMass_zero_of_dyadic
    hb halpha halpha_lt selection hdelta_nonneg hdelta_pos hdelta_le hgap

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
              (actualSelectedHeightMovingCarlsonMiddleMass
                (selectedClassicalAdmissibleGoodHeight b selection)
                (classicalAdmissibleDyadicCarlsonGapWidth rate))
              atTop (𝓝 0) :=
  exists_selectedClassicalAdmissibleDyadicCarlsonMiddleMassDecay

end PrimeNumberTheorem
