import PrimeNumberTheorem.ZeroDensityLayerBudgetEventuallyZeroFreeUnified

namespace PrimeNumberTheorem

example
    {upperError : ℝ → ℝ} {cost : ℝ → ℝ → ℝ}
    {zeroFree : ℝ → ℝ → Prop}
    {grid : DynamicFiniteHeightGrid}
    (zeroFreeHeights :
      EventuallyDynamicZeroFreeHeightCertificate zeroFree grid)
    (explicitFormula :
      ZeroFreeExplicitFormulaUpperCertificate upperError cost zeroFree) :
    ∀ᶠ x in Filter.atTop,
      |upperError x| ≤
        cost x (dynamicFiniteGridOptimalHeight cost grid x) :=
  eventually_zeroFreeExplicitFormula_upper_at_dynamicOptimalHeight
    zeroFreeHeights explicitFormula

end PrimeNumberTheorem
