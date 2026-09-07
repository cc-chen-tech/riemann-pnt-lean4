import PrimeNumberTheorem.MWKFCubicAFEIntegralLimit

open Filter

namespace PrimeNumberTheorem.MWKFCubic

-- This must be an actual full-line integral limit, with no domination
-- hypothesis supplied by the caller and no restriction on the height sequence.
#check (@tendsto_cubicAFEMollifiedMomentFinite :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 →
    ∀ {X : ℝ}, 1 / 2 < X →
      Tendsto (fun V : ℝ ↦ cubicAFEMollifiedMomentFinite W T X V)
        atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)))

end PrimeNumberTheorem.MWKFCubic
