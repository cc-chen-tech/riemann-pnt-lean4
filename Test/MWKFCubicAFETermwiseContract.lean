import PrimeNumberTheorem.MWKFCubicAFETermwise

open Complex Filter
open scoped Interval

namespace PrimeNumberTheorem.MWKFCubic

#check cubicAFEVerticalPoint
#check cubicAFEScalar
#check continuous_cubicAFEScalar_vertical
#check continuous_cubicAFENormalizedDirichletTerm_vertical
#check norm_cubicAFEDirichletTerm_vertical_eq
#check hasSum_intervalIntegral_cubicAFENormalizedDirichletTerm
#check cubicAFEWeightFinite
#check cubicAFEDoubleSumFinite
#check cubicAFEDoubleSumFinite_eq

#check (@tendsto_two_mul_cubicAFEDoubleSumFinite :
  ∀ (t : ℝ) {X : ℝ}, 1 / 2 < X →
    Tendsto (fun V : ℝ ↦ 2 * cubicAFEDoubleSumFinite t X V)
      atTop
      (nhds (Complex.normSq (riemannZeta (cubicCriticalPoint t)) : ℂ)))

end PrimeNumberTheorem.MWKFCubic
