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

-- Sign, factor pi, and fixed gamma product are part of the exact error.
#check (@two_mul_cubicAFEDoubleSumFinite_sub_normSq_eq :
  ∀ (t : ℝ) {X V : ℝ}, 1 / 2 < X → 0 < V →
    2 * cubicAFEDoubleSumFinite t X V -
        (Complex.normSq (riemannZeta (cubicCriticalPoint t)) : ℂ) =
      -(I * (∫ x : ℝ in -X..X,
        cubicAFECompletedIntegrand t ((x : ℂ) + (V : ℂ) * I))) /
        ((Real.pi : ℂ) * cubicAFEGammaProduct t 0))

#check (@tendsto_two_mul_cubicAFEDoubleSumFinite :
  ∀ (t : ℝ) {X : ℝ}, 1 / 2 < X →
    Tendsto (fun V : ℝ ↦ 2 * cubicAFEDoubleSumFinite t X V)
      atTop
      (nhds (Complex.normSq (riemannZeta (cubicCriticalPoint t)) : ℂ)))

end PrimeNumberTheorem.MWKFCubic
