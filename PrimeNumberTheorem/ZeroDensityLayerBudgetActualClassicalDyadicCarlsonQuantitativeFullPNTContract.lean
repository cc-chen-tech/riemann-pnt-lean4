import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeFullPNT

/-!
# Classical dyadic Carlson quantitative full-PNT contract

Public contract for the pointwise complete natural relative-PNT error
majorant assembled from the finite zero tail, closed real-axis term, and the
certified explicit-formula remainder bound.
-/

open Filter
open scoped Topology

namespace PrimeNumberTheorem

#check classicalDyadicCarlsonFullPNTErrorMajorant
#check tendsto_abs_actualPNTClosedRealAxisRelativeTerm_natural_zero
#check tendsto_classicalDyadicCarlsonFullPNTErrorMajorant_zero
#check eventually_abs_relativeChebyshevPsi0Error_le_classicalFullPNTMajorant
#check exists_selectedClassicalAdmissibleDyadicCarlsonQuantitativeFullPNTErrorMajorant

end PrimeNumberTheorem
