import PrimeNumberTheorem.MWKFCubicAFEInfiniteCompletedMoment

open PrimeNumberTheorem.MWKFCubic
open Complex Filter MeasureTheory
open scoped Topology

#check tendsto_cubicAFECompletedNonzeroModeMomentFinite_height
#check cubicMollifiedSecondMoment_eq_completed_modes
#check cubicMollifiedSecondMoment_eq_completed_principal_remainder

-- The remainder is the proved limit of the original nonzero-mode sum,
-- not merely an arbitrary R satisfying an assumed exact decomposition.
example (W : CubicTestWeight) :
    Tendsto (fun V : ℝ ↦ cubicAFECompletedNonzeroModeMomentFinite W 3 1 V 2) atTop
      (nhds (cubicAFECompletedNonzeroModeMomentVertical W 3 1 2)) := by
  exact tendsto_cubicAFECompletedNonzeroModeMomentFinite_height W (by norm_num) (by norm_num) 2

-- Keep the real part and the physical factor T when normalizing the
-- principal part. This is an exact identity, not a 4/3 asymptotic claim.
example (W : CubicTestWeight) :
    cubicMollifiedSecondMoment W 3 = 3 * cubicAFECompletedPrincipalPart W 3 1 2 +
      cubicAFECompletedRemainder W 3 1 2 := by
  exact cubicMollifiedSecondMoment_eq_completed_principal_remainder W (by norm_num) (by norm_num) 2
