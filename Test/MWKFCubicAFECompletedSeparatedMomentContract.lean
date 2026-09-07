import PrimeNumberTheorem.MWKFCubicAFECompletedSeparatedMoment

open PrimeNumberTheorem.MWKFCubic
open Complex Filter MeasureTheory
open scoped Topology

#check summable_shift_cubicAFECompletedZeroModeBox
#check summable_shift_cubicAFECompletedNonzeroModeBox
#check cubicAFEMollifiedMomentFinite_eq_diagonal_completed_zero_nonzero
#check tendsto_cubicAFECompletedZeroModeMoment_height
#check tendsto_cubicAFEDiagonal_completedNonzero_height

-- The entire original mollifier support, all nonzero shifts and all
-- dyadic boxes occur in the completed zero-mode moment, not a finite sample.
example (W : CubicTestWeight) :
    Tendsto (fun V : ℝ ↦ cubicAFECompletedZeroModeMomentFinite W 2 1 V 2) atTop
      (nhds (cubicAFECompletedZeroModeMomentVertical W 2 1 2)) := by
  exact tendsto_cubicAFECompletedZeroModeMoment_height W (by norm_num) (by norm_num) 2

-- The completed nonzero modes are not silently identified with their
-- uncompleted versions; the zero-mode correction is retained in the limit.
example (W : CubicTestWeight) :
    Tendsto (fun V : ℝ ↦ cubicAFEDiagonalMomentFinite W 2 1 V +
      cubicAFECompletedNonzeroModeMomentFinite W 2 1 V 2) atTop
      (nhds ((cubicMollifiedSecondMoment W 2 : ℂ) -
        cubicAFECompletedZeroModeMomentVertical W 2 1 2)) := by
  exact tendsto_cubicAFEDiagonal_completedNonzero_height W (by norm_num) (by norm_num) 2
