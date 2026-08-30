import PrimeNumberTheorem.MWKFCubicAFEDiagonalHeight

open PrimeNumberTheorem.MWKFCubic
open Complex Filter MeasureTheory
open scoped Topology Interval

#check cubicAFEDiagonalMellinKernel_norm_le
#check integrable_cubicAFEDiagonalMellinKernel
#check integrable_cubicAFEDiagonalPhysicalMellinKernel
#check tendsto_cubicAFEDiagonalPhysicalDoubleIntegral_height
#check tendsto_cubicAFEDiagonalMomentFinite_height

-- Noncoprime d,e are retained in the literal reciprocal-LCM Mellin kernel.
example (t : ℝ) : Integrable (fun v : ℝ ↦
    cubicAFEDiagonalMellinKernel 6 9 t (cubicAFEVerticalPoint 1 v)) := by
  exact integrable_cubicAFEDiagonalMellinKernel t (by norm_num) (by decide) (by decide)

-- Both squarefree coefficients are nonzero inside floor(3^3); the whole
-- physical time/height norm, not only fixed-time slices, is integrable.
example (W : CubicTestWeight) : Integrable (fun p : ℝ × ℝ ↦
    ‖cubicAFEDiagonalPhysicalMellinKernel W 3 1 6 10 p.1 p.2‖) := by
  exact (integrable_cubicAFEDiagonalPhysicalMellinKernel W (by norm_num)
    (by norm_num) (by decide) (by decide)).norm

example (W : CubicTestWeight) :
    Tendsto (fun V : ℝ ↦ cubicAFEDiagonalMomentFinite W 3 1 V) atTop
      (nhds (cubicAFEDiagonalMomentVertical W 3 1)) := by
  exact tendsto_cubicAFEDiagonalMomentFinite_height W (by norm_num) (by norm_num)
