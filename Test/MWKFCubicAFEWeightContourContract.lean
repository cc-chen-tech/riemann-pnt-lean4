import PrimeNumberTheorem.MWKFCubicAFEWeightContour

open PrimeNumberTheorem.MWKFCubic

#check differentiableOn_cubicAFEWeightMellinNumerator
#check cubicAFEWeightMellinNumerator_zero
#check cubicAFEWeightMellinKernel_eq_remainder_add
#check boundaryRectIntegral_cubicAFEWeightMellinKernel

open Complex

example (t P V : ℝ) (hV : 0 < V) :
    MathlibAux.boundaryRectIntegral (cubicAFEWeightMellinKernel t P)
      (-1 / 4) (3 / 4) (-V) V = 2 * Real.pi * I :=
  boundaryRectIntegral_cubicAFEWeightMellinKernel t P (by norm_num) (by norm_num)
    (by norm_num) (by linarith) hV
