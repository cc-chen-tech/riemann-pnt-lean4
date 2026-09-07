import PrimeNumberTheorem.MWKFCubicAFEPhysicalEndpoint

open PrimeNumberTheorem.MWKFCubic MeasureTheory Filter

#check cubicAFEProgressionPhysicalSummandVertical
#check tendsto_cubicAFEProgressionPhysicalSummand_height
#check integrableOn_cubicAFEProgressionPhysicalSummandVertical
#check tendsto_cubicAFECompletedPhysicalIntegral

-- Zero shift is allowed for the pointwise height limit, not for the
-- uncut spatial integrability theorem below.
example (W : CubicTestWeight) (T t : ℝ) :
    Tendsto (fun V : ℝ ↦ cubicAFEProgressionPhysicalSummand W T (3 / 4) V 1 1 0 t 1)
      atTop (nhds (cubicAFEProgressionPhysicalSummandVertical W T (3 / 4) 1 1 0 t 1)) :=
  tendsto_cubicAFEProgressionPhysicalSummand_height W T (by norm_num) (by norm_num) 0 t
    (by norm_num [cubicAFEProgressionDomain])

example (W : CubicTestWeight) (T t : ℝ) :
    IntegrableOn (fun x ↦ ‖cubicAFEProgressionPhysicalSummandVertical W T (3 / 4) 1 1 (-1) t x‖)
      (cubicAFEProgressionDomain 1 1 (-1)) :=
  (integrableOn_cubicAFEProgressionPhysicalSummandVertical W T (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) t).norm

example (W : CubicTestWeight) (T t : ℝ) :
    Tendsto (fun J : ℕ ↦ ∫ x in cubicAFEProgressionDomain 1 1 (-1),
      (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond 1 1 (-1) x) : ℂ) *
        cubicAFEProgressionPhysicalSummandVertical W T (3 / 4) 1 1 (-1) t x)
      atTop (nhds (∫ x in cubicAFEProgressionDomain 1 1 (-1),
        cubicAFEProgressionPhysicalSummandVertical W T (3 / 4) 1 1 (-1) t x)) :=
  tendsto_cubicAFECompletedPhysicalIntegral W T (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) t
