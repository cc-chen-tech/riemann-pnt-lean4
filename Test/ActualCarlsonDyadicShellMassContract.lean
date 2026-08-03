import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonDyadicShellMass

namespace PrimeNumberTheorem

#check pntCarlsonClassicalDensityExponent_lt_one
#check CarlsonEventualMajorant.eventually_actualCarlsonDyadicReciprocalCount_le
#check exists_summable_actualCarlsonDyadicReciprocalCount
#check actualCarlsonDyadicShellMultiplicityMass_le_count_div
#check summable_actualCarlsonDyadicShellMultiplicityMass

example {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    Summable (actualCarlsonDyadicShellMultiplicityMass sigma) :=
  summable_actualCarlsonDyadicShellMultiplicityMass hhalf hone

end PrimeNumberTheorem
