import PrimeNumberTheorem.WindowedMellinL2
/-!
Axiom audit for the L2 windowed Mellin response analytic core.
Expected: only `propext`, `Classical.choice`, `Quot.sound`.
-/
open PrimeNumberTheorem
#print axioms WindowedMellinL2.integral_cpow_eq_integralFactor
#print axioms WindowedMellinL2.integral_rpow_sub_one_eq
#print axioms WindowedMellinL2.seedResponse_aligned_lowerBound
#print axioms WindowedMellinL2.complementaryResponse_le
#print axioms WindowedMellinL2.norm_cpow_ofReal_pos
