import PrimeNumberTheorem.WindowedDetectorResponseKernel
/-!
Axiom audit for the windowed detector response kernel.
Expected: only `propext`, `Classical.choice`, `Quot.sound`.
-/
open PrimeNumberTheorem
#print axioms WindowedMellinL2.norm_zeroResponseKernel_eq
#print axioms WindowedMellinL2.norm_zeroResponseKernel_correctScale_bounds
#print axioms WindowedMellinL2.norm_zeroResponseKernel_le_uniform
