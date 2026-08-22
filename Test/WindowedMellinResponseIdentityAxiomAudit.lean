import PrimeNumberTheorem.WindowedMellinResponseIdentity
/-!
Axiom audit for the L2 windowed Mellin response identity.
Expected: only `propext`, `Classical.choice`, `Quot.sound` (the truncated
explicit formula remains an explicit input `hexplicit`).
-/
open PrimeNumberTheorem
#print axioms WindowedMellinL2.windowedIntegral_cubicKernel_eq_response
#print axioms WindowedMellinL2.windowedMellinResponse_eq_sum_add_error
