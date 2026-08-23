import PrimeNumberTheorem.WindowedMellinL3
/-!
Axiom audit for the L3 complementary-layer assembly and the top-layer
(A) sums.  Expected: only `propext`, `Classical.choice`, `Quot.sound`.
-/
open PrimeNumberTheorem
#print axioms WindowedMellinL3.complementaryResponseSum_le
#print axioms WindowedMellinL3.complementaryResponseSum_lt_seedResponse
#print axioms WindowedMellinL3.topLayerMass_le
#print axioms WindowedMellinL3.topLayerResponseSum_le
#print axioms WindowedMellinL3.topLayerResponseSum_le_of_kernel
#print axioms WindowedMellinL3.topAndComplementaryResponse_lt_seedScale
#print axioms WindowedMellinL3.topLayerCoeffResponseSum_le
#print axioms WindowedMellinL3.complementaryCoeffResponseSum_le
#print axioms PrimeNumberTheorem.WindowedMellinL3.topLayerPacket_card_le_of_mass
