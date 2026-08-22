import PrimeNumberTheorem.ExceptionalZeroAmplificationGateInstantiation
/-!
Axiom audit for the gate instantiation skeleton.
Expected: only `propext`, `Classical.choice`, `Quot.sound` (plus whatever
the gate contract itself audits to — it is parameter-free of sorryAx).
-/
open PrimeNumberTheorem
#print axioms ExceptionalZeroAmplificationGate.seedRoots_eventually_nonempty
#print axioms ExceptionalZeroAmplificationGate.no_nontrivial_zero_re_gt_two_thirds_of_gateInputs
