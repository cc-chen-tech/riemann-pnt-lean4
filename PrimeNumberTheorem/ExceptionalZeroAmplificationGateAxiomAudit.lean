import PrimeNumberTheorem.ExceptionalZeroAmplificationGateContract

/-!
Axiom audit for the amplification gate contract.

Expected result: the gate theorems depend on no *new* axioms.  Since
`carlson_zeroDensity_isBigO` and `exists_carlson_parameterized_count_certificate`
are proved unconditionally in `CarlsonAsymptotic.lean`, the printed axiom list
should contain only the standard library base axioms (`Classical.choice`,
`propext`, `funext`, `Quot.sound`).  The six unproved gate inputs are explicit
parameters, so they must NOT appear as axioms.  Any additional axiom in the
printed list is an existing repository assumption and must be reviewed one by
one before the gate is considered closed.
-/

#print axioms PrimeNumberTheorem.ExceptionalZeroAmplificationGate.amplificationGate
#print axioms PrimeNumberTheorem.ExceptionalZeroAmplificationGate.amplificationGate_of_inputs
#print axioms PrimeNumberTheorem.ExceptionalZeroAmplificationGate.amplificationGate_excludes_seed
