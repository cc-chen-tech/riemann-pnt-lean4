import PrimeNumberTheorem.HalfIsolatedZeroDichotomy.DetectionPointChoice

/-!
# Axiom audit for the promoted `DetectionPointChoice` theorems

The three former axioms of the detection-point choice route are now
theorems (Appendices A and B plus the main assembly).  This file prints
their axiom dependencies: a clean promotion shows only `propext`,
`Classical.choice`, `Quot.sound` (standard mathlib axioms) and no
`sorryAx`.

- Appendix A: `exists_point_avoiding_small_intervals` (interval covering).
- Appendix B: `exists_windowedZeroMultiplicity_le` (T0-form) and
  `exists_windowedZeroMultiplicity_le_uniform` (uniform [a, b]-form).
- Main assembly: `ringMass_le_windowedCount` (windowed ring mass),
  `dyadic_distance_sum_le` (high-region dyadic split), and
  `exists_good_detection_point` (L1 main theorem: a good detection
  point with frequency-weighted mass
  `C (1 + log(T0+H+6))^2 (T0+H) / (T0 H)`).

Run with `lake env lean Test/DetectionPointChoiceAxiomAudit.lean`.
-/

open PrimeNumberTheorem

#print axioms HalfIsolatedZeroDichotomy.exists_point_avoiding_small_intervals
#print axioms HalfIsolatedZeroDichotomy.exists_windowedZeroMultiplicity_le
#print axioms HalfIsolatedZeroDichotomy.exists_windowedZeroMultiplicity_le_uniform
#print axioms HalfIsolatedZeroDichotomy.ringMass_le_windowedCount
#print axioms HalfIsolatedZeroDichotomy.dyadic_distance_sum_le
#print axioms HalfIsolatedZeroDichotomy.exists_good_detection_point
