import PrimeNumberTheorem.HalfIsolatedZeroDichotomy.DetectionPointChoice

/-!
# Axiom audit for the promoted `DetectionPointChoice` theorems

The three former axioms of the detection-point choice route are now
theorems.  This file prints their axiom dependencies: a clean promotion
shows only `propext`, `Classical.choice`, `Quot.sound` (standard
mathlib axioms) and no `sorryAx`.

- Appendix A: interval covering / avoidance lemma.
- Appendix B: windowed zero count (T0-form and uniform [a, b]-form).
- Main assembly: ring mass → dyadic distance sum → good detection point.
-/

open PrimeNumberTheorem

#print axioms HalfIsolatedZeroDichotomy.exists_point_avoiding_small_intervals
#print axioms HalfIsolatedZeroDichotomy.exists_windowedZeroMultiplicity_le
#print axioms HalfIsolatedZeroDichotomy.exists_windowedZeroMultiplicity_le_uniform
#print axioms HalfIsolatedZeroDichotomy.ringMass_le_windowedCount
#print axioms HalfIsolatedZeroDichotomy.dyadic_distance_sum_le
#print axioms HalfIsolatedZeroDichotomy.exists_good_detection_point
