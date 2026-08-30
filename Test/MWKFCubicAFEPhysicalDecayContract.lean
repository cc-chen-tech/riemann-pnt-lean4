import PrimeNumberTheorem.MWKFCubicAFEPhysicalDecay

open PrimeNumberTheorem.MWKFCubic MeasureTheory

-- The real product is arbitrary positive, not only an integer sample.
example (t X V P : ℝ) (hP : 0 < P) :
    ‖cubicAFERealProductWeightFinite t X V P‖ ≤
      cubicAFEWeightEnvelope X V t * P ^ (-X) :=
  norm_cubicAFERealProductWeightFinite_le_envelope t X V hP

-- Negative finite heights must be allowed without an orientation assumption.
example (t X P : ℝ) (hP : 0 < P) :
    ‖cubicAFERealProductWeightFinite t X (-3) P‖ ≤
      cubicAFEWeightEnvelope X (-3) t * P ^ (-X) :=
  norm_cubicAFERealProductWeightFinite_le_envelope t X (-3) hP

#check norm_cubicAFEProgressionPhysicalSummand_le_envelope
#check integrable_cubicAFEPhysicalTimeEnvelope
#check integrable_cubicAFEHalfLinePower
#check cubicAFEDyadicLowerWeight_mul_rpow_le
