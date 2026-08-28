import HardyTheorem.ConreyHorizontalJensenAsymptotic

open HardyTheorem

#check conreyHorizontalJensenHeightBase_le_three_mul_exp_two
#check conreyHorizontalJensenGrowthLog_le_twentyFive_mul
#check conreyHorizontalJensenFactorLogDenominator_lower
#check conreyHorizontalJensenFactorZeroMassMajorant
#check conreyHorizontalJensenFactorZeroMassMajorant_bounds
#check exists_conreyHorizontalJensenFactorZeroMassMajorant_bounds

example :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Y : ℕ} {R L U : ℝ}, 2 ≤ Y →
      (Y : ℝ) ≤ Real.exp L → 0 ≤ R → R ≤ 6 / 5 → 40000 ≤ L →
      conreyHorizontalRightEdge L + 1 ≤ U → U + 1 ≤ Real.exp L →
      C ≤ Real.exp L →
      conreyHorizontalJensenFactorZeroMass Y R L U ≤
          conreyHorizontalJensenFactorZeroMassMajorant C Y R L U ∧
        0 ≤ conreyHorizontalJensenFactorZeroMassMajorant C Y R L U ∧
        conreyHorizontalJensenFactorZeroMassMajorant C Y R L U ≤
          1000 * L ^ 2 :=
  exists_conreyHorizontalJensenFactorZeroMassMajorant_bounds

#print axioms conreyHorizontalJensenHeightBase_le_three_mul_exp_two
#print axioms conreyHorizontalJensenGrowthLog_le_twentyFive_mul
#print axioms conreyHorizontalJensenFactorLogDenominator_lower
#print axioms conreyHorizontalJensenFactorZeroMassMajorant_bounds
#print axioms exists_conreyHorizontalJensenFactorZeroMassMajorant_bounds
