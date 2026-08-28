import HardyTheorem.ConreyHorizontalJensenAsymptotic

open HardyTheorem Complex

#check conreyHorizontalJensenHeightBase_le_three_mul_exp_two
#check conreyHorizontalJensenGrowthLog_le_twentyFive_mul
#check conreyHorizontalJensenFactorLogDenominator_lower
#check conreyHorizontalJensenFactorZeroMassMajorant
#check conreyHorizontalJensenFactorZeroMassMajorant_bounds
#check exists_conreyHorizontalJensenFactorZeroMassMajorant_bounds
#check conreyHorizontalJensenFactorLogVariationMajorant_le_eightyOneMillion
#check conreyHorizontalJensenCoarseGeometry
#check conreyHorizontalJensenExplicitHorizontalRhs_le_coarse
#check exists_conreyHorizontalJensenHeight_weightedLogDeriv_le_coarse
#check tendsto_conreyHorizontalJensen_coarse_div_exp_div_zero

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

example {Creg Cmass L U : ℝ} {Y : ℕ} {R : ℝ}
    (hCreg : 1 ≤ Creg) (hCregTop : Creg ≤ Real.exp L)
    (hCmass : 1 ≤ Cmass) (hCmassTop : Cmass ≤ Real.exp L)
    (hY : 2 ≤ Y) (hYtop : (Y : ℝ) ≤ Real.exp L)
    (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U)
    (hUtop : U + 1 ≤ Real.exp L) :
    conreyHorizontalJensenFactorLogVariationMajorant Creg Y R L U
        (conreyHorizontalJensenFactorZeroMassMajorant Cmass Y R L U) ≤
      81000000 * L ^ 4 :=
  conreyHorizontalJensenFactorLogVariationMajorant_le_eightyOneMillion
    hCreg hCregTop hCmass hCmassTop hY hYtop hR0 hRmax hL hU hUtop

example :
    ∃ Creg Cmass : ℝ, 1 ≤ Creg ∧ 1 ≤ Cmass ∧
      ∀ {Y : ℕ} {R L U : ℝ}, 2 ≤ Y →
        (Y : ℝ) ≤ Real.exp L → 0 ≤ R → R ≤ 6 / 5 → 40000 ≤ L →
        conreyHorizontalRightEdge L + 1 ≤ U → U + 1 ≤ Real.exp L →
        Creg ≤ Real.exp L → Cmass ≤ Real.exp L →
        ∃ t ∈ Set.Icc U (U + 1),
          (∀ x ∈ Set.Icc (conreyHorizontalLeftEdge R L)
              (conreyHorizontalRightEdge L),
            conreyHorizontalJensenProduct Y R L
              ((x : ℂ) + Complex.I * (t : ℂ)) ≠ 0) ∧
          |∫ x in conreyHorizontalLeftEdge R L..conreyHorizontalRightEdge L,
              (x - conreyHorizontalLeftEdge R L) *
                (logDeriv (conreyHorizontalJensenProduct Y R L)
                  ((x : ℂ) + Complex.I * (t : ℂ))).im| ≤
            1100000000000 * L ^ 7 :=
  exists_conreyHorizontalJensenHeight_weightedLogDeriv_le_coarse

#print axioms conreyHorizontalJensenHeightBase_le_three_mul_exp_two
#print axioms conreyHorizontalJensenGrowthLog_le_twentyFive_mul
#print axioms conreyHorizontalJensenFactorLogDenominator_lower
#print axioms conreyHorizontalJensenFactorZeroMassMajorant_bounds
#print axioms exists_conreyHorizontalJensenFactorZeroMassMajorant_bounds
#print axioms conreyHorizontalJensenFactorLogVariationMajorant_le_eightyOneMillion
#print axioms conreyHorizontalJensenCoarseGeometry
#print axioms conreyHorizontalJensenExplicitHorizontalRhs_le_coarse
#print axioms exists_conreyHorizontalJensenHeight_weightedLogDeriv_le_coarse
#print axioms tendsto_conreyHorizontalJensen_coarse_div_exp_div_zero
