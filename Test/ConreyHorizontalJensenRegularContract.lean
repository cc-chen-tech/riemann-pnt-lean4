import HardyTheorem.ConreyHorizontalJensenRegular

open HardyTheorem

#check conreyHorizontalJensenRadiusGap
#check conreyHorizontalJensenFactorRadius
#check conreyHorizontalJensenGoodRadiusLower
#check conreyHorizontalJensenGoodRadiusUpper
#check one_fifth_lt_conreyHorizontalJensenRadiusGap
#check conreyHorizontalJensenRadiusGap_lt_one_fourth
#check conreyHorizontalJensenBufferGeometry
#check conreyHorizontalJensenFactorZeroMass
#check conreyHorizontalJensenFactorZeroSupport
#check conreyHorizontalJensenFactorDiskSeparation
#check exists_conreyHorizontalJensenFactorZeroMass_le
#check card_conreyHorizontalJensenFactorZeroSupport_le_mass
#check conreyHorizontalJensenFactorDiskSeparation_lower_of_mass_le
#check mem_conreyHorizontalJensenFactorZeroSupport_iff_zero
#check exists_conreyHorizontalJensenGoodFactorCircle
#check conreyHorizontalJensenFactorCircleLogUpper
#check conreyHorizontalJensenFactorCenterLogLower
#check exists_conreyHorizontalJensenGoodFactor_logDeriv_le

example {R L : ℝ} (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L) :
    (1 / 5 : ℝ) < conreyHorizontalJensenRadiusGap R L ∧
      conreyHorizontalJensenRadiusGap R L < (1 / 4 : ℝ) :=
  ⟨one_fifth_lt_conreyHorizontalJensenRadiusGap hR0 hRmax hL,
    conreyHorizontalJensenRadiusGap_lt_one_fourth hR0 hRmax hL⟩

example :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Y : ℕ} {R L U : ℝ}, 2 ≤ Y →
      (Y : ℝ) ≤ Real.exp L → 0 ≤ R → R ≤ 6 / 5 → 40000 ≤ L →
      conreyHorizontalRightEdge L + 1 ≤ U → U + 1 ≤ Real.exp L →
      conreyHorizontalJensenFactorZeroMass Y R L U ≤
        (Real.log (C * (Y : ℝ) *
            (conreyHorizontalJensenHeightBase L U) ^ 6 * (L + 2) ^ 2) +
          Real.log 6) /
            Real.log (conreyHorizontalJensenOuterRadius L /
              conreyHorizontalJensenFactorRadius R L) :=
  exists_conreyHorizontalJensenFactorZeroMass_le

#print axioms one_fifth_lt_conreyHorizontalJensenRadiusGap
#print axioms conreyHorizontalJensenRadiusGap_lt_one_fourth
#print axioms conreyHorizontalJensenBufferGeometry
#print axioms exists_conreyHorizontalJensenFactorZeroMass_le
#print axioms conreyHorizontalJensenFactorDiskSeparation_lower_of_mass_le
#print axioms exists_conreyHorizontalJensenGoodFactorCircle
#print axioms exists_conreyHorizontalJensenGoodFactor_logDeriv_le
