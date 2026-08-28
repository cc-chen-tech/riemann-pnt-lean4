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

example {Y : ℕ} {R L U J : ℝ} (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L) (hU : conreyHorizontalRightEdge L + 1 ≤ U)
    (hmass : conreyHorizontalJensenFactorZeroMass Y R L U ≤ J) :
    0 < conreyHorizontalJensenRadiusGap R L / (16 * (J + 1)) ∧
      conreyHorizontalJensenRadiusGap R L / (16 * (J + 1)) ≤
        conreyHorizontalJensenFactorDiskSeparation Y R L U :=
  conreyHorizontalJensenFactorDiskSeparation_lower_of_mass_le
    hR0 hRmax hL hU hmass

example {Y : ℕ} {R L U : ℝ} (hY : 2 ≤ Y) (hR0 : 0 ≤ R)
    (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) {z : ℂ}
    (hz : z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
      (conreyHorizontalJensenFactorRadius R L)) :
    z ∈ conreyHorizontalJensenFactorZeroSupport Y R L U ↔
      conreyHorizontalJensenProduct Y R L z = 0 :=
  mem_conreyHorizontalJensenFactorZeroSupport_iff_zero
    hY hR0 hRmax hL hU hz

example {Y : ℕ} {R L U : ℝ} (hY : 2 ≤ Y) (hR0 : 0 ≤ R)
    (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) :
    ∃ q : ℝ,
      0 < q ∧ q ∈ Set.Icc
        (conreyHorizontalJensenGoodRadiusLower R L)
        (conreyHorizontalJensenGoodRadiusUpper R L) ∧
      (∀ z ∈ Metric.sphere (conreyHorizontalJensenCenter L U) q,
        ∀ rho ∈ conreyHorizontalJensenFactorZeroSupport Y R L U,
          conreyHorizontalJensenFactorDiskSeparation Y R L U ≤ dist z rho) ∧
      (∀ z ∈ Metric.sphere (conreyHorizontalJensenCenter L U) q,
        z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
          (conreyHorizontalJensenFactorRadius R L)) ∧
      ∀ z ∈ Metric.sphere (conreyHorizontalJensenCenter L U) q,
        conreyHorizontalJensenProduct Y R L z ≠ 0 :=
  exists_conreyHorizontalJensenGoodFactorCircle hY hR0 hRmax hL hU

example :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Y : ℕ} {R L U : ℝ}, 2 ≤ Y →
      (Y : ℝ) ≤ Real.exp L → 0 ≤ R → R ≤ 6 / 5 → 40000 ≤ L →
      conreyHorizontalRightEdge L + 1 ≤ U → U + 1 ≤ Real.exp L →
      ∃ q : ℝ, ∃ g : ℂ → ℂ,
        q ∈ Set.Icc (conreyHorizontalJensenGoodRadiusLower R L)
          (conreyHorizontalJensenGoodRadiusUpper R L) ∧
        AnalyticOnNhd ℂ g
          (Metric.closedBall (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenFactorRadius R L)) ∧
        (∀ u : (Metric.closedBall (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenFactorRadius R L) : Set ℂ), g u ≠ 0) ∧
        conreyHorizontalJensenFactorCenterLogLower Y R L U ≤
          Real.log ‖g (conreyHorizontalJensenCenter L U)‖ ∧
        (∀ z ∈ Metric.sphere (conreyHorizontalJensenCenter L U) q,
          Real.log ‖g z‖ ≤
            conreyHorizontalJensenFactorCircleLogUpper C Y R L U) ∧
        (∀ z ∈ Metric.ball (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenFactorRadius R L),
          conreyHorizontalJensenProduct Y R L z ≠ 0 →
            logDeriv (conreyHorizontalJensenProduct Y R L) z =
              (∑ᶠ u,
                (MeromorphicOn.divisor
                  (conreyHorizontalJensenProduct Y R L)
                  (Metric.closedBall (conreyHorizontalJensenCenter L U)
                    (conreyHorizontalJensenFactorRadius R L)) u : ℂ) *
                  (z - u)⁻¹) + logDeriv g z) ∧
        ∀ z ∈ Metric.closedBall (conreyHorizontalJensenCenter L U)
            (conreyHorizontalJensenInnerRadius R L),
          ‖logDeriv g z‖ ≤
            4 * max
                (conreyHorizontalJensenFactorCircleLogUpper C Y R L U -
                  conreyHorizontalJensenFactorCenterLogLower Y R L U) 1 *
              (q + conreyHorizontalJensenInnerRadius R L) /
              (q - conreyHorizontalJensenInnerRadius R L) ^ 2 :=
  exists_conreyHorizontalJensenGoodFactor_logDeriv_le

#print axioms one_fifth_lt_conreyHorizontalJensenRadiusGap
#print axioms conreyHorizontalJensenRadiusGap_lt_one_fourth
#print axioms conreyHorizontalJensenBufferGeometry
#print axioms exists_conreyHorizontalJensenFactorZeroMass_le
#print axioms conreyHorizontalJensenFactorDiskSeparation_lower_of_mass_le
#print axioms exists_conreyHorizontalJensenGoodFactorCircle
#print axioms exists_conreyHorizontalJensenGoodFactor_logDeriv_le
