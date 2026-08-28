import HardyTheorem.ConreyHorizontalJensenIntegral

open HardyTheorem

#check abs_im_inv_horizontal_sub_eq_poissonKernel
#check integral_abs_im_inv_horizontal_sub_le_pi
#check abs_integral_weighted_im_inv_horizontal_sub_le
#check conreyHorizontalJensenFactorZeroHeights
#check conreyHorizontalJensenFactorHorizontalSeparation
#check conreyHorizontalJensenFactorHorizontalSeparation_lower_of_mass_le
#check exists_conreyHorizontalJensenFactorAdmissibleHeight

example {a b t : ℝ} {rho : ℂ} (hab : a ≤ b) (ht : t ≠ rho.im) :
    |∫ x in a..b, (x - a) *
        ((((x : ℂ) + Complex.I * (t : ℂ) - rho)⁻¹).im)| ≤
      (b - a) * Real.pi :=
  abs_integral_weighted_im_inv_horizontal_sub_le hab ht

example {Y : ℕ} {R L U J : ℝ} (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L) (hU : conreyHorizontalRightEdge L + 1 ≤ U)
    (hmass : conreyHorizontalJensenFactorZeroMass Y R L U ≤ J) :
    0 < 1 / (4 * (J + 1)) ∧
      1 / (4 * (J + 1)) ≤
        conreyHorizontalJensenFactorHorizontalSeparation Y R L U :=
  conreyHorizontalJensenFactorHorizontalSeparation_lower_of_mass_le
    hR0 hRmax hL hU hmass

example {Y : ℕ} {R L U : ℝ} (hY : 2 ≤ Y) (hR0 : 0 ≤ R)
    (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U) :
    ∃ t ∈ Set.Icc U (U + 1),
      (∀ z ∈ conreyHorizontalJensenFactorZeroSupport Y R L U,
        conreyHorizontalJensenFactorHorizontalSeparation Y R L U ≤
          |t - z.im|) ∧
      ∀ x ∈ Set.Icc (conreyHorizontalLeftEdge R L)
          (conreyHorizontalRightEdge L),
        conreyHorizontalJensenProduct Y R L
          ((x : ℂ) + Complex.I * (t : ℂ)) ≠ 0 :=
  exists_conreyHorizontalJensenFactorAdmissibleHeight
    hY hR0 hRmax hL hU

#print axioms integral_abs_im_inv_horizontal_sub_le_pi
#print axioms abs_integral_weighted_im_inv_horizontal_sub_le
#print axioms conreyHorizontalJensenFactorHorizontalSeparation_lower_of_mass_le
#print axioms exists_conreyHorizontalJensenFactorAdmissibleHeight
