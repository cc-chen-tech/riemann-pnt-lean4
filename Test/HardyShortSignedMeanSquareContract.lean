import HardyTheorem.HardyShortSignedMeanSquare

open Complex Set

#check MathlibAux.shortExponentialCoefficient
#check MathlibAux.intervalIntegral_exponentialPolynomial_eq_exponentialPolynomial
#check MathlibAux.integral_normSq_intervalIntegral_exponentialPolynomial_le
#check HardyTheorem.hardyFirstModel
#check HardyTheorem.hardyFirstModelShortIntegral
#check HardyTheorem.hardyFirstModelShortIntegral_eq_re_sum_hardyPhaseShortIntegral
#check HardyTheorem.exists_abs_hardyShortIntegral_sub_hardyFirstModelShortIntegral_le
#print axioms MathlibAux.integral_normSq_intervalIntegral_exponentialPolynomial_le
#print axioms HardyTheorem.hardyFirstModelShortIntegral_eq_re_sum_hardyPhaseShortIntegral
#print axioms HardyTheorem.exists_abs_hardyShortIntegral_sub_hardyFirstModelShortIntegral_le

example {ι : Type*} (delta : ℝ) (coeff : ι → ℂ) (freq : ι → ℝ) (n : ι) :
    MathlibAux.shortExponentialCoefficient delta coeff freq n =
      coeff n * ∫ v in 0..delta, Complex.exp (Complex.I * (freq n * v)) :=
  rfl

example (kappa T t : ℝ) :
    HardyTheorem.hardyFirstModel kappa T t =
      (Complex.exp (Complex.I * kappa) *
        (∑ n ∈ Finset.Icc 1 (HardyTheorem.firstZetaApproximationCutoff T),
          ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
            Complex.exp
              (Complex.I * HardyTheorem.OscillatoryIntegral.hardyPhase n t))).re :=
  rfl

example {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    {a b delta : ℝ}
    (hfreq : ∀ m ∈ s, ∀ n ∈ s, m ≠ n → freq m ≠ freq n) :
    (∫ t in a..b,
        Complex.normSq
          (∫ u in t..t + delta,
            MathlibAux.exponentialPolynomial s coeff freq u)) ≤
      ∑ m ∈ s, ∑ n ∈ s,
        if m = n then
          (b - a) * Complex.normSq
            (MathlibAux.shortExponentialCoefficient delta coeff freq n)
        else
          2 * ‖MathlibAux.shortExponentialCoefficient delta coeff freq m‖ *
              ‖MathlibAux.shortExponentialCoefficient delta coeff freq n‖ /
            |freq m - freq n| :=
  MathlibAux.integral_normSq_intervalIntegral_exponentialPolynomial_le
    s coeff freq hfreq

example :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ T delta t : ℝ, T0 ≤ T → 0 ≤ delta →
        t ∈ Icc T (2 * T - delta) →
          |HardyTheorem.hardyShortIntegral delta t -
              HardyTheorem.hardyFirstModelShortIntegral kappa T delta t| ≤
            C * delta / Real.sqrt T :=
  HardyTheorem.exists_abs_hardyShortIntegral_sub_hardyFirstModelShortIntegral_le
