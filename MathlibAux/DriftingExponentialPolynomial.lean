import MathlibAux.DirichletPolynomialMeanSquare
import PrimeNumberTheorem.ZeroForcedOscillation

open Complex MeasureTheory Set
open scoped BigOperators Interval

namespace MathlibAux

noncomputable section

/-!
# Finite exponential polynomials with slowly drifting amplitudes

This module compares a finite oscillatory package with the package obtained
by allowing each coefficient to acquire a real exponential drift.  The main
estimate keeps three costs visible: diagonal energy, the ordered
off-diagonal frequency budget, and the loss caused by the real-part drift.
-/

/-- A finite exponential polynomial whose `i`-th coefficient is multiplied
by `exp (drift i * (t - base))`. -/
noncomputable def driftingExponentialPolynomial
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (coeff : ι → ℂ) (freq drift : ι → ℝ)
    (base t : ℝ) : ℂ :=
  ∑ i ∈ S,
    coeff i * (Real.exp (drift i * (t - base)) : ℂ) *
      Complex.exp (I * (freq i * t))

/-- The distinct frequencies in a finite package. -/
noncomputable def mergedFrequencySupport
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (freq : ι → ℝ) : Finset ℝ :=
  S.image freq

/-- The coefficient obtained after collecting every term with the same
frequency.  Cancellation at a repeated frequency is therefore recorded in
the coefficient rather than excluded by an injectivity hypothesis. -/
noncomputable def mergedFrequencyCoefficient
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    (u : ℝ) : ℂ :=
  ∑ i ∈ S with freq i = u, coeff i

/-- Collecting equal frequencies does not change the frozen exponential
polynomial. -/
theorem exponentialPolynomial_eq_mergedFrequencyPolynomial
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    exponentialPolynomial S coeff freq t =
      exponentialPolynomial (mergedFrequencySupport S freq)
        (mergedFrequencyCoefficient S coeff freq) id t := by
  classical
  have hmaps :
      ∀ i ∈ S, freq i ∈ mergedFrequencySupport S freq := by
    intro i hi
    exact Finset.mem_image_of_mem freq hi
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun i => coeff i * Complex.exp (I * (freq i * t)))
  rw [exponentialPolynomial, exponentialPolynomial]
  symm
  calc
    ∑ u ∈ mergedFrequencySupport S freq,
        mergedFrequencyCoefficient S coeff freq u *
          Complex.exp (I * (id u * t)) =
        ∑ u ∈ mergedFrequencySupport S freq,
          ∑ i ∈ S with freq i = u,
            coeff i * Complex.exp (I * (freq i * t)) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [mergedFrequencyCoefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hiu : freq i = u := (Finset.mem_filter.mp hi).2
      simp only [id_eq]
      rw [hiu]
    _ = ∑ i ∈ S,
        coeff i * Complex.exp (I * (freq i * t)) := hfiber

/-- On the forward half-line, a drift in `[-delta, 0]` differs from the
frozen coefficient by at most `1 - exp (-delta * (t - base))`. -/
theorem norm_driftingExponentialPolynomial_sub_exponentialPolynomial_le
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {coeff : ι → ℂ} {freq drift : ι → ℝ}
    {a delta t : ℝ}
    (hdelta : 0 ≤ delta)
    (hat : a ≤ t)
    (hdrift : ∀ i ∈ S, -delta ≤ drift i ∧ drift i ≤ 0) :
    ‖driftingExponentialPolynomial S coeff freq drift a t -
        exponentialPolynomial S coeff freq t‖ ≤
      (1 - Real.exp (-delta * (t - a))) *
        ∑ i ∈ S, ‖coeff i‖ := by
  classical
  let q : ℝ := 1 - Real.exp (-delta * (t - a))
  have hta : 0 ≤ t - a := sub_nonneg.mpr hat
  have hq : 0 ≤ q := by
    dsimp [q]
    exact sub_nonneg.mpr
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hdelta) hta))
  have hterm (i : ι) (hi : i ∈ S) :
      ‖coeff i * (Real.exp (drift i * (t - a)) : ℂ) *
            Complex.exp (I * (freq i * t)) -
          coeff i * Complex.exp (I * (freq i * t))‖ ≤
        q * ‖coeff i‖ := by
    have hdi := hdrift i hi
    have hduNonpos : drift i * (t - a) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hdi.2 hta
    have hduLower : -delta * (t - a) ≤ drift i * (t - a) :=
      mul_le_mul_of_nonneg_right hdi.1 hta
    have hexpLe : Real.exp (drift i * (t - a)) ≤ 1 :=
      Real.exp_le_one_iff.mpr hduNonpos
    have hexpLower :
        Real.exp (-delta * (t - a)) ≤
          Real.exp (drift i * (t - a)) :=
      Real.exp_le_exp.mpr hduLower
    have habs :
        |Real.exp (drift i * (t - a)) - 1| ≤ q := by
      rw [abs_of_nonpos (sub_nonpos.mpr hexpLe)]
      dsimp [q]
      linarith
    have hreal :
        ‖(Real.exp (drift i * (t - a)) : ℂ) - 1‖ =
          |Real.exp (drift i * (t - a)) - 1| := by
      rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    have hosc :
        ‖Complex.exp (I * (freq i * t))‖ = 1 := by
      rw [norm_exp]
      simp
    calc
      ‖coeff i * (Real.exp (drift i * (t - a)) : ℂ) *
            Complex.exp (I * (freq i * t)) -
          coeff i * Complex.exp (I * (freq i * t))‖ =
          ‖coeff i‖ *
            |Real.exp (drift i * (t - a)) - 1| := by
        rw [show
          coeff i * (Real.exp (drift i * (t - a)) : ℂ) *
                Complex.exp (I * (freq i * t)) -
              coeff i * Complex.exp (I * (freq i * t)) =
            coeff i *
              ((Real.exp (drift i * (t - a)) : ℂ) - 1) *
                Complex.exp (I * (freq i * t)) by ring]
        rw [norm_mul, norm_mul, hreal, hosc, mul_one]
      _ ≤ ‖coeff i‖ * q :=
        mul_le_mul_of_nonneg_left habs (norm_nonneg _)
      _ = q * ‖coeff i‖ := by ring
  rw [driftingExponentialPolynomial, exponentialPolynomial,
    ← Finset.sum_sub_distrib]
  calc
    ‖∑ i ∈ S,
        (coeff i * (Real.exp (drift i * (t - a)) : ℂ) *
            Complex.exp (I * (freq i * t)) -
          coeff i * Complex.exp (I * (freq i * t)))‖ ≤
        ∑ i ∈ S,
          ‖coeff i * (Real.exp (drift i * (t - a)) : ℂ) *
              Complex.exp (I * (freq i * t)) -
            coeff i * Complex.exp (I * (freq i * t))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ S, q * ‖coeff i‖ := by
      gcongr with i hi
      exact hterm i hi
    _ = q * ∑ i ∈ S, ‖coeff i‖ := by
      rw [Finset.mul_sum]
    _ = _ := rfl

private theorem integral_normSq_close_to_exponentialPolynomial_ge
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    (F : ℝ → ℂ) {a L R : ℝ}
    (hL : 0 ≤ L)
    (hF : Continuous F)
    (hfreq : Set.InjOn freq ↑S)
    (hclose :
      ∀ t ∈ Icc a (a + L),
        ‖F t - exponentialPolynomial S coeff freq t‖ ≤ R) :
    (1 / 2 : ℝ) *
          (L * ∑ i ∈ S, ‖coeff i‖ ^ 2 -
            PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
              S coeff freq) -
        L * R ^ 2 ≤
      ∫ t in a..(a + L), ‖F t‖ ^ 2 := by
  let P : ℝ → ℂ := fun t => exponentialPolynomial S coeff freq t
  let E : ℝ → ℂ := fun t => F t - P t
  have hab : a ≤ a + L := le_add_of_nonneg_right hL
  have hP : Continuous P := by
    dsimp [P, exponentialPolynomial]
    fun_prop
  have hE : Continuous E := hF.sub hP
  have hPInt :
      IntervalIntegrable (fun t => ‖P t‖ ^ 2) volume a (a + L) :=
    (by fun_prop : Continuous fun t => ‖P t‖ ^ 2).intervalIntegrable
      a (a + L)
  have hFInt :
      IntervalIntegrable (fun t => ‖F t‖ ^ 2) volume a (a + L) :=
    (by fun_prop : Continuous fun t => ‖F t‖ ^ 2).intervalIntegrable
      a (a + L)
  have hEInt :
      IntervalIntegrable (fun t => ‖E t‖ ^ 2) volume a (a + L) :=
    (by fun_prop : Continuous fun t => ‖E t‖ ^ 2).intervalIntegrable
      a (a + L)
  have hPLower :
      L * (∑ i ∈ S, ‖coeff i‖ ^ 2) -
          PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
            S coeff freq ≤
        ∫ t in a..(a + L), ‖P t‖ ^ 2 := by
    have hbase :=
      PrimeNumberTheorem.ZeroForcedOscillation.abs_intervalIntegral_sqNorm_exponentialPolynomial_sub_diagonal_le
        S coeff freq (a := a) (b := a + L) hfreq
    have hlower := (abs_le.mp hbase).1
    dsimp [P] at hlower ⊢
    simp only [add_sub_cancel_left,
      PrimeNumberTheorem.ZeroForcedOscillation.exponentialPolynomial,
      exponentialPolynomial] at hlower ⊢
    linarith
  have hEPoint (t : ℝ) (ht : t ∈ Icc a (a + L)) :
      ‖E t‖ ^ 2 ≤ R ^ 2 := by
    have hnorm : ‖E t‖ ≤ R := by
      dsimp [E, P]
      exact hclose t ht
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hEUpper :
      (∫ t in a..(a + L), ‖E t‖ ^ 2) ≤ L * R ^ 2 := by
    have hconstInt :
        IntervalIntegrable (fun _t : ℝ => R ^ 2)
          volume a (a + L) :=
      Continuous.intervalIntegrable continuous_const a (a + L)
    calc
      (∫ t in a..(a + L), ‖E t‖ ^ 2) ≤
          ∫ _t in a..(a + L), R ^ 2 :=
        intervalIntegral.integral_mono_on hab hEInt hconstInt hEPoint
      _ = L * R ^ 2 := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  have htransferPoint (t : ℝ) :
      (1 / 2 : ℝ) * ‖P t‖ ^ 2 - ‖E t‖ ^ 2 ≤ ‖F t‖ ^ 2 := by
    have htriangle : ‖P t‖ ≤ ‖F t‖ + ‖E t‖ := by
      calc
        ‖P t‖ = ‖F t - E t‖ := by
          congr 1
          dsimp [E]
          abel
        _ ≤ ‖F t‖ + ‖E t‖ := norm_sub_le _ _
    have hsquare :
        ‖P t‖ ^ 2 ≤ (‖F t‖ + ‖E t‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    nlinarith [hsquare, sq_nonneg (‖F t‖ - ‖E t‖)]
  have htransfer :
      (1 / 2 : ℝ) * (∫ t in a..(a + L), ‖P t‖ ^ 2) -
          (∫ t in a..(a + L), ‖E t‖ ^ 2) ≤
        ∫ t in a..(a + L), ‖F t‖ ^ 2 := by
    have hleftInt :
        IntervalIntegrable
          (fun t => (1 / 2 : ℝ) * ‖P t‖ ^ 2 - ‖E t‖ ^ 2)
          volume a (a + L) :=
      (hPInt.const_mul (1 / 2 : ℝ)).sub hEInt
    have hmono :
        (∫ t in a..(a + L),
            ((1 / 2 : ℝ) * ‖P t‖ ^ 2 - ‖E t‖ ^ 2)) ≤
          ∫ t in a..(a + L), ‖F t‖ ^ 2 :=
      intervalIntegral.integral_mono_on hab hleftInt hFInt
        (fun t _ht => htransferPoint t)
    rw [intervalIntegral.integral_sub
        (hPInt.const_mul (1 / 2 : ℝ)) hEInt,
      intervalIntegral.integral_const_mul] at hmono
    exact hmono
  have hscaled :
      (1 / 2 : ℝ) *
          (L * (∑ i ∈ S, ‖coeff i‖ ^ 2) -
            PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
              S coeff freq) ≤
        (1 / 2 : ℝ) *
          (∫ t in a..(a + L), ‖P t‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hPLower (by norm_num)
  linarith

/-- A finite package with real-part drift in `[-delta, 0]` retains at least
half of the frozen diagonal-minus-off-diagonal energy, up to the explicit
drift loss.  No frequency-spacing lower bound is hidden in the statement:
all spectral interaction remains in `offDiagonalBound`. -/
theorem integral_normSq_driftingExponentialPolynomial_ge
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {coeff : ι → ℂ} {freq drift : ι → ℝ}
    {a L delta : ℝ}
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hdrift : ∀ i ∈ S, -delta ≤ drift i ∧ drift i ≤ 0)
    (hfreq : Set.InjOn freq ↑S) :
    (1 / 2 : ℝ) *
          (L * ∑ i ∈ S, ‖coeff i‖ ^ 2 -
            PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
              S coeff freq) -
        L * (1 - Real.exp (-delta * L)) ^ 2 *
          (∑ i ∈ S, ‖coeff i‖) ^ 2 ≤
      ∫ t in a..(a + L),
        ‖driftingExponentialPolynomial S coeff freq drift a t‖ ^ 2 := by
  classical
  let frozen : ℝ → ℂ := fun t =>
    exponentialPolynomial S coeff freq t
  let moving : ℝ → ℂ := fun t =>
    driftingExponentialPolynomial S coeff freq drift a t
  let error : ℝ → ℂ := fun t => moving t - frozen t
  let energy : ℝ := ∑ i ∈ S, ‖coeff i‖ ^ 2
  let mass : ℝ := ∑ i ∈ S, ‖coeff i‖
  let offDiagonal : ℝ :=
    PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound S coeff freq
  let q : ℝ := 1 - Real.exp (-delta * L)
  have hab : a ≤ a + L := le_add_of_nonneg_right hL
  have hq : 0 ≤ q := by
    dsimp [q]
    apply sub_nonneg.mpr
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hdelta) hL)
  have hmass : 0 ≤ mass := by
    dsimp [mass]
    positivity
  have hfrozenContinuous : Continuous frozen := by
    dsimp [frozen, exponentialPolynomial]
    fun_prop
  have hmovingContinuous : Continuous moving := by
    dsimp [moving, driftingExponentialPolynomial]
    fun_prop
  have herrorContinuous : Continuous error :=
    hmovingContinuous.sub hfrozenContinuous
  have hfrozenInt :
      IntervalIntegrable (fun t => ‖frozen t‖ ^ 2) volume a (a + L) :=
    (by fun_prop : Continuous fun t => ‖frozen t‖ ^ 2).intervalIntegrable
      a (a + L)
  have hmovingInt :
      IntervalIntegrable (fun t => ‖moving t‖ ^ 2) volume a (a + L) :=
    (by fun_prop : Continuous fun t => ‖moving t‖ ^ 2).intervalIntegrable
      a (a + L)
  have herrorInt :
      IntervalIntegrable (fun t => ‖error t‖ ^ 2) volume a (a + L) :=
    (by fun_prop : Continuous fun t => ‖error t‖ ^ 2).intervalIntegrable
      a (a + L)
  have hfrozenLower :
      L * energy - offDiagonal ≤
        ∫ t in a..(a + L), ‖frozen t‖ ^ 2 := by
    have hbase :=
      PrimeNumberTheorem.ZeroForcedOscillation.abs_intervalIntegral_sqNorm_exponentialPolynomial_sub_diagonal_le
        S coeff freq (a := a) (b := a + L) hfreq
    have hlower := (abs_le.mp hbase).1
    dsimp [frozen, energy, offDiagonal] at hlower ⊢
    simp only [add_sub_cancel_left,
      PrimeNumberTheorem.ZeroForcedOscillation.exponentialPolynomial,
      exponentialPolynomial] at hlower ⊢
    linarith
  have herrorPoint (t : ℝ) (ht : t ∈ Icc a (a + L)) :
      ‖error t‖ ^ 2 ≤ q ^ 2 * mass ^ 2 := by
    have hta : a ≤ t := ht.1
    have hlength : t - a ≤ L := by linarith [ht.2]
    have hqt :
        1 - Real.exp (-delta * (t - a)) ≤ q := by
      have hexp :
          Real.exp (-delta * L) ≤
            Real.exp (-delta * (t - a)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left hlength (neg_nonpos.mpr hdelta)
      dsimp [q]
      linarith
    have hpoint :=
      norm_driftingExponentialPolynomial_sub_exponentialPolynomial_le
        (S := S) (coeff := coeff) (freq := freq) (drift := drift)
        (a := a) (delta := delta) (t := t) hdelta hta hdrift
    have hnorm : ‖error t‖ ≤ q * mass := by
      dsimp [error, moving, frozen, mass]
      exact hpoint.trans
        (mul_le_mul_of_nonneg_right hqt (by positivity))
    have hsquare :
        ‖error t‖ ^ 2 ≤ (q * mass) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith
  have herrorUpper :
      (∫ t in a..(a + L), ‖error t‖ ^ 2) ≤
        L * q ^ 2 * mass ^ 2 := by
    have hconstInt :
        IntervalIntegrable (fun _t : ℝ => q ^ 2 * mass ^ 2)
          volume a (a + L) :=
      Continuous.intervalIntegrable continuous_const a (a + L)
    calc
      (∫ t in a..(a + L), ‖error t‖ ^ 2) ≤
          ∫ _t in a..(a + L), q ^ 2 * mass ^ 2 :=
        intervalIntegral.integral_mono_on hab herrorInt hconstInt herrorPoint
      _ = L * q ^ 2 * mass ^ 2 := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  have htransferPoint (t : ℝ) :
      (1 / 2 : ℝ) * ‖frozen t‖ ^ 2 - ‖error t‖ ^ 2 ≤
        ‖moving t‖ ^ 2 := by
    have htriangle : ‖frozen t‖ ≤ ‖moving t‖ + ‖error t‖ := by
      calc
        ‖frozen t‖ = ‖moving t - error t‖ := by
          congr 1
          dsimp [error]
          abel
        _ ≤ ‖moving t‖ + ‖error t‖ := norm_sub_le _ _
    have hsquare :
        ‖frozen t‖ ^ 2 ≤ (‖moving t‖ + ‖error t‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    nlinarith [hsquare, sq_nonneg (‖moving t‖ - ‖error t‖)]
  have htransfer :
      (1 / 2 : ℝ) *
            (∫ t in a..(a + L), ‖frozen t‖ ^ 2) -
          (∫ t in a..(a + L), ‖error t‖ ^ 2) ≤
        ∫ t in a..(a + L), ‖moving t‖ ^ 2 := by
    have hleftInt :
        IntervalIntegrable
          (fun t =>
            (1 / 2 : ℝ) * ‖frozen t‖ ^ 2 - ‖error t‖ ^ 2)
          volume a (a + L) :=
      (hfrozenInt.const_mul (1 / 2 : ℝ)).sub herrorInt
    have hmono :
        (∫ t in a..(a + L),
            ((1 / 2 : ℝ) * ‖frozen t‖ ^ 2 - ‖error t‖ ^ 2)) ≤
          ∫ t in a..(a + L), ‖moving t‖ ^ 2 :=
      intervalIntegral.integral_mono_on hab hleftInt hmovingInt
        (fun t _ht => htransferPoint t)
    rw [intervalIntegral.integral_sub
        (hfrozenInt.const_mul (1 / 2 : ℝ)) herrorInt,
      intervalIntegral.integral_const_mul] at hmono
    exact hmono
  have hscaled :
      (1 / 2 : ℝ) * (L * energy - offDiagonal) ≤
        (1 / 2 : ℝ) *
          (∫ t in a..(a + L), ‖frozen t‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hfrozenLower (by norm_num)
  have hcombined :
      (1 / 2 : ℝ) * (L * energy - offDiagonal) -
          L * q ^ 2 * mass ^ 2 ≤
        ∫ t in a..(a + L), ‖moving t‖ ^ 2 := by
    linarith
  simpa [energy, offDiagonal, q, mass, moving] using hcombined

/-- Collision-safe form of the drifting-package lower bound. Equal
frequencies are first merged, so cancellation at one frequency lowers the
displayed diagonal energy instead of invalidating a hidden injectivity
assumption. -/
theorem integral_normSq_driftingExponentialPolynomial_ge_merged
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {coeff : ι → ℂ} {freq drift : ι → ℝ}
    {a L delta : ℝ}
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hdrift : ∀ i ∈ S, -delta ≤ drift i ∧ drift i ≤ 0) :
    (1 / 2 : ℝ) *
          (L *
              ∑ u ∈ mergedFrequencySupport S freq,
                ‖mergedFrequencyCoefficient S coeff freq u‖ ^ 2 -
            PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
              (mergedFrequencySupport S freq)
              (mergedFrequencyCoefficient S coeff freq) id) -
        L * (1 - Real.exp (-delta * L)) ^ 2 *
          (∑ i ∈ S, ‖coeff i‖) ^ 2 ≤
      ∫ t in a..(a + L),
        ‖driftingExponentialPolynomial S coeff freq drift a t‖ ^ 2 := by
  classical
  let U : Finset ℝ := mergedFrequencySupport S freq
  let d : ℝ → ℂ := mergedFrequencyCoefficient S coeff freq
  let F : ℝ → ℂ := fun t =>
    driftingExponentialPolynomial S coeff freq drift a t
  let q : ℝ := 1 - Real.exp (-delta * L)
  let mass : ℝ := ∑ i ∈ S, ‖coeff i‖
  let R : ℝ := q * mass
  have hq : 0 ≤ q := by
    dsimp [q]
    apply sub_nonneg.mpr
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hdelta) hL)
  have hmass : 0 ≤ mass := by
    dsimp [mass]
    positivity
  have hF : Continuous F := by
    dsimp [F, driftingExponentialPolynomial]
    fun_prop
  have hfreq : Set.InjOn id (U : Set ℝ) := by
    intro u hu v hv huv
    exact huv
  have hclose :
      ∀ t ∈ Icc a (a + L),
        ‖F t - exponentialPolynomial U d id t‖ ≤ R := by
    intro t ht
    have hpoint :=
      norm_driftingExponentialPolynomial_sub_exponentialPolynomial_le
        (S := S) (coeff := coeff) (freq := freq) (drift := drift)
        (a := a) (delta := delta) (t := t)
        hdelta ht.1 hdrift
    have hrewrite :=
      exponentialPolynomial_eq_mergedFrequencyPolynomial
        S coeff freq t
    have hlength : t - a ≤ L := by
      linarith [ht.2]
    have hqt :
        1 - Real.exp (-delta * (t - a)) ≤ q := by
      have hexp :
          Real.exp (-delta * L) ≤
            Real.exp (-delta * (t - a)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left hlength (neg_nonpos.mpr hdelta)
      dsimp [q]
      linarith
    dsimp [F, U, d, R, q, mass]
    rw [← hrewrite]
    exact hpoint.trans
      (mul_le_mul_of_nonneg_right hqt (by positivity))
  have hbase :=
    integral_normSq_close_to_exponentialPolynomial_ge
      U d id F hL hF hfreq hclose
  calc
    (1 / 2 : ℝ) *
          (L *
              ∑ u ∈ mergedFrequencySupport S freq,
                ‖mergedFrequencyCoefficient S coeff freq u‖ ^ 2 -
            PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
              (mergedFrequencySupport S freq)
              (mergedFrequencyCoefficient S coeff freq) id) -
        L * (1 - Real.exp (-delta * L)) ^ 2 *
          (∑ i ∈ S, ‖coeff i‖) ^ 2 =
        (1 / 2 : ℝ) *
          (L * ∑ u ∈ U, ‖d u‖ ^ 2 -
            PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
              U d id) -
          L * R ^ 2 := by
      dsimp [U, d, R, q, mass]
      ring
    _ ≤ ∫ t in a..(a + L), ‖F t‖ ^ 2 := hbase
    _ = ∫ t in a..(a + L),
        ‖driftingExponentialPolynomial S coeff freq drift a t‖ ^ 2 := by
      rfl

/-- Collision-safe coercivity gate obtained from the merged-frequency lower
bound. -/
theorem integral_normSq_driftingExponentialPolynomial_pos_merged
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {coeff : ι → ℂ} {freq drift : ι → ℝ}
    {a L delta : ℝ}
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hdrift : ∀ i ∈ S, -delta ≤ drift i ∧ drift i ≤ 0)
    (hcoercive :
      PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
            (mergedFrequencySupport S freq)
            (mergedFrequencyCoefficient S coeff freq) id +
          2 * L * (1 - Real.exp (-delta * L)) ^ 2 *
            (∑ i ∈ S, ‖coeff i‖) ^ 2 <
        L *
          ∑ u ∈ mergedFrequencySupport S freq,
            ‖mergedFrequencyCoefficient S coeff freq u‖ ^ 2) :
    0 <
      ∫ t in a..(a + L),
        ‖driftingExponentialPolynomial S coeff freq drift a t‖ ^ 2 := by
  have hbase :=
    integral_normSq_driftingExponentialPolynomial_ge_merged
      (S := S) (coeff := coeff) (freq := freq) (drift := drift)
      (a := a) (L := L) (delta := delta)
      hL hdelta hdrift
  linarith

/-- Concrete coercivity gate.  If the frozen off-diagonal interaction plus
twice the drift loss is smaller than the diagonal energy, then the drifting
package has strictly positive local second moment. -/
theorem integral_normSq_driftingExponentialPolynomial_pos
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {coeff : ι → ℂ} {freq drift : ι → ℝ}
    {a L delta : ℝ}
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hdrift : ∀ i ∈ S, -delta ≤ drift i ∧ drift i ≤ 0)
    (hfreq : Set.InjOn freq ↑S)
    (hcoercive :
      PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
            S coeff freq +
          2 * L * (1 - Real.exp (-delta * L)) ^ 2 *
            (∑ i ∈ S, ‖coeff i‖) ^ 2 <
        L * ∑ i ∈ S, ‖coeff i‖ ^ 2) :
    0 <
      ∫ t in a..(a + L),
        ‖driftingExponentialPolynomial S coeff freq drift a t‖ ^ 2 := by
  have hbase :=
    integral_normSq_driftingExponentialPolynomial_ge
      (S := S) (coeff := coeff) (freq := freq) (drift := drift)
      (a := a) (L := L) (delta := delta)
      hL hdelta hdrift hfreq
  linarith

end

end MathlibAux
