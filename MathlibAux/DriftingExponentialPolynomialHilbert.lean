import MathlibAux.DriftingExponentialPolynomial
import PrimeNumberTheorem.CarneiroLittmannProfile

open Complex MeasureTheory Set
open scoped BigOperators Interval

namespace MathlibAux

noncomputable section

open PrimeNumberTheorem.DirichletPolynomial

/-!
# Local-separation Hilbert bounds for drifting exponential polynomials

The frozen finite exponential polynomial is controlled by the
Carneiro--Littmann local-separation Hilbert inequality.  Comparing a drifting
polynomial to that frozen polynomial then gives a collision-safe local `L2`
lower bound whose spectral loss is the actual weighted local-separation
energy.
-/

/-- The coefficient energy weighted by reciprocal local frequency
separation.  This is the exact loss in the local-separation Hilbert bound. -/
noncomputable def exponentialPolynomialLocalSeparationEnergy
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) : ℝ :=
  ∑ i ∈ S,
    ‖coeff i‖ ^ 2 /
      localFrequencySeparation S freq i

private theorem
    abs_finiteExponentialMeanSquare_sub_diagonal_le_localSeparation
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {coeff : ι → ℂ} {freq : ι → ℝ} {a b : ℝ}
    (hS : S.Nontrivial) (hfreq : Set.InjOn freq (S : Set ι)) :
    |(∫ t in a..b, ‖finiteExponentialSum S coeff freq t‖ ^ 2) -
        (b - a) * ∑ i ∈ S, ‖coeff i‖ ^ 2| ≤
      4 * Real.pi *
        exponentialPolynomialLocalSeparationEnergy S coeff freq := by
  let lhs : ℝ :=
    (∫ t in a..b, ‖finiteExponentialSum S coeff freq t‖ ^ 2) -
      (b - a) * ∑ i ∈ S, ‖coeff i‖ ^ 2
  let weighted : ℝ :=
    exponentialPolynomialLocalSeparationEnergy S coeff freq
  have hexact :=
    finiteExponentialMeanSquare_cast_eq_diagonal_add_hilbert
      (S := S) (c := coeff) (omega := freq) (a := a) (b := b) hfreq
  have hcast :
      (lhs : ℂ) =
        -I *
          (hilbertForm S (phaseTwist coeff freq b) freq -
            hilbertForm S (phaseTwist coeff freq a) freq) := by
    dsimp [lhs]
    rw [ofReal_sub]
    push_cast
    rw [hexact]
    ring
  have hphase (t : ℝ) :
      exponentialPolynomialLocalSeparationEnergy
          S (phaseTwist coeff freq t) freq =
        weighted := by
    dsimp [exponentialPolynomialLocalSeparationEnergy, weighted]
    apply Finset.sum_congr rfl
    intro i hi
    simp [phaseTwist, Complex.norm_exp]
  have hb :=
    hilbertForm_norm_le_two_pi_localSeparation_carneiroLittmann
      S (phaseTwist coeff freq b) freq hS hfreq
  have ha :=
    hilbertForm_norm_le_two_pi_localSeparation_carneiroLittmann
      S (phaseTwist coeff freq a) freq hS hfreq
  change
    ‖hilbertForm S (phaseTwist coeff freq b) freq‖ ≤
      2 * Real.pi *
        exponentialPolynomialLocalSeparationEnergy
          S (phaseTwist coeff freq b) freq at hb
  change
    ‖hilbertForm S (phaseTwist coeff freq a) freq‖ ≤
      2 * Real.pi *
        exponentialPolynomialLocalSeparationEnergy
          S (phaseTwist coeff freq a) freq at ha
  rw [hphase] at hb ha
  change |lhs| ≤ 4 * Real.pi * weighted
  calc
    |lhs| = ‖(lhs : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖-I *
        (hilbertForm S (phaseTwist coeff freq b) freq -
          hilbertForm S (phaseTwist coeff freq a) freq)‖ :=
      congrArg norm hcast
    _ = ‖hilbertForm S (phaseTwist coeff freq b) freq -
          hilbertForm S (phaseTwist coeff freq a) freq‖ := by
      rw [norm_mul, norm_neg, norm_I, one_mul]
    _ ≤ ‖hilbertForm S (phaseTwist coeff freq b) freq‖ +
          ‖hilbertForm S (phaseTwist coeff freq a) freq‖ :=
      norm_sub_le _ _
    _ ≤ 4 * Real.pi * weighted := by linarith

/-- The frozen exponential-polynomial mean square differs from its diagonal
energy by at most the concrete `4 * pi` local-separation Hilbert loss. -/
theorem
    abs_intervalIntegral_normSq_exponentialPolynomial_sub_diagonal_le_localSeparation
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {coeff : ι → ℂ} {freq : ι → ℝ} {a b : ℝ}
    (hS : S.Nontrivial) (hfreq : Set.InjOn freq (S : Set ι)) :
    |(∫ t in a..b, ‖exponentialPolynomial S coeff freq t‖ ^ 2) -
        (b - a) * ∑ i ∈ S, ‖coeff i‖ ^ 2| ≤
      4 * Real.pi *
        exponentialPolynomialLocalSeparationEnergy S coeff freq := by
  simpa [exponentialPolynomial, finiteExponentialSum] using
    (abs_finiteExponentialMeanSquare_sub_diagonal_le_localSeparation
      (S := S) (coeff := coeff) (freq := freq) (a := a) (b := b)
      hS hfreq)

/-- After equal frequencies are merged, a drifting exponential polynomial
retains half of the frozen diagonal-minus-Hilbert energy, up to the explicit
drift loss. -/
theorem
    integral_normSq_driftingExponentialPolynomial_ge_merged_localSeparation
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {coeff : ι → ℂ} {freq drift : ι → ℝ}
    {a L delta : ℝ}
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hdrift : ∀ i ∈ S, -delta ≤ drift i ∧ drift i ≤ 0)
    (hsupport : (mergedFrequencySupport S freq).Nontrivial) :
    (1 / 2 : ℝ) *
          (L *
              ∑ u ∈ mergedFrequencySupport S freq,
                ‖mergedFrequencyCoefficient S coeff freq u‖ ^ 2 -
            4 * Real.pi *
              exponentialPolynomialLocalSeparationEnergy
                (mergedFrequencySupport S freq)
                (mergedFrequencyCoefficient S coeff freq) id) -
        L * (1 - Real.exp (-delta * L)) ^ 2 *
          (∑ i ∈ S, ‖coeff i‖) ^ 2 ≤
      ∫ t in a..(a + L),
        ‖driftingExponentialPolynomial S coeff freq drift a t‖ ^ 2 := by
  classical
  let U : Finset ℝ := mergedFrequencySupport S freq
  let d : ℝ → ℂ := mergedFrequencyCoefficient S coeff freq
  let frozen : ℝ → ℂ := fun t => exponentialPolynomial U d id t
  let moving : ℝ → ℂ := fun t =>
    driftingExponentialPolynomial S coeff freq drift a t
  let error : ℝ → ℂ := fun t => moving t - frozen t
  let energy : ℝ := ∑ u ∈ U, ‖d u‖ ^ 2
  let weighted : ℝ :=
    exponentialPolynomialLocalSeparationEnergy U d id
  let mass : ℝ := ∑ i ∈ S, ‖coeff i‖
  let q : ℝ := 1 - Real.exp (-delta * L)
  have hab : a ≤ a + L := le_add_of_nonneg_right hL
  have hq : 0 ≤ q := by
    dsimp [q]
    exact sub_nonneg.mpr
      (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hdelta) hL))
  have hmass : 0 ≤ mass := by
    dsimp [mass]
    positivity
  have hfreqU : Set.InjOn id (U : Set ℝ) := by
    intro u hu v hv huv
    exact huv
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
    (by fun_prop : Continuous fun t => ‖frozen t‖ ^ 2)
      |>.intervalIntegrable a (a + L)
  have hmovingInt :
      IntervalIntegrable (fun t => ‖moving t‖ ^ 2) volume a (a + L) :=
    (by fun_prop : Continuous fun t => ‖moving t‖ ^ 2)
      |>.intervalIntegrable a (a + L)
  have herrorInt :
      IntervalIntegrable (fun t => ‖error t‖ ^ 2) volume a (a + L) :=
    (by fun_prop : Continuous fun t => ‖error t‖ ^ 2)
      |>.intervalIntegrable a (a + L)
  have hfrozenLower :
      L * energy - 4 * Real.pi * weighted ≤
        ∫ t in a..(a + L), ‖frozen t‖ ^ 2 := by
    have hmean :=
      abs_intervalIntegral_normSq_exponentialPolynomial_sub_diagonal_le_localSeparation
        (S := U) (coeff := d) (freq := id)
        (a := a) (b := a + L) hsupport hfreqU
    have hlower := (abs_le.mp hmean).1
    dsimp [frozen, energy, weighted] at hlower ⊢
    simp only [add_sub_cancel_left] at hlower
    linarith
  have hclose (t : ℝ) (ht : t ∈ Icc a (a + L)) :
      ‖error t‖ ≤ q * mass := by
    have hpoint :=
      norm_driftingExponentialPolynomial_sub_exponentialPolynomial_le
        (S := S) (coeff := coeff) (freq := freq) (drift := drift)
        (a := a) (delta := delta) (t := t)
        hdelta ht.1 hdrift
    have hrewrite :=
      exponentialPolynomial_eq_mergedFrequencyPolynomial
        S coeff freq t
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
    dsimp [error, moving, frozen, U, d]
    rw [← hrewrite]
    exact hpoint.trans
      (mul_le_mul_of_nonneg_right hqt (by positivity))
  have herrorUpper :
      (∫ t in a..(a + L), ‖error t‖ ^ 2) ≤
        L * q ^ 2 * mass ^ 2 := by
    have hpoint (t : ℝ) (ht : t ∈ Icc a (a + L)) :
        ‖error t‖ ^ 2 ≤ q ^ 2 * mass ^ 2 := by
      have hnorm := hclose t ht
      have hnonneg : 0 ≤ q * mass := mul_nonneg hq hmass
      have hsquare :=
        pow_le_pow_left₀ (norm_nonneg (error t)) hnorm 2
      nlinarith
    have hconstInt :
        IntervalIntegrable (fun _t : ℝ => q ^ 2 * mass ^ 2)
          volume a (a + L) :=
      Continuous.intervalIntegrable continuous_const a (a + L)
    calc
      (∫ t in a..(a + L), ‖error t‖ ^ 2) ≤
          ∫ _t in a..(a + L), q ^ 2 * mass ^ 2 :=
        intervalIntegral.integral_mono_on hab herrorInt hconstInt hpoint
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
      (1 / 2 : ℝ) * (∫ t in a..(a + L), ‖frozen t‖ ^ 2) -
          (∫ t in a..(a + L), ‖error t‖ ^ 2) ≤
        ∫ t in a..(a + L), ‖moving t‖ ^ 2 := by
    have hleftInt :
        IntervalIntegrable
          (fun t => (1 / 2 : ℝ) * ‖frozen t‖ ^ 2 - ‖error t‖ ^ 2)
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
      (1 / 2 : ℝ) * (L * energy - 4 * Real.pi * weighted) ≤
        (1 / 2 : ℝ) *
          (∫ t in a..(a + L), ‖frozen t‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hfrozenLower (by norm_num)
  have hcombined :
      (1 / 2 : ℝ) * (L * energy - 4 * Real.pi * weighted) -
          L * q ^ 2 * mass ^ 2 ≤
        ∫ t in a..(a + L), ‖moving t‖ ^ 2 := by
    linarith
  simpa [U, d, energy, weighted, mass, q, moving] using hcombined

end

end MathlibAux
