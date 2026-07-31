import HardyTheorem.SelbergSqrtZetaSignedRationalLocalSeparation
import HardyTheorem.SelbergSqrtZetaSignedRationalShortKernelPhase

/-!
# Local-separation bound for the complete fixed-shift short kernel

At fixed window shifts, the complete rational-frequency double sum is a
unit-modulus theta factor times a shifted exponential-polynomial
correlation.  Bounding the correlation by its two square means preserves the
Montgomery--Vaughan cancellation already present in the full frequency sum;
no pairwise absolute reciprocal-gap sum is introduced.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- The complete rational-frequency phase sum at fixed window shifts. -/
noncomputable def selbergSqrtZetaSignedRationalFixedShiftPhaseSum
    (N X : ℕ) (v w t : ℝ) : ℂ :=
  ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
    ∑ r ∈ selbergSqrtZetaSignedRationalSupport N X,
      (starRingEnd ℂ) (selbergSqrtZetaSignedRationalCoeff N X r) *
        selbergSqrtZetaSignedRationalCoeff N X q *
        Complex.exp
          (Complex.I *
            ((selbergSqrtZetaSignedRationalShortKernelPhase
              q r v w t : ℝ) : ℂ))

/-- A fixed-shift complete short-kernel section is bounded by the actual
local-separation weighted coefficient energy.  The estimate treats the
frequency double sum as one Hermitian object rather than summing one-pair
bounds. -/
theorem
    norm_integral_selbergSqrtZetaSignedRationalFixedShiftPhaseSum_le_localSeparation
    (N X : ℕ) {T H v w : ℝ}
    (_hT : 0 < T) (_hH : 0 ≤ H) (hroom : H ≤ T)
    (_hv : v ∈ Icc (0 : ℝ) H) (_hw : w ∈ Icc (0 : ℝ) H)
    (hQ : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial) :
    ‖∫ t in T..2 * T - H,
        selbergSqrtZetaSignedRationalFixedShiftPhaseSum N X v w t‖ ≤
      (T - H) *
          ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
            Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff N X q) +
        4 * Real.pi *
          ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
            Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff N X q) /
              PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                (selbergSqrtZetaSignedRationalSupport N X)
                selbergSqrtZetaSignedRationalFrequency q := by
  classical
  let Q : Finset ℚ := selbergSqrtZetaSignedRationalSupport N X
  let c : ℚ → ℂ := selbergSqrtZetaSignedRationalCoeff N X
  let omega : ℚ → ℝ := selbergSqrtZetaSignedRationalFrequency
  let P : ℝ → ℂ :=
    selbergSqrtZetaSignedRationalCollectedPolynomial N X
  let B : ℝ :=
    (T - H) * ∑ q ∈ Q, Complex.normSq (c q) +
      4 * Real.pi *
        ∑ q ∈ Q,
          Complex.normSq (c q) /
            PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
              Q omega q
  have hlong : T ≤ 2 * T - H := by linarith
  have hP : Continuous P := by
    dsimp only [P]
    unfold selbergSqrtZetaSignedRationalCollectedPolynomial
      MathlibAux.exponentialPolynomial
    fun_prop
  have hfactor (t : ℝ) :
      selbergSqrtZetaSignedRationalFixedShiftPhaseSum N X v w t =
        Complex.exp
            (Complex.I *
              (((thetaModel (t + w) - thetaModel (t + v) : ℝ)) : ℂ)) *
          (P (t + w) * (starRingEnd ℂ) (P (t + v))) := by
    dsimp only [P, selbergSqrtZetaSignedRationalCollectedPolynomial]
    rw [MathlibAux.exponentialPolynomial_mul_conj_shift_eq_double_sum]
    unfold selbergSqrtZetaSignedRationalFixedShiftPhaseSum
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    have hphase :
        Complex.I *
            ((selbergSqrtZetaSignedRationalShortKernelPhase
              q r v w t : ℝ) : ℂ) =
          Complex.I *
              (((thetaModel (t + w) - thetaModel (t + v) : ℝ)) : ℂ) +
            Complex.I *
              ((((selbergSqrtZetaSignedRationalFrequency q -
                    selbergSqrtZetaSignedRationalFrequency r) * t +
                  selbergSqrtZetaSignedRationalFrequency q * w -
                  selbergSqrtZetaSignedRationalFrequency r * v : ℝ)) : ℂ) := by
      unfold selbergSqrtZetaSignedRationalShortKernelPhase
      push_cast
      ring
    have hlinear :
        Complex.I *
            ((((selbergSqrtZetaSignedRationalFrequency q -
                    selbergSqrtZetaSignedRationalFrequency r) * t +
                  selbergSqrtZetaSignedRationalFrequency q * w -
                  selbergSqrtZetaSignedRationalFrequency r * v : ℝ)) : ℂ) =
          Complex.I *
                (selbergSqrtZetaSignedRationalFrequency q : ℂ) * (t : ℂ) +
              Complex.I *
                (selbergSqrtZetaSignedRationalFrequency q : ℂ) * (w : ℂ) -
            Complex.I *
                (selbergSqrtZetaSignedRationalFrequency r : ℂ) * (t : ℂ) -
          Complex.I *
              (selbergSqrtZetaSignedRationalFrequency r : ℂ) * (v : ℂ) := by
      push_cast
      ring
    rw [hphase, Complex.exp_add, hlinear]
    ring
  have hnorm (t : ℝ) :
      ‖selbergSqrtZetaSignedRationalFixedShiftPhaseSum N X v w t‖ =
        ‖P (t + w)‖ * ‖P (t + v)‖ := by
    rw [hfactor, norm_mul, norm_mul]
    change
      ‖Complex.exp
          (Complex.I *
            (((thetaModel (t + w) - thetaModel (t + v) : ℝ)) : ℂ))‖ *
          (‖P (t + w)‖ * ‖star (P (t + v))‖) =
        ‖P (t + w)‖ * ‖P (t + v)‖
    rw [norm_star, Complex.norm_exp_I_mul_ofReal, one_mul]
  have hleftInt :
      IntervalIntegrable
        (fun t : ℝ => ‖P (t + w)‖ * ‖P (t + v)‖)
        volume T (2 * T - H) := by
    apply Continuous.intervalIntegrable
    exact
      ((hP.comp (continuous_id.add continuous_const)).norm).mul
        ((hP.comp (continuous_id.add continuous_const)).norm)
  have hwSqInt :
      IntervalIntegrable
        (fun t : ℝ => Complex.normSq (P (t + w)))
        volume T (2 * T - H) := by
    apply Continuous.intervalIntegrable
    exact
      Complex.continuous_normSq.comp
        (hP.comp (continuous_id.add continuous_const))
  have hvSqInt :
      IntervalIntegrable
        (fun t : ℝ => Complex.normSq (P (t + v)))
        volume T (2 * T - H) := by
    apply Continuous.intervalIntegrable
    exact
      Complex.continuous_normSq.comp
        (hP.comp (continuous_id.add continuous_const))
  have hrightInt :
      IntervalIntegrable
        (fun t : ℝ =>
          (Complex.normSq (P (t + w)) +
            Complex.normSq (P (t + v))) / 2)
        volume T (2 * T - H) := by
    apply Continuous.intervalIntegrable
    exact
      ((Complex.continuous_normSq.comp
          (hP.comp (continuous_id.add continuous_const))).add
        (Complex.continuous_normSq.comp
          (hP.comp (continuous_id.add continuous_const)))).div_const 2
  have hpoint : ∀ t ∈ Set.Icc T (2 * T - H),
      ‖P (t + w)‖ * ‖P (t + v)‖ ≤
        (Complex.normSq (P (t + w)) +
          Complex.normSq (P (t + v))) / 2 := by
    intro t ht
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖P (t + w)‖ - ‖P (t + v)‖)]
  have hmean (u : ℝ) :
      (∫ t in T..2 * T - H, Complex.normSq (P (t + u))) ≤ B := by
    calc
      (∫ t in T..2 * T - H, Complex.normSq (P (t + u))) =
          ∫ x in T + u..(2 * T - H) + u,
            Complex.normSq (P x) := by
        simpa using
          (intervalIntegral.integral_comp_add_right
            (fun x : ℝ => Complex.normSq (P x)) u
            (a := T) (b := 2 * T - H))
      _ ≤ ((2 * T - H) + u - (T + u)) *
            ∑ q ∈ Q, Complex.normSq (c q) +
          4 * Real.pi *
            ∑ q ∈ Q,
              Complex.normSq (c q) /
                PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                  Q omega q := by
        simpa only [P, Q, c, omega] using
          (integral_normSq_selbergSqrtZetaSignedRationalCollectedPolynomial_le_localSeparation
            N X (show T + u ≤ (2 * T - H) + u by linarith) hQ)
      _ = B := by
        dsimp only [B]
        ring
  calc
    ‖∫ t in T..2 * T - H,
        selbergSqrtZetaSignedRationalFixedShiftPhaseSum N X v w t‖ ≤
        ∫ t in T..2 * T - H,
          ‖selbergSqrtZetaSignedRationalFixedShiftPhaseSum N X v w t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hlong
    _ = ∫ t in T..2 * T - H,
          ‖P (t + w)‖ * ‖P (t + v)‖ := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hnorm t
    _ ≤ ∫ t in T..2 * T - H,
          (Complex.normSq (P (t + w)) +
            Complex.normSq (P (t + v))) / 2 :=
      intervalIntegral.integral_mono_on
        hlong hleftInt hrightInt hpoint
    _ = ((∫ t in T..2 * T - H, Complex.normSq (P (t + w))) +
          ∫ t in T..2 * T - H, Complex.normSq (P (t + v))) / 2 := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_add hwSqInt hvSqInt]
    _ ≤ B := by
      nlinarith [hmean w, hmean v]
    _ = (T - H) *
          ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
            Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff N X q) +
        4 * Real.pi *
          ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
            Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff N X q) /
              PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                (selbergSqrtZetaSignedRationalSupport N X)
                selbergSqrtZetaSignedRationalFrequency q := by
      rfl

end HardyTheorem
