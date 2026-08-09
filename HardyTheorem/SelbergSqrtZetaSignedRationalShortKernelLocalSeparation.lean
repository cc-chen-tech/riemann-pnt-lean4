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

/-- The complete fixed-shift phase sum is one unitary Hardy-phase factor
times the ordinary correlation of the rationally collected polynomial. -/
theorem selbergSqrtZetaSignedRationalFixedShiftPhaseSum_eq_factorized
    (N X : ℕ) (v w t : ℝ) :
    selbergSqrtZetaSignedRationalFixedShiftPhaseSum N X v w t =
      Complex.exp
          (Complex.I *
            (((thetaModel (t + w) - thetaModel (t + v) : ℝ)) : ℂ)) *
        (selbergSqrtZetaSignedRationalCollectedPolynomial N X (t + w) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedRationalCollectedPolynomial N X (t + v))) := by
  classical
  unfold selbergSqrtZetaSignedRationalCollectedPolynomial
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

/-- At the zeta-approximation cutoff, the fixed-shift phase sum is exactly the
ordinary correlation of the finite complex Selberg model.  The constant phase
`kappa` cancels from the correlation. -/
theorem selbergSqrtZetaSignedRationalFixedShiftPhaseSum_eq_modelCorrelation
    (kappa T : ℝ) (X : ℕ) (v w t : ℝ) :
    selbergSqrtZetaSignedRationalFixedShiftPhaseSum
        (firstZetaApproximationCutoff T) X v w t =
      (starRingEnd ℂ)
          (selbergSqrtZetaSignedComplexModel kappa T X (t + v)) *
        selbergSqrtZetaSignedComplexModel kappa T X (t + w) := by
  have hexp (a b : ℝ) :
      (starRingEnd ℂ) (Complex.exp (I * (a : ℂ))) *
          Complex.exp (I * (b : ℂ)) =
        Complex.exp (I * ((b - a : ℝ) : ℂ)) := by
    rw [← Complex.exp_conj]
    rw [← Complex.exp_add]
    congr 1
    simp only [map_mul, conj_I, conj_ofReal]
    push_cast
    ring
  rw [selbergSqrtZetaSignedRationalFixedShiftPhaseSum_eq_factorized]
  unfold selbergSqrtZetaSignedComplexModel
  rw [selbergSqrtZetaSignedPhasePolynomial_eq_exp_mul_signedTriplePolynomial,
    selbergSqrtZetaSignedPhasePolynomial_eq_exp_mul_signedTriplePolynomial,
    selbergSqrtZetaSignedTriplePolynomial_eq_rationalCollectedPolynomial,
    selbergSqrtZetaSignedTriplePolynomial_eq_rationalCollectedPolynomial]
  rw [show
      (starRingEnd ℂ)
            (Complex.exp (I * (kappa : ℂ)) *
              (Complex.exp (I * (thetaModel (t + v) : ℂ)) *
                selbergSqrtZetaSignedRationalCollectedPolynomial
                  (firstZetaApproximationCutoff T) X (t + v))) *
          (Complex.exp (I * (kappa : ℂ)) *
            (Complex.exp (I * (thetaModel (t + w) : ℂ)) *
              selbergSqrtZetaSignedRationalCollectedPolynomial
                (firstZetaApproximationCutoff T) X (t + w))) =
        ((starRingEnd ℂ) (Complex.exp (I * (kappa : ℂ))) *
            Complex.exp (I * (kappa : ℂ))) *
          ((starRingEnd ℂ)
              (Complex.exp (I * (thetaModel (t + v) : ℂ))) *
            Complex.exp (I * (thetaModel (t + w) : ℂ))) *
          (selbergSqrtZetaSignedRationalCollectedPolynomial
              (firstZetaApproximationCutoff T) X (t + w) *
            (starRingEnd ℂ)
              (selbergSqrtZetaSignedRationalCollectedPolynomial
                (firstZetaApproximationCutoff T) X (t + v))) by
        simp only [map_mul]
        ring]
  rw [hexp kappa kappa,
    hexp (thetaModel (t + v)) (thetaModel (t + w))]
  norm_num

private noncomputable def selbergSqrtZetaSignedComplexModelClamped
    (kappa T : ℝ) (X : ℕ) (t : ℝ) : ℂ :=
  selbergSqrtZetaSignedComplexModel kappa T X (max T t)

private theorem continuous_selbergSqrtZetaSignedComplexModelClamped
    (kappa : ℝ) {T : ℝ} (X : ℕ) (hT : 0 < T) :
    Continuous (selbergSqrtZetaSignedComplexModelClamped kappa T X) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hmax : 0 < max T x := hT.trans_le (le_max_left T x)
  have harg : ContinuousAt (fun y : ℝ => max T y) x :=
    (continuous_const.max continuous_id).continuousAt
  have htheta :
      ContinuousAt (fun y : ℝ => thetaModel (max T y)) x := by
    unfold thetaModel
    fun_prop (disch := positivity)
  have hP : ContinuousAt
      (fun y : ℝ =>
        selbergSqrtZetaSignedCollectedTriplePolynomial
          (firstZetaApproximationCutoff T) X (max T y)) x := by
    unfold selbergSqrtZetaSignedCollectedTriplePolynomial
      MathlibAux.collectedExponentialPolynomial
      MathlibAux.exponentialPolynomial
    fun_prop
  rw [show selbergSqrtZetaSignedComplexModelClamped kappa T X =
      fun y : ℝ =>
        Complex.exp (I * (kappa : ℂ)) *
          Complex.exp (I * (thetaModel (max T y) : ℂ)) *
          selbergSqrtZetaSignedCollectedTriplePolynomial
            (firstZetaApproximationCutoff T) X (max T y) by
    funext y
    unfold selbergSqrtZetaSignedComplexModelClamped
    exact
      selbergSqrtZetaSignedComplexModel_eq_exp_mul_exp_mul_collectedTriplePolynomial
        kappa T X (max T y)]
  exact
    (continuousAt_const.mul
      (continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp htheta)).cexp).mul hP

private theorem selbergSqrtZetaSignedComplexModelClamped_eq
    (kappa T : ℝ) (X : ℕ) {t : ℝ} (ht : T ≤ t) :
    selbergSqrtZetaSignedComplexModelClamped kappa T X t =
      selbergSqrtZetaSignedComplexModel kappa T X t := by
  unfold selbergSqrtZetaSignedComplexModelClamped
  rw [max_eq_right ht]

/-- The integrated square energy of the actual rational short model is the
real part of the complete fixed-shift phase sum.  This is the bridge from the
local-separation kernel estimate to the model used in the Selberg bad-window
budget. -/
theorem
    integral_normSq_selbergSqrtZetaSignedRationalShortModel_eq_re_fixedShiftPhaseSum
    (kappa T : ℝ) (X : ℕ) {H : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T) :
    (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalShortModel T X H t)) =
      (∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        selbergSqrtZetaSignedRationalFixedShiftPhaseSum
          (firstZetaApproximationCutoff T) X v w t).re := by
  let f : ℝ → ℂ :=
    selbergSqrtZetaSignedComplexModelClamped kappa T X
  have hf : Continuous f :=
    continuous_selbergSqrtZetaSignedComplexModelClamped kappa X hT
  have hlong : T ≤ 2 * T - H := by linarith
  have hinner (t : ℝ) (ht : T ≤ t) :
      (∫ v in 0..H, f (t + v)) =
        ∫ v in 0..H,
          selbergSqrtZetaSignedComplexModel kappa T X (t + v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hvIcc : v ∈ Icc (0 : ℝ) H := by
      simpa [uIcc_of_le hH] using hv
    exact selbergSqrtZetaSignedComplexModelClamped_eq
      kappa T X (ht.trans (le_add_of_nonneg_right hvIcc.1))
  have hwindow : Continuous (fun t : ℝ => ∫ v in 0..H, f (t + v)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hf.comp (continuous_fst.add continuous_snd)
  have hcomplexInt : IntervalIntegrable
      (fun t : ℝ =>
        (starRingEnd ℂ) (∫ v in 0..H, f (t + v)) *
          (∫ w in 0..H, f (t + w)))
      volume T (2 * T - H) := by
    apply Continuous.intervalIntegrable
    exact hwindow.star.mul hwindow
  have hre :
      (∫ t in T..2 * T - H,
          Complex.normSq (∫ v in 0..H, f (t + v))) =
        (∫ t in T..2 * T - H,
          (starRingEnd ℂ) (∫ v in 0..H, f (t + v)) *
            (∫ w in 0..H, f (t + w))).re := by
    calc
      (∫ t in T..2 * T - H,
          Complex.normSq (∫ v in 0..H, f (t + v))) =
          ∫ t in T..2 * T - H,
            ((starRingEnd ℂ) (∫ v in 0..H, f (t + v)) *
              (∫ w in 0..H, f (t + w))).re := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact congrArg Complex.re
          (Complex.normSq_eq_conj_mul_self
            (z := ∫ v in 0..H, f (t + v)))
      _ = (∫ t in T..2 * T - H,
          (starRingEnd ℂ) (∫ v in 0..H, f (t + v)) *
            (∫ w in 0..H, f (t + w))).re :=
        Complex.reCLM.intervalIntegral_comp_comm hcomplexInt
  have hfubini :=
    MathlibAux.slidingIntervalCorrelation_fubini
      hf hf hlong hH
  calc
    (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalShortModel T X H t)) =
        ∫ t in T..2 * T - H,
          Complex.normSq
            (∫ v in 0..H,
              selbergSqrtZetaSignedComplexModel kappa T X (t + v)) :=
      (integral_normSq_integral_selbergSqrtZetaSignedComplexModel_shift_eq_rationalShortModel
        kappa T X hT hlong hH).symm
    _ = ∫ t in T..2 * T - H,
          Complex.normSq (∫ v in 0..H, f (t + v)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Icc T (2 * T - H) := by
        simpa [uIcc_of_le hlong] using ht
      change
        Complex.normSq
            (∫ v in 0..H,
              selbergSqrtZetaSignedComplexModel kappa T X (t + v)) =
          Complex.normSq (∫ v in 0..H, f (t + v))
      rw [hinner t htIcc.1]
    _ = (∫ t in T..2 * T - H,
          (starRingEnd ℂ) (∫ v in 0..H, f (t + v)) *
            (∫ w in 0..H, f (t + w))).re := hre
    _ = (∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
          (starRingEnd ℂ) (f (t + v)) * f (t + w)).re :=
      congrArg Complex.re hfubini
    _ = (∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        selbergSqrtZetaSignedRationalFixedShiftPhaseSum
          (firstZetaApproximationCutoff T) X v w t).re := by
      apply congrArg Complex.re
      apply intervalIntegral.integral_congr
      intro v hv
      have hvIcc : v ∈ Icc (0 : ℝ) H := by
        simpa [uIcc_of_le hH] using hv
      apply intervalIntegral.integral_congr
      intro w hw
      have hwIcc : w ∈ Icc (0 : ℝ) H := by
        simpa [uIcc_of_le hH] using hw
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Icc T (2 * T - H) := by
        simpa [uIcc_of_le hlong] using ht
      dsimp only [f]
      rw [selbergSqrtZetaSignedComplexModelClamped_eq
          kappa T X (htIcc.1.trans (le_add_of_nonneg_right hvIcc.1)),
        selbergSqrtZetaSignedComplexModelClamped_eq
          kappa T X (htIcc.1.trans (le_add_of_nonneg_right hwIcc.1))]
      exact
        (selbergSqrtZetaSignedRationalFixedShiftPhaseSum_eq_modelCorrelation
          kappa T X v w t).symm

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
  have hnorm (t : ℝ) :
      ‖selbergSqrtZetaSignedRationalFixedShiftPhaseSum N X v w t‖ =
        ‖P (t + w)‖ * ‖P (t + v)‖ := by
    rw [selbergSqrtZetaSignedRationalFixedShiftPhaseSum_eq_factorized,
      norm_mul, norm_mul]
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

/-- Averaging the complete fixed-shift frequency sum over the full short-window
shift square costs exactly the area `H²`; the local-separation cancellation is
retained inside the height integral. -/
theorem
    norm_integral_integral_integral_selbergSqrtZetaSignedRationalFixedShiftPhaseSum_le_localSeparation
    (N X : ℕ) {T H : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T)
    (hQ : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial) :
    ‖∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        selbergSqrtZetaSignedRationalFixedShiftPhaseSum N X v w t‖ ≤
      H ^ 2 *
        ((T - H) *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
              Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff N X q) +
          4 * Real.pi *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
              Complex.normSq
                  (selbergSqrtZetaSignedRationalCoeff N X q) /
                PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                  (selbergSqrtZetaSignedRationalSupport N X)
                  selbergSqrtZetaSignedRationalFrequency q) := by
  let B : ℝ :=
    (T - H) *
        ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
          Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) +
      4 * Real.pi *
        ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
          Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
            PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
              (selbergSqrtZetaSignedRationalSupport N X)
              selbergSqrtZetaSignedRationalFrequency q
  have hinner (v : ℝ) (hv : v ∈ Set.uIcc (0 : ℝ) H) :
      ‖∫ w in 0..H, ∫ t in T..2 * T - H,
          selbergSqrtZetaSignedRationalFixedShiftPhaseSum N X v w t‖ ≤
        B * H := by
    calc
      ‖∫ w in 0..H, ∫ t in T..2 * T - H,
          selbergSqrtZetaSignedRationalFixedShiftPhaseSum N X v w t‖ ≤
          B * |H - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro w hw
        have hvIcc : v ∈ Set.Icc (0 : ℝ) H := by
          simpa [Set.uIcc_of_le hH] using hv
        have hwIcc : w ∈ Set.Icc (0 : ℝ) H := by
          simpa [Set.uIcc_of_le hH] using
            (Set.uIoc_subset_uIcc hw)
        simpa only [B] using
          norm_integral_selbergSqrtZetaSignedRationalFixedShiftPhaseSum_le_localSeparation
            N X hT hH hroom hvIcc hwIcc hQ
      _ = B * H := by rw [sub_zero, abs_of_nonneg hH]
  calc
    ‖∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        selbergSqrtZetaSignedRationalFixedShiftPhaseSum N X v w t‖ ≤
        (B * H) * |H - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro v hv
      exact hinner v (Set.uIoc_subset_uIcc hv)
    _ = H ^ 2 * B := by
      rw [sub_zero, abs_of_nonneg hH]
      ring
    _ = H ^ 2 *
        ((T - H) *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
              Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff N X q) +
          4 * Real.pi *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
              Complex.normSq
                  (selbergSqrtZetaSignedRationalCoeff N X q) /
                PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                  (selbergSqrtZetaSignedRationalSupport N X)
                  selbergSqrtZetaSignedRationalFrequency q) := by
      rfl

/-- The actual rational short-model square energy satisfies the
local-separation budget.  This closes the analytic transfer from the complete
Hermitian fixed-shift kernel to the `L²` quantity used in the excessive-window
argument. -/
theorem
    integral_normSq_selbergSqrtZetaSignedRationalShortModel_le_localSeparation
    (kappa T : ℝ) (X : ℕ) {H : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T)
    (hQ :
      (selbergSqrtZetaSignedRationalSupport
        (firstZetaApproximationCutoff T) X).Nontrivial) :
    (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalShortModel T X H t)) ≤
      H ^ 2 *
        ((T - H) *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport
                (firstZetaApproximationCutoff T) X,
              Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff
                  (firstZetaApproximationCutoff T) X q) +
          4 * Real.pi *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport
                (firstZetaApproximationCutoff T) X,
              Complex.normSq
                  (selbergSqrtZetaSignedRationalCoeff
                    (firstZetaApproximationCutoff T) X q) /
                PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                  (selbergSqrtZetaSignedRationalSupport
                    (firstZetaApproximationCutoff T) X)
                  selbergSqrtZetaSignedRationalFrequency q) := by
  let z : ℂ :=
    ∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
      selbergSqrtZetaSignedRationalFixedShiftPhaseSum
        (firstZetaApproximationCutoff T) X v w t
  calc
    (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalShortModel T X H t)) =
        z.re := by
      simpa only [z] using
        integral_normSq_selbergSqrtZetaSignedRationalShortModel_eq_re_fixedShiftPhaseSum
          kappa T X hT hH hroom
    _ ≤ ‖z‖ := Complex.re_le_norm z
    _ ≤ H ^ 2 *
        ((T - H) *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport
                (firstZetaApproximationCutoff T) X,
              Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff
                  (firstZetaApproximationCutoff T) X q) +
          4 * Real.pi *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport
                (firstZetaApproximationCutoff T) X,
              Complex.normSq
                  (selbergSqrtZetaSignedRationalCoeff
                    (firstZetaApproximationCutoff T) X q) /
                PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                  (selbergSqrtZetaSignedRationalSupport
                    (firstZetaApproximationCutoff T) X)
                  selbergSqrtZetaSignedRationalFrequency q) := by
      simpa only [z] using
        norm_integral_integral_integral_selbergSqrtZetaSignedRationalFixedShiftPhaseSum_le_localSeparation
          (firstZetaApproximationCutoff T) X hT hH hroom hQ

end HardyTheorem
