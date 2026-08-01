import HardyTheorem.SelbergSqrtZetaSignedRationalNoncarrierEnergy
import HardyTheorem.SelbergSqrtZetaSignedRationalShortKernelLocalSeparation

/-!
# The actual noncarrier short-window kernel

The ratio-one carrier is removed before the Hermitian short-window argument.
The remaining theta-frequency model is factorized through the genuine
noncarrier exponential polynomial, so Montgomery--Vaughan local separation
never pays for the deleted carrier.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- The Hermitian fixed-shift phase sum with the ratio-one carrier deleted
from both frequency variables. -/
noncomputable def
    selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum
    (N X : ℕ) (v w t : ℝ) : ℂ :=
  ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
    ∑ r ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
      (starRingEnd ℂ) (selbergSqrtZetaSignedRationalCoeff N X r) *
        selbergSqrtZetaSignedRationalCoeff N X q *
        Complex.exp
          (Complex.I *
            ((selbergSqrtZetaSignedRationalShortKernelPhase
              q r v w t : ℝ) : ℂ))

/-- The noncarrier fixed-shift phase sum is a unit Hardy-phase factor times
the ordinary correlation of the noncarrier exponential polynomial. -/
theorem
    selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum_eq_factorized
    (N X : ℕ) (v w t : ℝ) :
    selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum N X v w t =
      Complex.exp
          (Complex.I *
            (((thetaModel (t + w) - thetaModel (t + v) : ℝ)) : ℂ)) *
        (selbergSqrtZetaSignedRationalNoncarrierPolynomial N X (t + w) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedRationalNoncarrierPolynomial N X
              (t + v))) := by
  classical
  unfold selbergSqrtZetaSignedRationalNoncarrierPolynomial
  rw [MathlibAux.exponentialPolynomial_mul_conj_shift_eq_double_sum]
  unfold selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum
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

private noncomputable def
    selbergSqrtZetaSignedRationalNoncarrierPhasePolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (I * (thetaModel t : ℂ)) *
    selbergSqrtZetaSignedRationalNoncarrierPolynomial N X t

private theorem
    selbergSqrtZetaSignedRationalNoncarrierPhasePolynomial_eq_sum
    (N X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedRationalNoncarrierPhasePolynomial N X t =
      ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        selbergSqrtZetaSignedRationalCoeff N X q *
          Complex.exp
            (I * ((thetaModel t +
              selbergSqrtZetaSignedRationalFrequency q * t : ℝ) : ℂ)) := by
  classical
  unfold selbergSqrtZetaSignedRationalNoncarrierPhasePolynomial
    selbergSqrtZetaSignedRationalNoncarrierPolynomial
    MathlibAux.exponentialPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [show
      I * ((thetaModel t +
          selbergSqrtZetaSignedRationalFrequency q * t : ℝ) : ℂ) =
        I * (thetaModel t : ℂ) +
          I * (selbergSqrtZetaSignedRationalFrequency q : ℂ) * (t : ℂ) by
    push_cast
    ring]
  rw [Complex.exp_add]
  ring

private theorem
    integral_selbergSqrtZetaSignedRationalNoncarrierPhasePolynomial_shift_eq
    (N X : ℕ) {H t : ℝ} (ht : 0 < t) (hH : 0 ≤ H) :
    (∫ v in 0..H,
      selbergSqrtZetaSignedRationalNoncarrierPhasePolynomial N X (t + v)) =
      ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        selbergSqrtZetaSignedRationalCoeff N X q *
          thetaFrequencyShortIntegral
            (selbergSqrtZetaSignedRationalFrequency q) H t := by
  classical
  have hpoint : ∀ v ∈ Set.uIcc (0 : ℝ) H,
      selbergSqrtZetaSignedRationalNoncarrierPhasePolynomial N X (t + v) =
        ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
          selbergSqrtZetaSignedRationalCoeff N X q *
            Complex.exp
              (I * ((thetaModel (t + v) +
                selbergSqrtZetaSignedRationalFrequency q *
                  (t + v) : ℝ) : ℂ)) := by
    intro v hv
    exact
      selbergSqrtZetaSignedRationalNoncarrierPhasePolynomial_eq_sum
        N X (t + v)
  rw [intervalIntegral.integral_congr hpoint]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro q hq
    have hfactor :
        (∫ v in 0..H,
          selbergSqrtZetaSignedRationalCoeff N X q *
            Complex.exp
              (I * ((thetaModel (t + v) +
                selbergSqrtZetaSignedRationalFrequency q *
                  (t + v) : ℝ) : ℂ))) =
          selbergSqrtZetaSignedRationalCoeff N X q *
            ∫ v in 0..H,
              Complex.exp
                (I * ((thetaModel (t + v) +
                  selbergSqrtZetaSignedRationalFrequency q *
                    (t + v) : ℝ) : ℂ)) :=
      intervalIntegral.integral_const_mul _ _
    rw [hfactor]
    rfl
  · intro q hq
    apply ContinuousOn.intervalIntegrable_of_Icc hH
    intro v hv
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.cexp
    apply ContinuousAt.mul continuousAt_const
    apply Complex.continuous_ofReal.continuousAt.comp
    have htv : 0 < t + v := by linarith [hv.1]
    have htheta : ContinuousAt (fun x : ℝ => thetaModel (t + x)) v := by
      unfold thetaModel
      fun_prop (disch := positivity)
    exact htheta.add
      (continuousAt_const.mul
        (continuousAt_const.add continuousAt_id))

private noncomputable def
    selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped
    (T : ℝ) (N X : ℕ) (t : ℝ) : ℂ :=
  selbergSqrtZetaSignedRationalNoncarrierPhasePolynomial N X (max T t)

private theorem
    continuous_selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped
    {T : ℝ} (hT : 0 < T) (N X : ℕ) :
    Continuous
      (selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped T N X) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hmax : 0 < max T x := hT.trans_le (le_max_left T x)
  have harg : ContinuousAt (fun y : ℝ => max T y) x :=
    (continuous_const.max continuous_id).continuousAt
  have htheta : ContinuousAt (fun y : ℝ => thetaModel (max T y)) x := by
    unfold thetaModel
    fun_prop (disch := positivity)
  have hP : ContinuousAt
      (fun y : ℝ =>
        selbergSqrtZetaSignedRationalNoncarrierPolynomial N X (max T y)) x := by
    unfold selbergSqrtZetaSignedRationalNoncarrierPolynomial
      MathlibAux.exponentialPolynomial
    fun_prop
  unfold selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped
    selbergSqrtZetaSignedRationalNoncarrierPhasePolynomial
  exact
    ((continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp htheta)).cexp).mul hP

private theorem
    selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped_eq
    (T : ℝ) (N X : ℕ) {t : ℝ} (ht : T ≤ t) :
    selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped T N X t =
      selbergSqrtZetaSignedRationalNoncarrierPhasePolynomial N X t := by
  unfold selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped
  rw [max_eq_right ht]

private theorem
    integral_selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped_shift_eq
    {T : ℝ} (hT : 0 < T) (N X : ℕ) {H t : ℝ}
    (ht : T ≤ t) (hH : 0 ≤ H) :
    (∫ v in 0..H,
      selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped
        T N X (t + v)) =
      ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        selbergSqrtZetaSignedRationalCoeff N X q *
          thetaFrequencyShortIntegral
            (selbergSqrtZetaSignedRationalFrequency q) H t := by
  calc
    (∫ v in 0..H,
      selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped
        T N X (t + v)) =
        ∫ v in 0..H,
          selbergSqrtZetaSignedRationalNoncarrierPhasePolynomial
            N X (t + v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hvIcc : v ∈ Icc (0 : ℝ) H := by
        simpa [uIcc_of_le hH] using hv
      exact
        selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped_eq
          T N X (ht.trans (le_add_of_nonneg_right hvIcc.1))
    _ = ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        selbergSqrtZetaSignedRationalCoeff N X q *
          thetaFrequencyShortIntegral
            (selbergSqrtZetaSignedRationalFrequency q) H t :=
      integral_selbergSqrtZetaSignedRationalNoncarrierPhasePolynomial_shift_eq
        N X (hT.trans_le ht) hH

/-- The actual noncarrier short-model square energy is the real part of the
noncarrier fixed-shift Hermitian phase sum. -/
theorem
    integral_normSq_selbergSqrtZetaSignedRationalNoncarrierShortModel_eq_re_fixedShiftPhaseSum
    (T : ℝ) (X : ℕ) {H : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T) :
    (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t)) =
      (∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum
          (firstZetaApproximationCutoff T) X v w t).re := by
  let N := firstZetaApproximationCutoff T
  let f : ℝ → ℂ :=
    selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped T N X
  have hf : Continuous f :=
    continuous_selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped
      hT N X
  have hlong : T ≤ 2 * T - H := by linarith
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
    MathlibAux.slidingIntervalCorrelation_fubini hf hf hlong hH
  calc
    (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t)) =
        ∫ t in T..2 * T - H,
          Complex.normSq (∫ v in 0..H, f (t + v)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Icc T (2 * T - H) := by
        simpa [uIcc_of_le hlong] using ht
      dsimp only [f]
      change
        Complex.normSq
            (selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t) =
          Complex.normSq
            (∫ v in 0..H,
              selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped
                T N X (t + v))
      rw [integral_selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped_shift_eq
          hT N X htIcc.1 hH]
      rfl
    _ = (∫ t in T..2 * T - H,
          (starRingEnd ℂ) (∫ v in 0..H, f (t + v)) *
            (∫ w in 0..H, f (t + w))).re := hre
    _ = (∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
          (starRingEnd ℂ) (f (t + v)) * f (t + w)).re :=
      congrArg Complex.re hfubini
    _ = (∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum
          N X v w t).re := by
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
      rw [selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped_eq
          T N X (htIcc.1.trans (le_add_of_nonneg_right hvIcc.1)),
        selbergSqrtZetaSignedRationalNoncarrierPhasePolynomialClamped_eq
          T N X (htIcc.1.trans (le_add_of_nonneg_right hwIcc.1))]
      rw [selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum_eq_factorized]
      unfold selbergSqrtZetaSignedRationalNoncarrierPhasePolynomial
      rw [map_mul]
      have hexp (a b : ℝ) :
          (starRingEnd ℂ) (Complex.exp (I * (a : ℂ))) *
              Complex.exp (I * (b : ℂ)) =
            Complex.exp (I * ((b - a : ℝ) : ℂ)) := by
        rw [← Complex.exp_conj, ← Complex.exp_add]
        congr 1
        simp only [map_mul, conj_I, conj_ofReal]
        push_cast
        ring
      calc
        (starRingEnd ℂ)
              (Complex.exp (I * (thetaModel (t + v) : ℂ))) *
            (starRingEnd ℂ)
              (selbergSqrtZetaSignedRationalNoncarrierPolynomial
                N X (t + v)) *
            (Complex.exp (I * (thetaModel (t + w) : ℂ)) *
              selbergSqrtZetaSignedRationalNoncarrierPolynomial
                N X (t + w)) =
            ((starRingEnd ℂ)
                (Complex.exp (I * (thetaModel (t + v) : ℂ))) *
              Complex.exp (I * (thetaModel (t + w) : ℂ))) *
              (selbergSqrtZetaSignedRationalNoncarrierPolynomial
                  N X (t + w) *
                (starRingEnd ℂ)
                  (selbergSqrtZetaSignedRationalNoncarrierPolynomial
                    N X (t + v))) := by ring
        _ = Complex.exp
              (I *
                (((thetaModel (t + w) - thetaModel (t + v) : ℝ)) : ℂ)) *
              (selbergSqrtZetaSignedRationalNoncarrierPolynomial N X (t + w) *
                (starRingEnd ℂ)
                  (selbergSqrtZetaSignedRationalNoncarrierPolynomial
                    N X (t + v))) := by
          rw [hexp]

/-- A noncarrier fixed-shift section is bounded only by the recomputed
noncarrier local-separation energy. -/
theorem
    norm_integral_selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum_le_localSeparation
    (N X : ℕ) {T H v w : ℝ}
    (_hT : 0 < T) (_hH : 0 ≤ H) (hroom : H ≤ T)
    (_hv : v ∈ Icc (0 : ℝ) H) (_hw : w ∈ Icc (0 : ℝ) H)
    (hNoncarrier :
      (selbergSqrtZetaSignedRationalNoncarrierSupport N X).Nontrivial) :
    ‖∫ t in T..2 * T - H,
        selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum
          N X v w t‖ ≤
      (T - H) *
          ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
            Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff N X q) +
        4 * Real.pi *
          ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
            Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff N X q) /
              PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                (selbergSqrtZetaSignedRationalNoncarrierSupport N X)
                selbergSqrtZetaSignedRationalFrequency q := by
  let P : ℝ → ℂ :=
    selbergSqrtZetaSignedRationalNoncarrierPolynomial N X
  let B : ℝ :=
    (T - H) *
        ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
          Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) +
      4 * Real.pi *
        ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
          Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
            PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
              (selbergSqrtZetaSignedRationalNoncarrierSupport N X)
              selbergSqrtZetaSignedRationalFrequency q
  have hlong : T ≤ 2 * T - H := by linarith
  have hP : Continuous P := by
    dsimp only [P]
    unfold selbergSqrtZetaSignedRationalNoncarrierPolynomial
      MathlibAux.exponentialPolynomial
    fun_prop
  have hnorm (t : ℝ) :
      ‖selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum
          N X v w t‖ =
        ‖P (t + w)‖ * ‖P (t + v)‖ := by
    rw [selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum_eq_factorized,
      norm_mul, norm_mul]
    change
      ‖Complex.exp
          (Complex.I *
            (((thetaModel (t + w) - thetaModel (t + v) : ℝ)) : ℂ))‖ *
          (‖P (t + w)‖ * ‖star (P (t + v))‖) =
        ‖P (t + w)‖ * ‖P (t + v)‖
    rw [norm_star, Complex.norm_exp_I_mul_ofReal, one_mul]
  have hleftInt : IntervalIntegrable
      (fun t : ℝ => ‖P (t + w)‖ * ‖P (t + v)‖)
      volume T (2 * T - H) := by
    apply Continuous.intervalIntegrable
    exact
      ((hP.comp (continuous_id.add continuous_const)).norm).mul
        ((hP.comp (continuous_id.add continuous_const)).norm)
  have hwSqInt : IntervalIntegrable
      (fun t : ℝ => Complex.normSq (P (t + w)))
      volume T (2 * T - H) := by
    apply Continuous.intervalIntegrable
    exact Complex.continuous_normSq.comp
      (hP.comp (continuous_id.add continuous_const))
  have hvSqInt : IntervalIntegrable
      (fun t : ℝ => Complex.normSq (P (t + v)))
      volume T (2 * T - H) := by
    apply Continuous.intervalIntegrable
    exact Complex.continuous_normSq.comp
      (hP.comp (continuous_id.add continuous_const))
  have hrightInt : IntervalIntegrable
      (fun t : ℝ =>
        (Complex.normSq (P (t + w)) + Complex.normSq (P (t + v))) / 2)
      volume T (2 * T - H) := by
    apply Continuous.intervalIntegrable
    exact
      ((Complex.continuous_normSq.comp
          (hP.comp (continuous_id.add continuous_const))).add
        (Complex.continuous_normSq.comp
          (hP.comp (continuous_id.add continuous_const)))).div_const 2
  have hpoint : ∀ t ∈ Icc T (2 * T - H),
      ‖P (t + w)‖ * ‖P (t + v)‖ ≤
        (Complex.normSq (P (t + w)) + Complex.normSq (P (t + v))) / 2 := by
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
            ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
              Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) +
          4 * Real.pi *
            ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
              Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
                PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                  (selbergSqrtZetaSignedRationalNoncarrierSupport N X)
                  selbergSqrtZetaSignedRationalFrequency q := by
        simpa only [P] using
          (integral_normSq_selbergSqrtZetaSignedRationalNoncarrierPolynomial_le_localSeparation
            N X (show T + u ≤ (2 * T - H) + u by linarith) hNoncarrier)
      _ = B := by
        dsimp only [B]
        ring
  calc
    ‖∫ t in T..2 * T - H,
        selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum
          N X v w t‖ ≤
        ∫ t in T..2 * T - H,
          ‖selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum
            N X v w t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hlong
    _ = ∫ t in T..2 * T - H, ‖P (t + w)‖ * ‖P (t + v)‖ := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hnorm t
    _ ≤ ∫ t in T..2 * T - H,
          (Complex.normSq (P (t + w)) + Complex.normSq (P (t + v))) / 2 :=
      intervalIntegral.integral_mono_on hlong hleftInt hrightInt hpoint
    _ = ((∫ t in T..2 * T - H, Complex.normSq (P (t + w))) +
          ∫ t in T..2 * T - H, Complex.normSq (P (t + v))) / 2 := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_add hwSqInt hvSqInt]
    _ ≤ B := by nlinarith [hmean w, hmean v]
    _ = (T - H) *
          ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
            Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) +
        4 * Real.pi *
          ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
            Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
              PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                (selbergSqrtZetaSignedRationalNoncarrierSupport N X)
                selbergSqrtZetaSignedRationalFrequency q := by
      rfl

private theorem
    norm_integral_integral_integral_selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum_le_localSeparation
    (N X : ℕ) {T H : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T)
    (hNoncarrier :
      (selbergSqrtZetaSignedRationalNoncarrierSupport N X).Nontrivial) :
    ‖∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum
          N X v w t‖ ≤
      H ^ 2 *
        ((T - H) *
            ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
              Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) +
          4 * Real.pi *
            ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
              Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
                PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                  (selbergSqrtZetaSignedRationalNoncarrierSupport N X)
                  selbergSqrtZetaSignedRationalFrequency q) := by
  let B : ℝ :=
    (T - H) *
        ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
          Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) +
      4 * Real.pi *
        ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
          Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
            PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
              (selbergSqrtZetaSignedRationalNoncarrierSupport N X)
              selbergSqrtZetaSignedRationalFrequency q
  have hinner (v : ℝ) (hv : v ∈ uIcc (0 : ℝ) H) :
      ‖∫ w in 0..H, ∫ t in T..2 * T - H,
          selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum
            N X v w t‖ ≤ B * H := by
    calc
      ‖∫ w in 0..H, ∫ t in T..2 * T - H,
          selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum
            N X v w t‖ ≤ B * |H - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro w hw
        have hvIcc : v ∈ Icc (0 : ℝ) H := by
          simpa [uIcc_of_le hH] using hv
        have hwIcc : w ∈ Icc (0 : ℝ) H := by
          simpa [uIcc_of_le hH] using (uIoc_subset_uIcc hw)
        simpa only [B] using
          norm_integral_selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum_le_localSeparation
            N X hT hH hroom hvIcc hwIcc hNoncarrier
      _ = B * H := by rw [sub_zero, abs_of_nonneg hH]
  calc
    ‖∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum
          N X v w t‖ ≤ (B * H) * |H - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro v hv
      exact hinner v (uIoc_subset_uIcc hv)
    _ = H ^ 2 * B := by
      rw [sub_zero, abs_of_nonneg hH]
      ring
    _ = H ^ 2 *
        ((T - H) *
            ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
              Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) +
          4 * Real.pi *
            ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
              Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
                PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                  (selbergSqrtZetaSignedRationalNoncarrierSupport N X)
                  selbergSqrtZetaSignedRationalFrequency q) := by
      rfl

/-- The actual Hardy-phase noncarrier short model satisfies the
local-separation mean-square budget with the carrier absent from both
coefficient sums and separation denominators. -/
theorem
    integral_normSq_selbergSqrtZetaSignedRationalNoncarrierShortModel_le_localSeparation
    (T : ℝ) (X : ℕ) {H : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T)
    (hNoncarrier :
      (selbergSqrtZetaSignedRationalNoncarrierSupport
        (firstZetaApproximationCutoff T) X).Nontrivial) :
    (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t)) ≤
      H ^ 2 *
        ((T - H) *
            ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport
                (firstZetaApproximationCutoff T) X,
              Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff
                  (firstZetaApproximationCutoff T) X q) +
          4 * Real.pi *
            ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport
                (firstZetaApproximationCutoff T) X,
              Complex.normSq
                  (selbergSqrtZetaSignedRationalCoeff
                    (firstZetaApproximationCutoff T) X q) /
                PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                  (selbergSqrtZetaSignedRationalNoncarrierSupport
                    (firstZetaApproximationCutoff T) X)
                  selbergSqrtZetaSignedRationalFrequency q) := by
  let z : ℂ :=
    ∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
      selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum
        (firstZetaApproximationCutoff T) X v w t
  calc
    (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalNoncarrierShortModel T X H t)) =
        z.re := by
      simpa only [z] using
        integral_normSq_selbergSqrtZetaSignedRationalNoncarrierShortModel_eq_re_fixedShiftPhaseSum
          T X hT hH hroom
    _ ≤ ‖z‖ := Complex.re_le_norm z
    _ ≤ H ^ 2 *
        ((T - H) *
            ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport
                (firstZetaApproximationCutoff T) X,
              Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff
                  (firstZetaApproximationCutoff T) X q) +
          4 * Real.pi *
            ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport
                (firstZetaApproximationCutoff T) X,
              Complex.normSq
                  (selbergSqrtZetaSignedRationalCoeff
                    (firstZetaApproximationCutoff T) X q) /
                PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                  (selbergSqrtZetaSignedRationalNoncarrierSupport
                    (firstZetaApproximationCutoff T) X)
                  selbergSqrtZetaSignedRationalFrequency q) := by
      simpa only [z] using
        norm_integral_integral_integral_selbergSqrtZetaSignedRationalNoncarrierFixedShiftPhaseSum_le_localSeparation
          (firstZetaApproximationCutoff T) X hT hH hroom hNoncarrier

end HardyTheorem
