import HardyTheorem.SelbergSqrtZetaSignedRationalCollected
import HardyTheorem.SelbergSqrtZetaSignedModelCorrelation
import HardyTheorem.ThetaFrequencyLinearization

/-!
# Rational-frequency short-window expansion of the signed Selberg model

Equal signed triple frequencies are first collected at positive rational
keys.  Integrating the resulting phase polynomial over a short window then
reduces exactly to a finite sum of the arbitrary-frequency theta integrals
from `ThetaFrequencyLinearization`.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- The signed phase polynomial is exactly the rationally collected sum of
theta phases. -/
theorem selbergSqrtZetaSignedPhasePolynomial_eq_sum_rational_thetaFrequency
    (N X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedPhasePolynomial N X t =
      ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        selbergSqrtZetaSignedRationalCoeff N X q *
          Complex.exp
            (I * ((thetaModel t +
              selbergSqrtZetaSignedRationalFrequency q * t : ℝ) : ℂ)) := by
  rw [selbergSqrtZetaSignedPhasePolynomial_eq_exp_mul_signedTriplePolynomial,
    selbergSqrtZetaSignedTriplePolynomial_eq_rationalCollectedPolynomial]
  unfold selbergSqrtZetaSignedRationalCollectedPolynomial
    MathlibAux.exponentialPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  have hcast :
      ((selbergSqrtZetaSignedRationalFrequency q * t : ℝ) : ℂ) =
        (selbergSqrtZetaSignedRationalFrequency q : ℂ) * (t : ℂ) :=
    Complex.ofReal_mul _ _
  have hexp :
      Complex.exp
          (I * ((thetaModel t +
            selbergSqrtZetaSignedRationalFrequency q * t : ℝ) : ℂ)) =
        Complex.exp (I * (thetaModel t : ℂ)) *
          Complex.exp
            (I *
              ((selbergSqrtZetaSignedRationalFrequency q * t : ℝ) : ℂ)) := by
    rw [show
        I * ((thetaModel t +
          selbergSqrtZetaSignedRationalFrequency q * t : ℝ) : ℂ) =
          I * (thetaModel t : ℂ) +
            I *
              ((selbergSqrtZetaSignedRationalFrequency q * t : ℝ) : ℂ) by
      push_cast
      ring]
    exact Complex.exp_add _ _
  rw [hcast] at hexp
  rw [hexp]
  ring

/-- Integrating the rationally collected phase polynomial over a positive
short window gives the corresponding finite sum of theta-frequency short
integrals. -/
theorem
    integral_selbergSqrtZetaSignedPhasePolynomial_shift_eq_sum_thetaFrequencyShortIntegral
    (N X : ℕ) {H t : ℝ} (ht : 0 < t) (hH : 0 ≤ H) :
    (∫ v in 0..H,
      selbergSqrtZetaSignedPhasePolynomial N X (t + v)) =
      ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        selbergSqrtZetaSignedRationalCoeff N X q *
          thetaFrequencyShortIntegral
            (selbergSqrtZetaSignedRationalFrequency q) H t := by
  have hpoint : ∀ v ∈ Set.uIcc (0 : ℝ) H,
      selbergSqrtZetaSignedPhasePolynomial N X (t + v) =
        ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
          selbergSqrtZetaSignedRationalCoeff N X q *
            Complex.exp
              (I * ((thetaModel (t + v) +
                selbergSqrtZetaSignedRationalFrequency q *
                  (t + v) : ℝ) : ℂ)) := by
    intro v _hv
    exact
      selbergSqrtZetaSignedPhasePolynomial_eq_sum_rational_thetaFrequency
        N X (t + v)
  rw [intervalIntegral.integral_congr hpoint]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro q _hq
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
  · intro q _hq
    apply ContinuousOn.intervalIntegrable_of_Icc hH
    intro v hv
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.cexp
    apply ContinuousAt.mul continuousAt_const
    apply Complex.continuous_ofReal.continuousAt.comp
    have htv : 0 < t + v := by
      linarith [hv.1]
    have htheta : ContinuousAt
        (fun x : ℝ => thetaModel (t + x)) v := by
      unfold thetaModel
      fun_prop (disch := positivity)
    exact htheta.add
      (continuousAt_const.mul
        (continuousAt_const.add continuousAt_id))

/-- The short-window integral of the full complex signed Selberg model is the
same rational theta-frequency sum, up to its constant phase `exp(I*kappa)`. -/
theorem
    integral_selbergSqrtZetaSignedComplexModel_shift_eq_sum_thetaFrequencyShortIntegral
    (kappa T : ℝ) (X : ℕ) {H t : ℝ}
    (ht : 0 < t) (hH : 0 ≤ H) :
    (∫ v in 0..H,
      selbergSqrtZetaSignedComplexModel kappa T X (t + v)) =
      Complex.exp (I * kappa) *
        ∑ q ∈ selbergSqrtZetaSignedRationalSupport
            (firstZetaApproximationCutoff T) X,
          selbergSqrtZetaSignedRationalCoeff
              (firstZetaApproximationCutoff T) X q *
            thetaFrequencyShortIntegral
              (selbergSqrtZetaSignedRationalFrequency q) H t := by
  unfold selbergSqrtZetaSignedComplexModel
  have hfactor :
      (∫ v in 0..H,
        Complex.exp (I * kappa) *
          selbergSqrtZetaSignedPhasePolynomial
            (firstZetaApproximationCutoff T) X (t + v)) =
        Complex.exp (I * kappa) *
          ∫ v in 0..H,
            selbergSqrtZetaSignedPhasePolynomial
              (firstZetaApproximationCutoff T) X (t + v) :=
    intervalIntegral.integral_const_mul _ _
  rw [hfactor]
  congr 1
  exact
    integral_selbergSqrtZetaSignedPhasePolynomial_shift_eq_sum_thetaFrequencyShortIntegral
      (firstZetaApproximationCutoff T) X ht hH

end HardyTheorem
