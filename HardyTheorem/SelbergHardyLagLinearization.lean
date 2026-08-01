import HardyTheorem.SelbergSqrtZetaSignedRationalShortKernelPhase

/-!
# Uniform linearization of the Hardy theta lag

The lag phase occurring after a sliding-window autocorrelation is

`thetaModel x - thetaModel (x + tau) - omega * tau`.

Its exact tangent frequency at `tau = 0` is
`-(deriv thetaModel x + omega)`.  No lower bound on that frequency is
possible for arbitrary `omega`; this file instead bounds its drift and the
corresponding first-order remainder uniformly on `x in [T, 2T]` and
`|tau| <= H`.
-/

open Set

namespace HardyTheorem

/-- The theta-model lag phase with an arbitrary additional lag frequency. -/
noncomputable def thetaLagPhase (omega x tau : ℝ) : ℝ :=
  thetaModel x - thetaModel (x + tau) - omega * tau

/-- The exact tangent frequency of `thetaLagPhase` at zero lag. -/
noncomputable def thetaLagReferenceFrequency (omega x : ℝ) : ℝ :=
  -(deriv thetaModel x + omega)

/-- Exact derivative of the theta lag at every positive shifted height. -/
theorem hasDerivAt_thetaLagPhase
    (omega x : ℝ) {tau : ℝ} (hxtau : 0 < x + tau) :
    HasDerivAt (thetaLagPhase omega x)
      (-(deriv thetaModel (x + tau) + omega)) tau := by
  have hthetaDiff : DifferentiableAt ℝ thetaModel (x + tau) := by
    change DifferentiableAt ℝ
      (fun y : ℝ =>
        y / 2 * Real.log (y / (2 * Real.pi)) - y / 2 - Real.pi / 8)
      (x + tau)
    fun_prop (disch := positivity)
  have hshift : HasDerivAt (fun u : ℝ => thetaModel (x + u))
      (deriv thetaModel (x + tau)) tau := by
    simpa only [Function.comp_def, zero_add, mul_one] using
      hthetaDiff.hasDerivAt.comp tau
        ((hasDerivAt_const tau x).add (hasDerivAt_id tau))
  have hlinear : HasDerivAt (fun u : ℝ => omega * u) omega tau := by
    simpa using (hasDerivAt_id tau).const_mul omega
  have hphase :=
    ((hasDerivAt_const tau (thetaModel x)).sub hshift).sub hlinear
  exact hphase.congr_deriv (by ring)

/-- At zero lag, the derivative is exactly the declared reference
frequency.  This is an identity, not a nonstationarity claim. -/
theorem deriv_thetaLagPhase_zero
    (omega : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (thetaLagPhase omega x) 0 =
      thetaLagReferenceFrequency omega x := by
  rw [(hasDerivAt_thetaLagPhase omega x (by simpa using hx)).deriv]
  simp [thetaLagReferenceFrequency]

/-- Explicit logarithmic form of the reference frequency. -/
theorem thetaLagReferenceFrequency_eq
    (omega : ℝ) {x : ℝ} (hx : 0 < x) :
    thetaLagReferenceFrequency omega x =
      -((1 / 2 : ℝ) * Real.log (x / (2 * Real.pi)) + omega) := by
  rw [thetaLagReferenceFrequency, deriv_thetaModel hx]

/-- Uniform drift of the lag frequency from its exact value at zero lag.

The frequency `omega` cancels from the estimate.  The denominator
`T - H` is the smallest possible shifted height under the stated window
hypotheses. -/
theorem abs_deriv_thetaLagPhase_sub_referenceFrequency_le
    (omega : ℝ) {T H x tau : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hHT : H ≤ T / 2)
    (hx : x ∈ Icc T (2 * T)) (htau : |tau| ≤ H) :
    |deriv (thetaLagPhase omega x) tau -
        thetaLagReferenceFrequency omega x| ≤
      |tau| / (2 * (T - H)) := by
  have hTH : 0 < T - H := by linarith
  have hxLower : T - H ≤ x := by linarith [hx.1]
  have htauLower : -H ≤ tau :=
    (neg_le_of_abs_le htau)
  have hxtauLower : T - H ≤ x + tau := by
    linarith [hx.1]
  have hxpos : 0 < x := hT.trans_le hx.1
  have hxtaupos : 0 < x + tau := hTH.trans_le hxtauLower
  have hlog :=
    OscillatoryIntegral.abs_log_sub_log_le_div
      hTH hxLower hxtauLower
  rw [(hasDerivAt_thetaLagPhase omega x hxtaupos).deriv,
    thetaLagReferenceFrequency, deriv_thetaModel hxtaupos,
    deriv_thetaModel hxpos]
  rw [Real.log_div (ne_of_gt hxtaupos) (by positivity),
    Real.log_div (ne_of_gt hxpos) (by positivity)]
  calc
    |-((1 / 2 : ℝ) *
          (Real.log (x + tau) - Real.log (2 * Real.pi)) + omega) -
        -((1 / 2 : ℝ) *
          (Real.log x - Real.log (2 * Real.pi)) + omega)| =
        (1 / 2 : ℝ) * |Real.log (x + tau) - Real.log x| := by
      rw [show
          -((1 / 2 : ℝ) *
                (Real.log (x + tau) - Real.log (2 * Real.pi)) + omega) -
              -((1 / 2 : ℝ) *
                (Real.log x - Real.log (2 * Real.pi)) + omega) =
            -(1 / 2 : ℝ) *
              (Real.log (x + tau) - Real.log x) by ring]
      rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ (1 / 2 : ℝ) * (|(x + tau) - x| / (T - H)) := by
      gcongr
    _ = |tau| / (2 * (T - H)) := by
      rw [show (x + tau) - x = tau by ring]
      field_simp [hTH.ne']

/-- Mean-value remainder for the zero-lag tangent line, uniform throughout
the full lag window.  This remains valid at stationary frequencies. -/
theorem abs_thetaLagPhase_sub_linearized_le
    (omega : ℝ) {T H x tau : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hHT : H ≤ T / 2)
    (hx : x ∈ Icc T (2 * T)) (htau : |tau| ≤ H) :
    |thetaLagPhase omega x tau -
        thetaLagReferenceFrequency omega x * tau| ≤
      H * |tau| / (2 * (T - H)) := by
  let R : ℝ → ℝ := fun u =>
    thetaLagPhase omega x u - thetaLagReferenceFrequency omega x * u
  have hTH : 0 < T - H := by linarith
  have hdiff : ∀ u ∈ Icc (-H) H, DifferentiableAt ℝ R u := by
    intro u hu
    have huabs : |u| ≤ H := (abs_le).2 hu
    have huLower : -H ≤ u := hu.1
    have hxupos : 0 < x + u := by
      have : T - H ≤ x + u := by linarith [hx.1]
      exact hTH.trans_le this
    have hphase := hasDerivAt_thetaLagPhase omega x hxupos
    have hlinear :=
      (hasDerivAt_id u).const_mul (thetaLagReferenceFrequency omega x)
    exact (hphase.sub hlinear).differentiableAt
  have hbound : ∀ u ∈ Icc (-H) H,
      ‖deriv R u‖ ≤ H / (2 * (T - H)) := by
    intro u hu
    have huabs : |u| ≤ H := (abs_le).2 hu
    have huLower : -H ≤ u := hu.1
    have hxupos : 0 < x + u := by
      have : T - H ≤ x + u := by linarith [hx.1]
      exact hTH.trans_le this
    have hphase := hasDerivAt_thetaLagPhase omega x hxupos
    have hlinear :=
      (hasDerivAt_id u).const_mul (thetaLagReferenceFrequency omega x)
    have hRhas : HasDerivAt R
        (-(deriv thetaModel (x + u) + omega) -
          thetaLagReferenceFrequency omega x) u := by
      simpa only [R, id_eq, mul_one] using hphase.sub hlinear
    have hdrift :=
      abs_deriv_thetaLagPhase_sub_referenceFrequency_le
        omega hT hH hHT hx huabs
    rw [hphase.deriv] at hdrift
    rw [hRhas.deriv, Real.norm_eq_abs]
    exact hdrift.trans (div_le_div_of_nonneg_right huabs (by positivity))
  have hzero : (0 : ℝ) ∈ Icc (-H) H := by
    constructor <;> linarith
  have htauMem : tau ∈ Icc (-H) H := (abs_le).1 htau
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (convex_Icc (-H) H) hzero htauMem
  calc
    |thetaLagPhase omega x tau -
        thetaLagReferenceFrequency omega x * tau| =
        ‖R tau - R 0‖ := by
      simp [R, thetaLagPhase, Real.norm_eq_abs]
    _ ≤ (H / (2 * (T - H))) * ‖tau - 0‖ := hmv
    _ = H * |tau| / (2 * (T - H)) := by
      rw [sub_zero, Real.norm_eq_abs]
      ring

/-- Window-only form of the linearization error. -/
theorem abs_thetaLagPhase_sub_linearized_le_window_sq
    (omega : ℝ) {T H x tau : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hHT : H ≤ T / 2)
    (hx : x ∈ Icc T (2 * T)) (htau : |tau| ≤ H) :
    |thetaLagPhase omega x tau -
        thetaLagReferenceFrequency omega x * tau| ≤
      H ^ 2 / (2 * (T - H)) := by
  have hTH : 0 < T - H := by linarith
  calc
    |thetaLagPhase omega x tau -
        thetaLagReferenceFrequency omega x * tau| ≤
        H * |tau| / (2 * (T - H)) :=
      abs_thetaLagPhase_sub_linearized_le omega hT hH hHT hx htau
    _ ≤ H * H / (2 * (T - H)) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left htau hH) (by positivity)
    _ = H ^ 2 / (2 * (T - H)) := by ring

/-- The cosine of the true lag phase is uniformly close to the cosine at
the exact zero-lag tangent frequency.  This is the form consumed directly
by triangle-kernel Fourier estimates. -/
theorem abs_cos_thetaLagPhase_sub_cos_linearized_le
    (omega : ℝ) {T H x tau : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hHT : H ≤ T / 2)
    (hx : x ∈ Icc T (2 * T)) (htau : |tau| ≤ H) :
    |Real.cos (thetaLagPhase omega x tau) -
        Real.cos (thetaLagReferenceFrequency omega x * tau)| ≤
      H ^ 2 / (2 * (T - H)) := by
  exact (Real.abs_cos_sub_cos_le _ _).trans
    (abs_thetaLagPhase_sub_linearized_le_window_sq
      omega hT hH hHT hx htau)

end HardyTheorem
