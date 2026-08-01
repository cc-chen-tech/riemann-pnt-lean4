import HardyTheorem.SelbergSqrtZetaSignedRationalShortKernelPhase
import MathlibAux.SeparatedFrequencySquareEnvelope
import MathlibAux.SlidingLagCosineBudget

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

/-- Square-window coordinate form of the Hardy lag linearization.  The base
point moves from `x` to `x + v`, but the linear comparison frequency is frozen
at `x`. -/
theorem abs_cos_thetaLagPhase_shift_sub_cos_frozen_le
    (omega : ℝ) {T H x v w : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hHT : H ≤ T / 2)
    (hx : x ∈ Icc T (2 * T - H))
    (hv : v ∈ Icc (0 : ℝ) H) (hw : w ∈ Icc (0 : ℝ) H) :
    |Real.cos (thetaLagPhase omega (x + v) (w - v)) -
        Real.cos (thetaLagReferenceFrequency omega x * (w - v))| ≤
      H ^ 2 / (T - H) := by
  have hTH : 0 < T - H := by linarith
  have hxpos : 0 < x := hT.trans_le hx.1
  have hxvpos : 0 < x + v := by linarith [hv.1]
  have hxv : x + v ∈ Icc T (2 * T) := by
    constructor <;> linarith [hv.1, hv.2, hx.1, hx.2]
  have htau : |w - v| ≤ H := by
    rw [abs_le]
    constructor <;> linarith [hv.1, hv.2, hw.1, hw.2]
  have hcurved := abs_cos_thetaLagPhase_sub_cos_linearized_le
    omega hT hH hHT hxv htau
  have hlog := OscillatoryIntegral.abs_log_sub_log_le_div
    hT hx.1 (by linarith [hx.1, hv.1] : T ≤ x + v)
  have hfrequency :
      |thetaLagReferenceFrequency omega (x + v) -
          thetaLagReferenceFrequency omega x| ≤ H / (2 * T) := by
    rw [thetaLagReferenceFrequency_eq omega hxvpos,
      thetaLagReferenceFrequency_eq omega hxpos]
    rw [Real.log_div (ne_of_gt hxvpos) (by positivity),
      Real.log_div (ne_of_gt hxpos) (by positivity)]
    calc
      |-((1 / 2 : ℝ) *
            (Real.log (x + v) - Real.log (2 * Real.pi)) + omega) -
          -((1 / 2 : ℝ) *
            (Real.log x - Real.log (2 * Real.pi)) + omega)| =
          (1 / 2 : ℝ) * |Real.log (x + v) - Real.log x| := by
        rw [show
          -((1 / 2 : ℝ) *
              (Real.log (x + v) - Real.log (2 * Real.pi)) + omega) -
            -((1 / 2 : ℝ) *
              (Real.log x - Real.log (2 * Real.pi)) + omega) =
            -(1 / 2 : ℝ) *
              (Real.log (x + v) - Real.log x) by ring]
        rw [abs_mul, abs_neg,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      _ ≤ (1 / 2 : ℝ) * (|v| / T) := by
        rw [show (x + v) - x = v by ring] at hlog
        gcongr
      _ ≤ (1 / 2 : ℝ) * (H / T) := by
        gcongr
        exact abs_le.2 ⟨by linarith [hv.1], hv.2⟩
      _ = H / (2 * T) := by ring
  have hfrozen :
      |Real.cos
          (thetaLagReferenceFrequency omega (x + v) * (w - v)) -
        Real.cos (thetaLagReferenceFrequency omega x * (w - v))| ≤
        H ^ 2 / (2 * T) := by
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [← sub_mul, abs_mul]
    calc
      |thetaLagReferenceFrequency omega (x + v) -
          thetaLagReferenceFrequency omega x| * |w - v| ≤
          (H / (2 * T)) * H :=
        mul_le_mul hfrequency htau (abs_nonneg _) (by positivity)
      _ = H ^ 2 / (2 * T) := by ring
  have hhalf : H ^ 2 / (2 * T) ≤ H ^ 2 / (2 * (T - H)) := by
    exact div_le_div_of_nonneg_left (sq_nonneg H) (by positivity) (by linarith)
  calc
    |Real.cos (thetaLagPhase omega (x + v) (w - v)) -
        Real.cos (thetaLagReferenceFrequency omega x * (w - v))| ≤
      |Real.cos (thetaLagPhase omega (x + v) (w - v)) -
          Real.cos
            (thetaLagReferenceFrequency omega (x + v) * (w - v))| +
        |Real.cos
            (thetaLagReferenceFrequency omega (x + v) * (w - v)) -
          Real.cos (thetaLagReferenceFrequency omega x * (w - v))| :=
      abs_sub_le _ _ _
    _ ≤ H ^ 2 / (2 * (T - H)) + H ^ 2 / (2 * T) :=
      add_le_add hcurved hfrozen
    _ ≤ H ^ 2 / (2 * (T - H)) + H ^ 2 / (2 * (T - H)) :=
      add_le_add_right hhalf (H ^ 2 / (2 * (T - H)))
    _ = H ^ 2 / (T - H) := by
      field_simp [hTH.ne']
      ring

/-- The true Hardy lag phase inherits the triangle-kernel Fourier saving on
a square shift window.  The second term is the explicit cost of replacing
the curved theta phase by its zero-lag tangent frequency. -/
theorem abs_squareIntegral_cos_thetaLagPhase_le
    (omega K : ℝ) {T H x : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hHT : H ≤ T / 2)
    (hx : x ∈ Icc T (2 * T))
    (hfreq : thetaLagReferenceFrequency omega x ≠ 0) :
    |∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H,
        K * Real.cos (thetaLagPhase omega x (w - v))| ≤
      |K| * (4 / thetaLagReferenceFrequency omega x ^ 2) +
        (|K| * (H ^ 2 / (2 * (T - H)))) * H ^ 2 := by
  let clampLag : ℝ → ℝ := fun tau => max (-H) (min H tau)
  let F : ℝ → ℝ → ℝ := fun v w =>
    K * Real.cos (thetaLagPhase omega x (clampLag (w - v)))
  have hTH : 0 < T - H := by linarith
  have hxpos : 0 < x := hT.trans_le hx.1
  have hclampMem (tau : ℝ) : clampLag tau ∈ Icc (-H) H := by
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hclampContinuous : Continuous clampLag := by
    dsimp only [clampLag]
    fun_prop
  have hF : Continuous (Function.uncurry F) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hshift : 0 < x + clampLag (p.2 - p.1) := by
      have := (hclampMem (p.2 - p.1)).1
      linarith [hx.1]
    change ContinuousAt
      (fun p : ℝ × ℝ =>
        K * Real.cos
          (thetaLagPhase omega x (clampLag (p.2 - p.1)))) p
    unfold thetaLagPhase thetaModel
    fun_prop (disch := positivity)
  have hclampEq {v w : ℝ}
      (hv : v ∈ Icc (0 : ℝ) H) (hw : w ∈ Icc (0 : ℝ) H) :
      clampLag (w - v) = w - v := by
    have hlower : -H ≤ w - v := by linarith [hv.2, hw.1]
    have hupper : w - v ≤ H := by linarith [hv.1, hw.2]
    simp only [clampLag, min_eq_right hupper, max_eq_right hlower]
  have hbound : ∀ v ∈ Icc (0 : ℝ) H, ∀ w ∈ Icc (0 : ℝ) H,
      |F v w -
          K * Real.cos
            (thetaLagReferenceFrequency omega x * (w - v))| ≤
        |K| * (H ^ 2 / (2 * (T - H))) := by
    intro v hv w hw
    have htau : |w - v| ≤ H := by
      rw [abs_le]
      constructor <;> linarith [hv.1, hv.2, hw.1, hw.2]
    have hcos := abs_cos_thetaLagPhase_sub_cos_linearized_le
      omega hT hH hHT hx htau
    rw [show F v w =
        K * Real.cos (thetaLagPhase omega x (w - v)) by
      simp only [F, hclampEq hv hw]]
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hcos (abs_nonneg K)
  have hbudget :=
    MathlibAux.abs_squareIntegral_le_cosine_difference_main_add_uniform_error
      hF hH hfreq hbound
  have hintegral :
      (∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H,
          K * Real.cos (thetaLagPhase omega x (w - v))) =
        ∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, F v w := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc (0 : ℝ) H := by
      simpa [uIcc_of_le hH] using hv
    apply intervalIntegral.integral_congr
    intro w hw
    have hw' : w ∈ Icc (0 : ℝ) H := by
      simpa [uIcc_of_le hH] using hw
    simp only [F, hclampEq hv' hw']
  rw [hintegral]
  exact hbudget

/-- The square-window cancellation bound in the coordinates of an actual
autocorrelation: the two Hardy phases are evaluated at `x + v` and `x + w`.
The comparison frequency is frozen at the left endpoint `x`. -/
theorem abs_squareIntegral_cos_thetaLagPhase_shift_le
    (omega : ℝ) {T H x : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hHT : H ≤ T / 2)
    (hx : x ∈ Icc T (2 * T - H))
    (hfreq : thetaLagReferenceFrequency omega x ≠ 0) :
    |∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H,
        Real.cos (thetaLagPhase omega (x + v) (w - v))| ≤
      4 / thetaLagReferenceFrequency omega x ^ 2 +
        (H ^ 2 / (T - H)) * H ^ 2 := by
  let clampShift : ℝ → ℝ := fun y => max 0 (min H y)
  let F : ℝ → ℝ → ℝ := fun v w =>
    Real.cos (thetaModel (x + clampShift v) -
      thetaModel (x + clampShift w) -
      omega * (clampShift w - clampShift v))
  have hxpos : 0 < x := hT.trans_le hx.1
  have hclampMem (y : ℝ) : clampShift y ∈ Icc (0 : ℝ) H := by
    constructor
    · exact le_max_left _ _
    · exact max_le hH (min_le_left _ _)
  have hclampContinuous : Continuous clampShift := by
    dsimp only [clampShift]
    fun_prop
  have hF : Continuous (Function.uncurry F) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hvpos : 0 < x + clampShift p.1 := by
      linarith [(hclampMem p.1).1]
    have hwpos : 0 < x + clampShift p.2 := by
      linarith [(hclampMem p.2).1]
    have hphase : ContinuousAt
      (fun p : ℝ × ℝ =>
        thetaModel (x + clampShift p.1) -
          thetaModel (x + clampShift p.2) -
          omega * (clampShift p.2 - clampShift p.1)) p := by
      unfold thetaModel
      fun_prop (disch := positivity)
    exact Real.continuous_cos.continuousAt.comp hphase
  have hclampEq {y : ℝ} (hy : y ∈ Icc (0 : ℝ) H) :
      clampShift y = y := by
    simp only [clampShift, min_eq_right hy.2, max_eq_right hy.1]
  have hbound : ∀ v ∈ Icc (0 : ℝ) H, ∀ w ∈ Icc (0 : ℝ) H,
      |F v w - Real.cos
          (thetaLagReferenceFrequency omega x * (w - v))| ≤
        H ^ 2 / (T - H) := by
    intro v hv w hw
    have hphase :
        thetaModel (x + v) - thetaModel (x + w) - omega * (w - v) =
          thetaLagPhase omega (x + v) (w - v) := by
      unfold thetaLagPhase
      congr 2
      congr 1
      ring
    simpa only [F, hclampEq hv, hclampEq hw, hphase] using
      (abs_cos_thetaLagPhase_shift_sub_cos_frozen_le
        omega hT hH hHT hx hv hw)
  have hbudget :=
    MathlibAux.abs_squareIntegral_le_cosine_difference_main_add_uniform_error
      (K := (1 : ℝ)) (epsilon := H ^ 2 / (T - H)) hF hH hfreq
      (fun v hv w hw => by simpa only [one_mul] using hbound v hv w hw)
  have hintegral :
      (∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H,
          Real.cos (thetaLagPhase omega (x + v) (w - v))) =
        ∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, F v w := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc (0 : ℝ) H := by
      simpa [uIcc_of_le hH] using hv
    apply intervalIntegral.integral_congr
    intro w hw
    have hw' : w ∈ Icc (0 : ℝ) H := by
      simpa [uIcc_of_le hH] using hw
    simp only [F, hclampEq hv', hclampEq hw', thetaLagPhase]
    congr 2
    congr 1
    ring
  rw [hintegral]
  simpa only [abs_one, one_mul] using hbudget

private theorem abs_squareIntegral_cos_thetaLagPhase_shift_le_window_sq
    (omega : ℝ) {H x : ℝ}
    (hH : 0 ≤ H) :
    |∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H,
        Real.cos (thetaLagPhase omega (x + v) (w - v))| ≤ H ^ 2 := by
  have hinner (v : ℝ) :
      |∫ w in (0 : ℝ)..H,
          Real.cos (thetaLagPhase omega (x + v) (w - v))| ≤ H := by
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ w in (0 : ℝ)..H,
          Real.cos (thetaLagPhase omega (x + v) (w - v))‖ ≤
          1 * |H - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro w _hw
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one _
      _ = H := by
        rw [sub_zero, abs_of_nonneg hH]
        ring
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H,
        Real.cos (thetaLagPhase omega (x + v) (w - v))‖ ≤
        H * |H - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro v _hv
      rw [Real.norm_eq_abs]
      exact hinner v
    _ = H ^ 2 := by
      rw [sub_zero, abs_of_nonneg hH]
      ring

/-- Stationary-safe square-window cancellation for the actual Hardy lag
phase.  At the unique stationary frequency the trivial square-area bound is
used; all other frequencies receive the reciprocal-square Fourier saving.
The same tangent-line error is retained in both cases, so this statement can
be summed directly with `sum_sq_stationaryMinReciprocalEnvelope_le`. -/
theorem abs_squareIntegral_cos_thetaLagPhase_shift_le_stationaryEnvelope
    (omega : ℝ) {T H x : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hHT : H ≤ T / 2)
    (hx : x ∈ Icc T (2 * T - H)) :
    |∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H,
        Real.cos (thetaLagPhase omega (x + v) (w - v))| ≤
      (MathlibAux.stationaryMinReciprocalEnvelope
          H (-deriv thetaModel x) omega) ^ 2 +
        (H ^ 2 / (T - H)) * H ^ 2 := by
  let xi : ℝ := -deriv thetaModel x
  let c : ℝ := thetaLagReferenceFrequency omega x
  have hTH : 0 < T - H := by linarith
  have hcEq : c = -(omega - xi) := by
    simp only [c, xi, thetaLagReferenceFrequency]
    ring
  have herror : 0 ≤ (H ^ 2 / (T - H)) * H ^ 2 := by
    positivity
  have htrivial :=
    abs_squareIntegral_cos_thetaLagPhase_shift_le_window_sq
      omega (x := x) hH
  by_cases homega : omega = xi
  · have henv :
        MathlibAux.stationaryMinReciprocalEnvelope H xi omega = H := by
      rw [MathlibAux.stationaryMinReciprocalEnvelope, if_pos homega]
    calc
      |∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H,
          Real.cos (thetaLagPhase omega (x + v) (w - v))| ≤ H ^ 2 :=
        htrivial
      _ ≤ H ^ 2 + (H ^ 2 / (T - H)) * H ^ 2 :=
        le_add_of_nonneg_right herror
      _ =
          (MathlibAux.stationaryMinReciprocalEnvelope
              H (-deriv thetaModel x) omega) ^ 2 +
            (H ^ 2 / (T - H)) * H ^ 2 := by
        simpa only [xi] using congrArg
          (fun y : ℝ => y ^ 2 + (H ^ 2 / (T - H)) * H ^ 2) henv.symm
  · have hc : c ≠ 0 := by
      rw [hcEq]
      exact neg_ne_zero.mpr (sub_ne_zero.mpr homega)
    have habs : |c| = |omega - xi| := by
      rw [hcEq, abs_neg]
    by_cases hshort : H ≤ 2 / |omega - xi|
    · have henv :
          MathlibAux.stationaryMinReciprocalEnvelope H xi omega = H := by
        rw [MathlibAux.stationaryMinReciprocalEnvelope, if_neg homega,
          min_eq_left hshort]
      calc
        |∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H,
            Real.cos (thetaLagPhase omega (x + v) (w - v))| ≤ H ^ 2 :=
          htrivial
        _ ≤ H ^ 2 + (H ^ 2 / (T - H)) * H ^ 2 :=
          le_add_of_nonneg_right herror
        _ =
            (MathlibAux.stationaryMinReciprocalEnvelope
                H (-deriv thetaModel x) omega) ^ 2 +
              (H ^ 2 / (T - H)) * H ^ 2 := by
          simpa only [xi] using congrArg
            (fun y : ℝ => y ^ 2 + (H ^ 2 / (T - H)) * H ^ 2) henv.symm
    · have hrecip : 2 / |omega - xi| ≤ H := le_of_not_ge hshort
      have henv :
          MathlibAux.stationaryMinReciprocalEnvelope H xi omega =
            2 / |omega - xi| := by
        rw [MathlibAux.stationaryMinReciprocalEnvelope, if_neg homega,
          min_eq_right hrecip]
      have hfourier :=
        abs_squareIntegral_cos_thetaLagPhase_shift_le
          omega hT hH hHT hx hc
      have hmain : 4 / c ^ 2 = (2 / |omega - xi|) ^ 2 := by
        calc
          4 / c ^ 2 = 4 / |c| ^ 2 := by rw [sq_abs]
          _ = 4 / |omega - xi| ^ 2 := by rw [habs]
          _ = (2 / |omega - xi|) ^ 2 := by ring
      calc
        |∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H,
            Real.cos (thetaLagPhase omega (x + v) (w - v))| ≤
            4 / c ^ 2 + (H ^ 2 / (T - H)) * H ^ 2 := by
          simpa only [c] using hfourier
        _ = (2 / |omega - xi|) ^ 2 +
              (H ^ 2 / (T - H)) * H ^ 2 := by rw [hmain]
        _ =
            (MathlibAux.stationaryMinReciprocalEnvelope
                H (-deriv thetaModel x) omega) ^ 2 +
              (H ^ 2 / (T - H)) * H ^ 2 := by
          simpa only [xi] using congrArg
            (fun y : ℝ => y ^ 2 + (H ^ 2 / (T - H)) * H ^ 2) henv.symm

end HardyTheorem
