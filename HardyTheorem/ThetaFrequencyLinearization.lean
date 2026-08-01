import HardyTheorem.HardyPhaseLinearization
import HardyTheorem.VerticalGammaAsymptotic

open Complex MeasureTheory Set

namespace HardyTheorem

/-- The short-window integral of the common theta phase with an arbitrary
additional real frequency.  Collected rational Selberg frequencies have
exactly this form. -/
noncomputable def thetaFrequencyShortIntegral
    (omega delta t : ℝ) : ℂ :=
  ∫ v in 0..delta,
    Complex.exp
      (I * ((thetaModel (t + v) + omega * (t + v) : ℝ) : ℂ))

/-- The first-order, constant-frequency approximation to a theta-frequency
short integral at its left endpoint. -/
noncomputable def thetaFrequencyLinearizedShortIntegral
    (omega delta t : ℝ) : ℂ :=
  Complex.exp (I * ((thetaModel t + omega * t : ℝ) : ℂ)) *
    ∫ v in 0..delta,
      Complex.exp
        (I * (((deriv thetaModel t + omega) * v : ℝ) : ℂ))

/-- A stationary-safe short-window envelope.  At exact stationary phase it
uses the window length; otherwise it retains reciprocal-frequency decay with
the tangent-line error. -/
noncomputable def thetaFrequencyShortIntegralEnvelope
    (omega T delta t : ℝ) : ℝ :=
  if deriv thetaModel t + omega = 0 then
    delta
  else
    min delta (2 / |deriv thetaModel t + omega|) +
      delta ^ 3 / (2 * T)

/-- Every theta-frequency integrand has unit norm, so the exact short
integral is bounded by the window length even at a stationary frequency. -/
theorem norm_thetaFrequencyShortIntegral_le_length
    (omega : ℝ) {delta t : ℝ} (hdelta : 0 ≤ delta) :
    ‖thetaFrequencyShortIntegral omega delta t‖ ≤ delta := by
  dsimp only [thetaFrequencyShortIntegral]
  calc
    ‖∫ v in 0..delta,
        Complex.exp
          (I * ((thetaModel (t + v) + omega * (t + v) : ℝ) : ℂ))‖ ≤
        1 * |delta - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro v _hv
      exact le_of_eq
        (Complex.norm_exp_I_mul_ofReal
          (thetaModel (t + v) + omega * (t + v)))
    _ = delta := by
      rw [sub_zero, abs_of_nonneg hdelta, one_mul]

private theorem thetaModel_eq_hardyPhase_one :
    thetaModel = OscillatoryIntegral.hardyPhase 1 := by
  funext t
  simp [thetaModel, OscillatoryIntegral.hardyPhase]
  ring

private theorem abs_thetaFrequency_linearization_error_le
    (omega : ℝ) {T t v : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hv : 0 ≤ v) :
    |(thetaModel (t + v) + omega * (t + v)) -
        (thetaModel t + omega * t) -
        (deriv thetaModel t + omega) * v| ≤
      v ^ 2 / (2 * T) := by
  have hbase :=
    OscillatoryIntegral.abs_hardyPhase_linearization_error_le
      (n := 1) (by norm_num) hT hTt hv
  rw [thetaModel_eq_hardyPhase_one]
  have hphase :
      OscillatoryIntegral.hardyPhase 1 (t + v) + omega * (t + v) -
          (OscillatoryIntegral.hardyPhase 1 t + omega * t) -
          (deriv (OscillatoryIntegral.hardyPhase 1) t + omega) * v =
        OscillatoryIntegral.hardyPhase 1 (t + v) -
          OscillatoryIntegral.hardyPhase 1 t -
          deriv (OscillatoryIntegral.hardyPhase 1) t * v := by
    ring
  rw [hphase]
  exact hbase

private theorem norm_exp_I_mul_real_sub_le
    (x y : ℝ) :
    ‖Complex.exp (I * x) - Complex.exp (I * y)‖ ≤ |x - y| := by
  have hfactor :
      Complex.exp (I * x) - Complex.exp (I * y) =
        Complex.exp (I * y) * (Complex.exp (I * (x - y)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    ring
  rw [hfactor, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa only [Complex.ofReal_sub, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))

/-- Adding an arbitrary linear frequency does not change the theta-phase
tangent-line error, so the integrated error remains `O(delta^3 / T)`. -/
theorem norm_thetaFrequencyShortIntegral_sub_linearized_le
    (omega : ℝ) {T t delta : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hdelta : 0 ≤ delta) :
    ‖thetaFrequencyShortIntegral omega delta t -
        thetaFrequencyLinearizedShortIntegral omega delta t‖ ≤
      delta ^ 3 / (2 * T) := by
  let F : ℝ → ℂ := fun v =>
    Complex.exp
      (I * ((thetaModel (t + v) + omega * (t + v) : ℝ) : ℂ))
  let G : ℝ → ℂ := fun v =>
    Complex.exp
      (I * (((thetaModel t + omega * t) +
        (deriv thetaModel t + omega) * v : ℝ) : ℂ))
  have hFint : IntervalIntegrable F volume 0 delta := by
    apply ContinuousOn.intervalIntegrable_of_Icc hdelta
    intro v hv
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.cexp
    apply ContinuousAt.mul continuousAt_const
    apply Complex.continuous_ofReal.continuousAt.comp
    have htv : 0 < t + v := by
      exact (hT.trans_le hTt).trans_le (by linarith [hv.1])
    have htheta :
        ContinuousAt (fun x : ℝ => thetaModel (t + x)) v := by
      rw [thetaModel_eq_hardyPhase_one]
      exact
        (OscillatoryIntegral.contDiffAt_hardyPhase_two
          (n := 1) (by norm_num) htv).continuousAt.comp
            (continuousAt_const.add continuousAt_id)
    exact htheta.add
      (continuousAt_const.mul
        (continuousAt_const.add continuousAt_id))
  have hGint : IntervalIntegrable G volume 0 delta := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hidentity :
      thetaFrequencyShortIntegral omega delta t -
          thetaFrequencyLinearizedShortIntegral omega delta t =
        ∫ v in 0..delta, F v - G v := by
    dsimp only [thetaFrequencyShortIntegral,
      thetaFrequencyLinearizedShortIntegral, F, G]
    have hlinear : ∀ v : ℝ,
        Complex.exp
            (I * ((thetaModel t + omega * t : ℝ) : ℂ)) *
            Complex.exp
              (I * (((deriv thetaModel t + omega) * v : ℝ) : ℂ)) =
          Complex.exp
            (I * (((thetaModel t + omega * t) +
              (deriv thetaModel t + omega) * v : ℝ) : ℂ)) := by
      intro v
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      (∫ v in 0..delta,
          Complex.exp
            (I * ((thetaModel (t + v) +
              omega * (t + v) : ℝ) : ℂ))) -
          Complex.exp
              (I * ((thetaModel t + omega * t : ℝ) : ℂ)) *
            ∫ v in 0..delta,
              Complex.exp
                (I * (((deriv thetaModel t + omega) * v : ℝ) : ℂ)) =
        (∫ v in 0..delta, F v) - ∫ v in 0..delta, G v := by
          congr 1
          calc
            Complex.exp
                (I * ((thetaModel t + omega * t : ℝ) : ℂ)) *
                ∫ v in 0..delta,
                  Complex.exp
                    (I *
                      (((deriv thetaModel t + omega) * v : ℝ) : ℂ)) =
              ∫ v in 0..delta,
                Complex.exp
                    (I * ((thetaModel t + omega * t : ℝ) : ℂ)) *
                  Complex.exp
                    (I *
                      (((deriv thetaModel t + omega) * v : ℝ) : ℂ)) :=
                (intervalIntegral.integral_const_mul _ _).symm
            _ = ∫ v in 0..delta, G v := by
              apply intervalIntegral.integral_congr
              intro v _hv
              exact hlinear v
      _ = ∫ v in 0..delta, F v - G v :=
        (intervalIntegral.integral_sub hFint hGint).symm
  rw [hidentity]
  have hpoint : ∀ v ∈ Set.Icc (0 : ℝ) delta,
      ‖F v - G v‖ ≤ delta ^ 2 / (2 * T) := by
    intro v hv
    dsimp only [F, G]
    have hexp := norm_exp_I_mul_real_sub_le
      (thetaModel (t + v) + omega * (t + v))
      ((thetaModel t + omega * t) +
        (deriv thetaModel t + omega) * v)
    calc
      ‖Complex.exp
            (I * ((thetaModel (t + v) +
              omega * (t + v) : ℝ) : ℂ)) -
          Complex.exp
            (I * (((thetaModel t + omega * t) +
              (deriv thetaModel t + omega) * v : ℝ) : ℂ))‖ ≤
          |(thetaModel (t + v) + omega * (t + v)) -
            (thetaModel t + omega * t) -
            (deriv thetaModel t + omega) * v| := by
        rw [show
          (thetaModel (t + v) + omega * (t + v)) -
              (thetaModel t + omega * t) -
              (deriv thetaModel t + omega) * v =
            (thetaModel (t + v) + omega * (t + v)) -
              ((thetaModel t + omega * t) +
                (deriv thetaModel t + omega) * v) by ring]
        simpa only [Complex.ofReal_add, Complex.ofReal_mul] using hexp
      _ ≤ v ^ 2 / (2 * T) :=
        abs_thetaFrequency_linearization_error_le omega hT hTt hv.1
      _ ≤ delta ^ 2 / (2 * T) := by
        exact div_le_div_of_nonneg_right
          ((sq_le_sq₀ hv.1 hdelta).2 hv.2) (by positivity)
  calc
    ‖∫ v in 0..delta, F v - G v‖ ≤
        (delta ^ 2 / (2 * T)) * |delta - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro v hv
      apply hpoint
      rw [Set.uIoc_of_le hdelta] at hv
      exact ⟨hv.1.le, hv.2⟩
    _ = delta ^ 3 / (2 * T) := by
      rw [sub_zero, abs_of_nonneg hdelta]
      ring

/-- Away from stationary phase, the tangent-line model retains the
rectangular-window reciprocal-frequency envelope. -/
theorem norm_thetaFrequencyLinearizedShortIntegral_le_min
    (omega : ℝ) {delta t : ℝ} (hdelta : 0 ≤ delta)
    (hfreq : deriv thetaModel t + omega ≠ 0) :
    ‖thetaFrequencyLinearizedShortIntegral omega delta t‖ ≤
      min delta (2 / |deriv thetaModel t + omega|) := by
  rw [thetaFrequencyLinearizedShortIntegral, norm_mul,
    Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa only [Complex.ofReal_mul] using
    MathlibAux.norm_integral_cexp_linear_le_min hdelta hfreq

/-- The true theta-frequency short integral retains the reciprocal-frequency
envelope up to the uniform tangent-line error. -/
theorem norm_thetaFrequencyShortIntegral_le_min_add_linearization_error
    (omega : ℝ) {T t delta : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hdelta : 0 ≤ delta)
    (hfreq : deriv thetaModel t + omega ≠ 0) :
    ‖thetaFrequencyShortIntegral omega delta t‖ ≤
      min delta (2 / |deriv thetaModel t + omega|) +
        delta ^ 3 / (2 * T) := by
  calc
    ‖thetaFrequencyShortIntegral omega delta t‖ ≤
        ‖thetaFrequencyShortIntegral omega delta t -
          thetaFrequencyLinearizedShortIntegral omega delta t‖ +
          ‖thetaFrequencyLinearizedShortIntegral omega delta t‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ delta ^ 3 / (2 * T) +
        min delta (2 / |deriv thetaModel t + omega|) :=
      add_le_add
        (norm_thetaFrequencyShortIntegral_sub_linearized_le
          omega hT hTt hdelta)
        (norm_thetaFrequencyLinearizedShortIntegral_le_min
          omega hdelta hfreq)
    _ = min delta (2 / |deriv thetaModel t + omega|) +
        delta ^ 3 / (2 * T) := by ring

/-- The stationary-safe envelope controls every arbitrary-frequency theta
short integral without a per-frequency nonvanishing hypothesis. -/
theorem norm_thetaFrequencyShortIntegral_le_envelope
    (omega : ℝ) {T t delta : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hdelta : 0 ≤ delta) :
    ‖thetaFrequencyShortIntegral omega delta t‖ ≤
      thetaFrequencyShortIntegralEnvelope omega T delta t := by
  unfold thetaFrequencyShortIntegralEnvelope
  split_ifs with hfreq
  · exact norm_thetaFrequencyShortIntegral_le_length omega hdelta
  · exact
      norm_thetaFrequencyShortIntegral_le_min_add_linearization_error
        omega hT hTt hdelta hfreq

end HardyTheorem
