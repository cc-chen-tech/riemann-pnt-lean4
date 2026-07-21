import HardyTheorem.HardyPhaseCorrelation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import MathlibAux.RectangularFourierEnvelope

open Complex MeasureTheory Set

namespace HardyTheorem.OscillatoryIntegral

/-- The first-order, constant-frequency approximation to one Hardy-phase
short integral at its left endpoint. -/
noncomputable def hardyPhaseLinearizedShortIntegral
    (n : ℕ) (delta t : ℝ) : ℂ :=
  Complex.exp (I * hardyPhase n t) *
    ∫ v in 0..delta,
      Complex.exp (I * (deriv (hardyPhase n) t * v))

/-- On a positive-height interval the Hardy phase differs from its tangent
line by at most a quadratic error.  The bound is uniform in the Dirichlet
index because the second derivative of the phase is `1 / (2t)`. -/
theorem abs_hardyPhase_linearization_error_le
    {n : ℕ} (hn : n ≠ 0) {T t v : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hv : 0 ≤ v) :
    |hardyPhase n (t + v) - hardyPhase n t -
        deriv (hardyPhase n) t * v| ≤ v ^ 2 / (2 * T) := by
  have ht : 0 < t := hT.trans_le hTt
  have htv : 0 < t + v := by positivity
  have hden : 0 < 2 * Real.pi * (n : ℝ) ^ 2 := by
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    positivity
  have hlogDiff :
      Real.log ((t + v) / (2 * Real.pi * (n : ℝ) ^ 2)) -
          Real.log (t / (2 * Real.pi * (n : ℝ) ^ 2)) =
        Real.log ((t + v) / t) := by
    rw [Real.log_div (ne_of_gt htv) (ne_of_gt hden),
      Real.log_div (ne_of_gt ht) (ne_of_gt hden),
      Real.log_div (ne_of_gt htv) (ne_of_gt ht)]
    ring
  have hratioPos : 0 < (t + v) / t := div_pos htv ht
  have hinvRatioPos : 0 < t / (t + v) := div_pos ht htv
  have hlogUpper : Real.log ((t + v) / t) ≤ v / t := by
    have h := Real.log_le_sub_one_of_pos hratioPos
    convert h using 1 <;> field_simp [ht.ne'] <;> ring
  have hlogLower : v / (t + v) ≤ Real.log ((t + v) / t) := by
    have h := Real.log_le_sub_one_of_pos hinvRatioPos
    rw [Real.log_div (ne_of_gt ht) (ne_of_gt htv)] at h
    have hlogNeg :
        Real.log t - Real.log (t + v) =
          -Real.log ((t + v) / t) := by
      rw [Real.log_div (ne_of_gt htv) (ne_of_gt ht)]
      ring
    have hfrac : t / (t + v) - 1 = -(v / (t + v)) := by
      field_simp [htv.ne']
      ring
    rw [hlogNeg, hfrac] at h
    linarith
  have herror :
      hardyPhase n (t + v) - hardyPhase n t -
          deriv (hardyPhase n) t * v =
        (1 / 2 : ℝ) *
          ((t + v) * Real.log ((t + v) / t) - v) := by
    rw [deriv_hardyPhase hn ht]
    simp only [hardyPhase]
    rw [show Real.log ((t + v) /
          (2 * Real.pi * (n : ℝ) ^ 2)) =
        Real.log (t / (2 * Real.pi * (n : ℝ) ^ 2)) +
          Real.log ((t + v) / t) by linarith [hlogDiff]]
    ring
  have herrorNonneg : 0 ≤
      hardyPhase n (t + v) - hardyPhase n t -
        deriv (hardyPhase n) t * v := by
    rw [herror]
    have hmul := mul_le_mul_of_nonneg_left hlogLower htv.le
    have : v ≤ (t + v) * Real.log ((t + v) / t) := by
      calc
        v = (t + v) * (v / (t + v)) := by field_simp [htv.ne']
        _ ≤ (t + v) * Real.log ((t + v) / t) := hmul
    nlinarith
  rw [abs_of_nonneg herrorNonneg, herror]
  have hmulUpper := mul_le_mul_of_nonneg_left hlogUpper htv.le
  calc
    (1 / 2 : ℝ) * ((t + v) * Real.log ((t + v) / t) - v) ≤
        (1 / 2 : ℝ) * ((t + v) * (v / t) - v) := by gcongr
    _ = v ^ 2 / (2 * t) := by field_simp [ht.ne']; ring
    _ ≤ v ^ 2 / (2 * T) := by
      exact div_le_div_of_nonneg_left (sq_nonneg v)
        (by positivity) (mul_le_mul_of_nonneg_left hTt (by norm_num))

private theorem norm_exp_I_mul_real_sub_le
    (x y : ℝ) :
    ‖Complex.exp (I * x) - Complex.exp (I * y)‖ ≤ |x - y| := by
  have hfactor :
      Complex.exp (I * x) - Complex.exp (I * y) =
        Complex.exp (I * y) * (Complex.exp (I * (x - y)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfactor, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa only [Complex.ofReal_sub, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))

/-- Replacing the Hardy phase by its tangent line over a short window costs
`O(delta^3 / T)` in the integrated phase. -/
theorem norm_hardyPhaseShortIntegral_sub_linearized_le
    {n : ℕ} (hn : n ≠ 0) {T t delta : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hdelta : 0 ≤ delta) :
    ‖hardyPhaseShortIntegral n delta t -
        hardyPhaseLinearizedShortIntegral n delta t‖ ≤
      delta ^ 3 / (2 * T) := by
  let F : ℝ → ℂ := fun v =>
    Complex.exp (I * hardyPhase n (t + v))
  let G : ℝ → ℂ := fun v =>
    Complex.exp (I *
      (hardyPhase n t + deriv (hardyPhase n) t * v))
  have hFint : IntervalIntegrable F volume 0 delta := by
    apply ContinuousOn.intervalIntegrable_of_Icc hdelta
    intro v hv
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.cexp
    apply ContinuousAt.mul continuousAt_const
    apply Complex.continuous_ofReal.continuousAt.comp
    exact (contDiffAt_hardyPhase_two hn
      ((hT.trans_le hTt).trans_le (by linarith [hv.1]))).continuousAt.comp
        (continuousAt_const.add continuousAt_id)
  have hGint : IntervalIntegrable G volume 0 delta := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hidentity :
      hardyPhaseShortIntegral n delta t -
          hardyPhaseLinearizedShortIntegral n delta t =
        ∫ v in 0..delta, F v - G v := by
    dsimp only [hardyPhaseShortIntegral,
      hardyPhaseLinearizedShortIntegral, F, G]
    have hlinear : ∀ v : ℝ,
        Complex.exp (I * hardyPhase n t) *
            Complex.exp (I * (deriv (hardyPhase n) t * v)) =
          Complex.exp (I *
            (hardyPhase n t + deriv (hardyPhase n) t * v)) := by
      intro v
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      (∫ v in 0..delta, Complex.exp (I * hardyPhase n (t + v))) -
          Complex.exp (I * hardyPhase n t) *
            ∫ v in 0..delta,
              Complex.exp (I * (deriv (hardyPhase n) t * v)) =
        (∫ v in 0..delta, F v) - ∫ v in 0..delta, G v := by
          congr 1
          calc
            Complex.exp (I * hardyPhase n t) *
                ∫ v in 0..delta,
                  Complex.exp (I * (deriv (hardyPhase n) t * v)) =
              ∫ v in 0..delta,
                Complex.exp (I * hardyPhase n t) *
                  Complex.exp (I * (deriv (hardyPhase n) t * v)) :=
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
      (hardyPhase n (t + v))
      (hardyPhase n t + deriv (hardyPhase n) t * v)
    calc
      ‖Complex.exp (I * hardyPhase n (t + v)) -
          Complex.exp (I *
            (hardyPhase n t + deriv (hardyPhase n) t * v))‖ ≤
          |hardyPhase n (t + v) - hardyPhase n t -
            deriv (hardyPhase n) t * v| := by
        rw [show hardyPhase n (t + v) - hardyPhase n t -
            deriv (hardyPhase n) t * v =
          hardyPhase n (t + v) -
            (hardyPhase n t + deriv (hardyPhase n) t * v) by ring]
        simpa only [Complex.ofReal_add, Complex.ofReal_mul] using hexp
      _ ≤ v ^ 2 / (2 * T) :=
        abs_hardyPhase_linearization_error_le hn hT hTt hv.1
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

/-- The tangent-line model has the rectangular-window length bound at every
frequency, including a stationary phase. -/
theorem norm_hardyPhaseLinearizedShortIntegral_le_length
    {n : ℕ} {delta t : ℝ} (hdelta : 0 ≤ delta) :
    ‖hardyPhaseLinearizedShortIntegral n delta t‖ ≤ delta := by
  rw [hardyPhaseLinearizedShortIntegral, norm_mul,
    Complex.norm_exp_I_mul_ofReal, one_mul]
  exact MathlibAux.norm_integral_cexp_linear_le_length hdelta

/-- Away from stationary phase, the tangent-line model retains the
short-window reciprocal-frequency envelope. -/
theorem norm_hardyPhaseLinearizedShortIntegral_le_min
    {n : ℕ} {delta t : ℝ} (hdelta : 0 ≤ delta)
    (hfreq : deriv (hardyPhase n) t ≠ 0) :
    ‖hardyPhaseLinearizedShortIntegral n delta t‖ ≤
      min delta (2 / |deriv (hardyPhase n) t|) := by
  rw [hardyPhaseLinearizedShortIntegral, norm_mul,
    Complex.norm_exp_I_mul_ofReal, one_mul]
  exact MathlibAux.norm_integral_cexp_linear_le_min hdelta hfreq

/-- The true Hardy-phase short integral retains the reciprocal-frequency
envelope up to the uniform tangent-line error. -/
theorem norm_hardyPhaseShortIntegral_le_min_add_linearization_error
    {n : ℕ} (hn : n ≠ 0) {T t delta : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hdelta : 0 ≤ delta)
    (hfreq : deriv (hardyPhase n) t ≠ 0) :
    ‖hardyPhaseShortIntegral n delta t‖ ≤
      min delta (2 / |deriv (hardyPhase n) t|) +
        delta ^ 3 / (2 * T) := by
  calc
    ‖hardyPhaseShortIntegral n delta t‖ ≤
        ‖hardyPhaseShortIntegral n delta t -
          hardyPhaseLinearizedShortIntegral n delta t‖ +
          ‖hardyPhaseLinearizedShortIntegral n delta t‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ delta ^ 3 / (2 * T) +
        min delta (2 / |deriv (hardyPhase n) t|) :=
      add_le_add
        (norm_hardyPhaseShortIntegral_sub_linearized_le hn hT hTt hdelta)
        (norm_hardyPhaseLinearizedShortIntegral_le_min hdelta hfreq)
    _ = min delta (2 / |deriv (hardyPhase n) t|) +
        delta ^ 3 / (2 * T) := by ring

/-- At a stationary frequency the true short integral is still controlled by
its window length plus the tangent-line error. -/
theorem norm_hardyPhaseShortIntegral_le_length_add_linearization_error
    {n : ℕ} (hn : n ≠ 0) {T t delta : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hdelta : 0 ≤ delta) :
    ‖hardyPhaseShortIntegral n delta t‖ ≤
      delta + delta ^ 3 / (2 * T) := by
  calc
    ‖hardyPhaseShortIntegral n delta t‖ ≤
        ‖hardyPhaseShortIntegral n delta t -
          hardyPhaseLinearizedShortIntegral n delta t‖ +
          ‖hardyPhaseLinearizedShortIntegral n delta t‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ delta ^ 3 / (2 * T) + delta :=
      add_le_add
        (norm_hardyPhaseShortIntegral_sub_linearized_le hn hT hTt hdelta)
        (norm_hardyPhaseLinearizedShortIntegral_le_length hdelta)
    _ = delta + delta ^ 3 / (2 * T) := by ring

end HardyTheorem.OscillatoryIntegral
