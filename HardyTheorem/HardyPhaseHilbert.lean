import HardyTheorem.HardyPhaseSecondMoment
import MathlibAux.LogarithmicHilbertIntegrationByParts

open Complex MeasureTheory Set

namespace HardyTheorem

private theorem hardyPhase_eq_thetaModel_sub
    {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t) :
    OscillatoryIntegral.hardyPhase n t =
      thetaModel t - t * Real.log n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlogSq : Real.log ((n : ℝ) ^ 2) = 2 * Real.log n := by
    rw [Real.log_pow]
    norm_num
  have hlogDiv :
      Real.log (t / (2 * Real.pi * ((n : ℝ) ^ 2))) =
        Real.log (t / (2 * Real.pi)) - 2 * Real.log n := by
    rw [show t / (2 * Real.pi * ((n : ℝ) ^ 2)) =
        (t / (2 * Real.pi)) / ((n : ℝ) ^ 2) by ring]
    rw [Real.log_div (by positivity) (by positivity), hlogSq]
  rw [OscillatoryIntegral.hardyPhase, thetaModel, hlogDiv]
  ring

/-- The common nonlinear phase left after the logarithmic Dirichlet
frequencies are separated from a shifted Hardy correlation. -/
noncomputable def hardyCorrelationAmplitude (v w t : ℝ) : ℂ :=
  Complex.exp (I *
    ((thetaModel (t + v) - thetaModel (t + w) : ℝ) : ℂ))

private noncomputable def hardyShiftTwist
    (coeff : ℕ → ℂ) (shift : ℝ) (n : ℕ) : ℂ :=
  coeff n * Complex.exp (-I * ((Real.log n * shift : ℝ) : ℂ))

/-- The off-diagonal correlation form for a dyadic block of Hardy phases. -/
noncomputable def hardyPhaseCorrelationOffDiagonal
    (s : Finset ℕ) (coeff : ℕ → ℂ) (v w t : ℝ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s,
    if m = n then 0
    else (starRingEnd ℂ) (coeff n) * coeff m *
      Complex.exp (I * OscillatoryIntegral.hardyPhaseCorrelation m n v w t)

/-- A Hardy correlation is a common nonlinear amplitude times an ordinary
negative logarithmic-frequency off-diagonal form. -/
theorem hardyPhaseCorrelationOffDiagonal_eq_amplitude_mul_logOffDiagonal
    (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0)
    {v w t : ℝ} (htv : 0 < t + v) (htw : 0 < t + w) :
    hardyPhaseCorrelationOffDiagonal s coeff v w t =
      hardyCorrelationAmplitude v w t *
        MathlibAux.logOffDiagonalForm s
          (hardyShiftTwist coeff w) (hardyShiftTwist coeff v) (-t) := by
  unfold hardyPhaseCorrelationOffDiagonal MathlibAux.logOffDiagonalForm
    MathlibAux.logOffDiagonalTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmn : m = n
  · simp [hmn]
  · simp only [hmn, ↓reduceIte]
    unfold OscillatoryIntegral.hardyPhaseCorrelation
    rw [hardyPhase_eq_thetaModel_sub (hpositive m hm) htv,
      hardyPhase_eq_thetaModel_sub (hpositive n hn) htw]
    unfold hardyCorrelationAmplitude hardyShiftTwist
    simp only [map_mul, ← Complex.exp_conj, map_neg, conj_I, conj_ofReal]
    have hexp :
        Complex.exp (I *
            ((((thetaModel (t + v) - (t + v) * Real.log m) -
              (thetaModel (t + w) - (t + w) * Real.log n)) : ℝ) : ℂ)) =
          Complex.exp (I *
              ((thetaModel (t + v) - thetaModel (t + w) : ℝ) : ℂ)) *
            Complex.exp (-(-I * ((Real.log n * w : ℝ) : ℂ))) *
            Complex.exp (-I * ((Real.log m * v : ℝ) : ℂ)) *
            Complex.exp
              (I * (((Real.log m : ℝ) : ℂ) -
                ((Real.log n : ℝ) : ℂ)) * ((-t : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring

private noncomputable def hardyCorrelationAmplitudeVelocity
    (v w t : ℝ) : ℝ :=
  (1 / 2) * (Real.log (t + v) - Real.log (t + w))

private noncomputable def hardyCorrelationAmplitudeDerivative
    (v w t : ℝ) : ℂ :=
  hardyCorrelationAmplitude v w t *
    (I * ((hardyCorrelationAmplitudeVelocity v w t : ℝ) : ℂ))

private theorem hasDerivAt_hardyCorrelationAmplitude
    {v w t : ℝ} (htv : 0 < t + v) (htw : 0 < t + w) :
    HasDerivAt (hardyCorrelationAmplitude v w)
      (hardyCorrelationAmplitudeDerivative v w t) t := by
  have htheta (shift : ℝ) (hpos : 0 < t + shift) :
      HasDerivAt (fun x : ℝ => thetaModel (x + shift))
        ((1 / 2 : ℝ) * Real.log ((t + shift) / (2 * Real.pi))) t := by
    have hdiff : DifferentiableAt ℝ thetaModel (t + shift) := by
      change DifferentiableAt ℝ
        (fun y : ℝ =>
          y / 2 * Real.log (y / (2 * Real.pi)) - y / 2 - Real.pi / 8)
        (t + shift)
      fun_prop (disch := positivity)
    have hout := hdiff.hasDerivAt
    rw [deriv_thetaModel hpos] at hout
    simpa only [Function.comp_def, id_eq, mul_one] using
      hout.comp t ((hasDerivAt_id t).add_const shift)
  have hphase := (htheta v htv).sub (htheta w htw)
  have hvelocity :
      (1 / 2 : ℝ) * Real.log ((t + v) / (2 * Real.pi)) -
          (1 / 2 : ℝ) * Real.log ((t + w) / (2 * Real.pi)) =
        hardyCorrelationAmplitudeVelocity v w t := by
    rw [Real.log_div (ne_of_gt htv) (by positivity),
      Real.log_div (ne_of_gt htw) (by positivity)]
    unfold hardyCorrelationAmplitudeVelocity
    ring
  rw [hvelocity] at hphase
  have hcast : HasDerivAt
      (fun x : ℝ =>
        ((thetaModel (x + v) - thetaModel (x + w) : ℝ) : ℂ))
      ((hardyCorrelationAmplitudeVelocity v w t : ℝ) : ℂ) t := by
    have hofReal : HasDerivAt (fun x : ℝ => (x : ℂ)) 1
        (thetaModel (t + v) - thetaModel (t + w)) :=
      Complex.ofRealCLM.hasDerivAt
    have hcomp := hofReal.scomp t hphase
    have hscalar :
        hardyCorrelationAmplitudeVelocity v w t • (1 : ℂ) =
          ((hardyCorrelationAmplitudeVelocity v w t : ℝ) : ℂ) := by
      rw [Complex.real_smul]
      simp
    simpa only [Function.comp_def, Pi.sub_apply] using
      hcomp.congr_deriv hscalar
  have harg := hcast.const_mul I
  have hexp := harg.cexp
  simpa only [hardyCorrelationAmplitude,
    hardyCorrelationAmplitudeDerivative] using hexp

private theorem continuousAt_hardyCorrelationAmplitudeDerivative
    {v w t : ℝ} (htv : 0 < t + v) (htw : 0 < t + w) :
    ContinuousAt (hardyCorrelationAmplitudeDerivative v w) t := by
  have hamp :=
    (hasDerivAt_hardyCorrelationAmplitude htv htw).continuousAt
  have hvel : ContinuousAt (hardyCorrelationAmplitudeVelocity v w) t := by
    unfold hardyCorrelationAmplitudeVelocity
    fun_prop (disch := positivity)
  unfold hardyCorrelationAmplitudeDerivative
  exact hamp.mul
    (continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp hvel))

private theorem normSq_hardyShiftTwist
    (coeff : ℕ → ℂ) (shift : ℝ) (n : ℕ) :
    Complex.normSq (hardyShiftTwist coeff shift n) =
      Complex.normSq (coeff n) := by
  unfold hardyShiftTwist
  rw [Complex.normSq_mul]
  have hexp : Complex.normSq
      (Complex.exp (-I * ((Real.log n * shift : ℝ) : ℂ))) = 1 := by
    rw [show -I * ((Real.log n * shift : ℝ) : ℂ) =
        I * ((-(Real.log n * shift) : ℝ) : ℂ) by
      push_cast
      ring]
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_I_mul_ofReal]
    norm_num
  rw [hexp, mul_one]

private theorem norm_hardyCorrelationAmplitudeDerivative_le
    {T v w t : ℝ} (hT : 0 < T) (ht : T ≤ t) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    ‖hardyCorrelationAmplitudeDerivative v w t‖ ≤
      |v - w| / (2 * T) := by
  have htv : T ≤ t + v := by linarith
  have htw : T ≤ t + w := by linarith
  have hlog := OscillatoryIntegral.abs_log_sub_log_le_div hT htw htv
  unfold hardyCorrelationAmplitudeDerivative
    hardyCorrelationAmplitudeVelocity
  rw [norm_mul, norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]
  have hamp : ‖hardyCorrelationAmplitude v w t‖ = 1 := by
    unfold hardyCorrelationAmplitude
    exact Complex.norm_exp_I_mul_ofReal _
  rw [hamp, one_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2) * |Real.log (t + v) - Real.log (t + w)| ≤
        (1 / 2) * (|(t + v) - (t + w)| / T) := by gcongr
    _ = |v - w| / (2 * T) := by
      rw [show (t + v) - (t + w) = v - w by ring]
      field_simp

private theorem integral_norm_hardyCorrelationAmplitudeDerivative_le
    {T delta v w : ℝ} (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hroom : delta ≤ T) (hv : v ∈ Set.Icc 0 delta)
    (hw : w ∈ Set.Icc 0 delta) :
    (∫ t in T..2 * T - delta,
      ‖hardyCorrelationAmplitudeDerivative v w t‖) ≤ delta / 2 := by
  have hab : T ≤ 2 * T - delta := by linarith
  let K : ℝ := delta / (2 * T)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hdiff : |v - w| ≤ delta := by
    rw [abs_le]
    constructor <;> linarith [hv.1, hv.2, hw.1, hw.2]
  have hpoint : ∀ t ∈ Set.Icc T (2 * T - delta),
      ‖hardyCorrelationAmplitudeDerivative v w t‖ ≤ K := by
    intro t ht
    calc
      ‖hardyCorrelationAmplitudeDerivative v w t‖ ≤
          |v - w| / (2 * T) :=
        norm_hardyCorrelationAmplitudeDerivative_le hT ht.1 hv.1 hw.1
      _ ≤ delta / (2 * T) :=
        div_le_div_of_nonneg_right hdiff (by positivity)
      _ = K := rfl
  have hderivInt : IntervalIntegrable
      (fun t => ‖hardyCorrelationAmplitudeDerivative v w t‖)
      volume T (2 * T - delta) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact (continuousAt_hardyCorrelationAmplitudeDerivative
      (by linarith [hT, ht.1, hv.1])
      (by linarith [hT, ht.1, hw.1])).norm.continuousWithinAt
  have hconstInt : IntervalIntegrable (fun _t : ℝ => K)
      volume T (2 * T - delta) := continuous_const.intervalIntegrable _ _
  calc
    (∫ t in T..2 * T - delta,
        ‖hardyCorrelationAmplitudeDerivative v w t‖) ≤
        ∫ _t in T..2 * T - delta, K :=
      intervalIntegral.integral_mono_on hab hderivInt hconstInt hpoint
    _ = K * (T - delta) := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring
    _ ≤ delta / 2 := by
      dsimp only [K]
      rw [div_mul_eq_mul_div]
      rw [div_le_iff₀ (mul_pos (by norm_num) hT)]
      nlinarith

/-- On one dyadic index block, the full off-diagonal Hardy correlation has
the expected `O(M)` bound uniformly over both short-window shifts. -/
theorem norm_integral_hardyPhaseCorrelationOffDiagonal_dyadic_le
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hlower : ∀ n ∈ s, M ≤ n) (hupper : ∀ n ∈ s, n ≤ 2 * M)
    {T delta v w : ℝ} (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hroom : delta ≤ T) (hv : v ∈ Set.Icc 0 delta)
    (hw : w ∈ Set.Icc 0 delta) :
    ‖∫ t in T..2 * T - delta,
        hardyPhaseCorrelationOffDiagonal s coeff v w t‖ ≤
      (2 + delta / 2) * ((5 * Real.pi + 3) * M *
        (2 * ∑ n ∈ s, Complex.normSq (coeff n))) := by
  have hab : T ≤ 2 * T - delta := by linarith
  have hpositive : ∀ n ∈ s, n ≠ 0 := by
    intro n hn hzero
    subst n
    have := hlower 0 hn
    omega
  let A : ℝ → ℂ := hardyCorrelationAmplitude v w
  let A' : ℝ → ℂ := hardyCorrelationAmplitudeDerivative v w
  have hA : ∀ t ∈ Set.uIcc T (2 * T - delta),
      HasDerivAt A (A' t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact hasDerivAt_hardyCorrelationAmplitude
      (by linarith [hT, ht.1, hv.1]) (by linarith [hT, ht.1, hw.1])
  have hAend : ‖A T‖ ≤ 1 ∧ ‖A (2 * T - delta)‖ ≤ 1 := by
    constructor <;> dsimp only [A, hardyCorrelationAmplitude] <;>
      rw [Complex.norm_exp_I_mul_ofReal]
  have hA'int : IntervalIntegrable A' volume T (2 * T - delta) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact (continuousAt_hardyCorrelationAmplitudeDerivative
      (by linarith [hT, ht.1, hv.1])
      (by linarith [hT, ht.1, hw.1])).continuousWithinAt
  have hvariation : (∫ t in T..2 * T - delta, ‖A' t‖) ≤ delta / 2 :=
    integral_norm_hardyCorrelationAmplitudeDerivative_le
      hT hdelta hroom hv hw
  have hgeneric := MathlibAux.norm_integral_amplitude_mul_logOffDiagonalForm_neg_le
    hM s (hardyShiftTwist coeff w) (hardyShiftTwist coeff v)
      hlower hupper hab hA hAend hA'int hvariation
  calc
    ‖∫ t in T..2 * T - delta,
        hardyPhaseCorrelationOffDiagonal s coeff v w t‖ =
        ‖∫ t in T..2 * T - delta,
          A t * MathlibAux.logOffDiagonalForm s
            (hardyShiftTwist coeff w) (hardyShiftTwist coeff v) (-t)‖ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc T (2 * T - delta) := by
        simpa [Set.uIcc_of_le hab] using ht
      exact hardyPhaseCorrelationOffDiagonal_eq_amplitude_mul_logOffDiagonal
        s coeff hpositive (by linarith [hT, ht'.1, hv.1])
          (by linarith [hT, ht'.1, hw.1])
    _ ≤ (2 + delta / 2) * ((5 * Real.pi + 3) * M *
        ((∑ n ∈ s, Complex.normSq (hardyShiftTwist coeff w n)) +
          ∑ n ∈ s, Complex.normSq (hardyShiftTwist coeff v n))) := hgeneric
    _ = (2 + delta / 2) * ((5 * Real.pi + 3) * M *
        (2 * ∑ n ∈ s, Complex.normSq (coeff n))) := by
      simp only [normSq_hardyShiftTwist]
      ring

end HardyTheorem
