import HardyTheorem.HardyPhaseWindowCoeffDerivative
import HardyTheorem.SelbergSqrtZetaSignedCollectedCorrelation

/-!
# Uniform second-derivative control of the signed pseudo-correlation phase

The pseudo-correlation carries the sum of two Hardy phases rather than their
difference. Its second derivative is therefore positive and of order `1 / T`
throughout the dyadic height box. The second-derivative oscillatory estimate
then gives a uniform `O(sqrt T)` bound, including frequencies at which the
first derivative may vanish.
-/

open Complex MeasureTheory Set

namespace HardyTheorem

/-- The real phase of one collected pseudo-correlation summand. -/
noncomputable def selbergSqrtZetaSignedPseudoPhase
    (omega nu v w : ℝ) (t : ℝ) : ℝ :=
  OscillatoryIntegral.hardyPhase 1 (t + v) +
    OscillatoryIntegral.hardyPhase 1 (t + w) +
      (omega + nu) * t

/-- The signed pseudo phase is twice continuously differentiable wherever
both shifted heights are positive. -/
theorem contDiffAt_selbergSqrtZetaSignedPseudoPhase_two
    {omega nu v w t : ℝ} (htv : 0 < t + v) (htw : 0 < t + w) :
    ContDiffAt ℝ 2
      (selbergSqrtZetaSignedPseudoPhase omega nu v w) t := by
  have hvShift : ContDiffAt ℝ 2 (fun x : ℝ => x + v) t :=
    contDiffAt_id.add contDiffAt_const
  have hwShift : ContDiffAt ℝ 2 (fun x : ℝ => x + w) t :=
    contDiffAt_id.add contDiffAt_const
  unfold selbergSqrtZetaSignedPseudoPhase
  exact
    (((OscillatoryIntegral.contDiffAt_hardyPhase_two
          (n := 1) (by norm_num) htv).comp t
          hvShift).add
      ((OscillatoryIntegral.contDiffAt_hardyPhase_two
          (n := 1) (by norm_num) htw).comp t
          hwShift)).add
      (contDiffAt_const.mul contDiffAt_id)

/-- The second derivative of the pseudo phase is the sum of two reciprocal
shifted heights; the collected frequencies disappear after differentiation. -/
theorem iteratedDeriv_two_selbergSqrtZetaSignedPseudoPhase
    {omega nu v w t : ℝ} (htv : 0 < t + v) (htw : 0 < t + w) :
    iteratedDeriv 2
        (selbergSqrtZetaSignedPseudoPhase omega nu v w) t =
      1 / (2 * (t + v)) + 1 / (2 * (t + w)) := by
  have hvCont : ContDiffAt ℝ 2
      (fun x : ℝ => OscillatoryIntegral.hardyPhase 1 (x + v)) t :=
    (OscillatoryIntegral.contDiffAt_hardyPhase_two (by norm_num) htv).comp t
      (contDiffAt_id.add contDiffAt_const)
  have hwCont : ContDiffAt ℝ 2
      (fun x : ℝ => OscillatoryIntegral.hardyPhase 1 (x + w)) t :=
    (OscillatoryIntegral.contDiffAt_hardyPhase_two (by norm_num) htw).comp t
      (contDiffAt_id.add contDiffAt_const)
  have hlinear : ContDiffAt ℝ 2 (fun x : ℝ => (omega + nu) * x) t :=
    contDiffAt_const.mul contDiffAt_id
  have hlinearTwo :
      iteratedDeriv 2 (fun x : ℝ => (omega + nu) * x) t = 0 := by
    rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
    have hfirst :
        deriv (fun x : ℝ => (omega + nu) * x) =
          fun _ => omega + nu := by
      funext x
      simpa using ((hasDerivAt_id x).const_mul (omega + nu)).deriv
    rw [hfirst]
    simp
  unfold selbergSqrtZetaSignedPseudoPhase
  rw [iteratedDeriv_fun_add (hvCont.add hwCont) hlinear,
    iteratedDeriv_fun_add hvCont hwCont]
  rw [show iteratedDeriv 2
          (fun x : ℝ => OscillatoryIntegral.hardyPhase 1 (x + v)) t =
        iteratedDeriv 2 (OscillatoryIntegral.hardyPhase 1) (t + v) by
      exact congrFun (iteratedDeriv_comp_add_const
        (n := 2) (f := OscillatoryIntegral.hardyPhase 1) (s := v)) t]
  rw [show iteratedDeriv 2
          (fun x : ℝ => OscillatoryIntegral.hardyPhase 1 (x + w)) t =
        iteratedDeriv 2 (OscillatoryIntegral.hardyPhase 1) (t + w) by
      exact congrFun (iteratedDeriv_comp_add_const
        (n := 2) (f := OscillatoryIntegral.hardyPhase 1) (s := w)) t]
  rw [OscillatoryIntegral.iteratedDeriv_two_hardyPhase (by norm_num) htv,
    OscillatoryIntegral.iteratedDeriv_two_hardyPhase (by norm_num) htw]
  rw [hlinearTwo]
  simp

/-- Each collected pseudo-correlation phase has a uniform `O(sqrt T)` height
integral on the full shift-compatible dyadic interval. -/
theorem norm_integral_cexp_selbergSqrtZetaSignedPseudoPhase_le
    {T delta v w omega nu : ℝ}
    (hT : 1 ≤ T) (_hdelta : 0 ≤ delta) (hroom : delta ≤ T)
    (hv : v ∈ Icc 0 delta) (hw : w ∈ Icc 0 delta) :
    ‖∫ t in T..2 * T - delta,
        Complex.exp
          (I * selbergSqrtZetaSignedPseudoPhase omega nu v w t)‖ ≤
      12 * Real.sqrt (4 * T) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hab : T ≤ 2 * T - delta := by linarith
  have hr : 0 < 1 / (4 * T) := one_div_pos.mpr (by positivity)
  have hlocal : ∀ t ∈ Icc T (2 * T - delta),
      ContDiffAt ℝ 2
        (selbergSqrtZetaSignedPseudoPhase omega nu v w) t := by
    intro t ht
    apply contDiffAt_selbergSqrtZetaSignedPseudoPhase_two
    · linarith [hTpos, ht.1, hv.1]
    · linarith [hTpos, ht.1, hw.1]
  have hsecond : ∀ t ∈ Icc T (2 * T - delta),
      1 / (4 * T) ≤
        iteratedDeriv 2
          (selbergSqrtZetaSignedPseudoPhase omega nu v w) t := by
    intro t ht
    have htvpos : 0 < t + v := by linarith [hTpos, ht.1, hv.1]
    have htwpos : 0 < t + w := by linarith [hTpos, ht.1, hw.1]
    have htvupper : t + v ≤ 2 * T := by linarith [ht.2, hv.2]
    have hfirst : 1 / (4 * T) ≤ 1 / (2 * (t + v)) := by
      exact (div_le_div_iff₀ (by positivity : 0 < 4 * T)
        (by positivity : 0 < 2 * (t + v))).2 (by nlinarith)
    rw [iteratedDeriv_two_selbergSqrtZetaSignedPseudoPhase htvpos htwpos]
    exact hfirst.trans (le_add_of_nonneg_right (by positivity))
  have hbound :=
    OscillatoryIntegral.norm_integral_cexp_phase_le_of_second_deriv_on_Icc
      hab hr hlocal (Or.inl hsecond)
  calc
    ‖∫ t in T..2 * T - delta,
        Complex.exp
          (I * selbergSqrtZetaSignedPseudoPhase omega nu v w t)‖ ≤
        12 / Real.sqrt (1 / (4 * T)) := hbound
    _ = 12 * Real.sqrt (4 * T) := by
      rw [one_div, Real.sqrt_inv]
      simp [div_eq_mul_inv]

/-- The time-independent coefficient of one collected pseudo-correlation
summand after the full Hardy phase is combined with its logarithmic mode. -/
noncomputable def selbergSqrtZetaSignedPseudoCoeff
    (kappa T : ℝ) (X : ℕ) (v w omega nu : ℝ) : ℂ :=
  selbergSqrtZetaSignedCollectedCoeff
      (firstZetaApproximationCutoff T) X omega *
    selbergSqrtZetaSignedCollectedCoeff
      (firstZetaApproximationCutoff T) X nu *
    Complex.exp
      (I * (((2 * kappa + omega * v + nu * w : ℝ)) : ℂ))

/-- At positive shifted heights, the actual complex signed model product is
the finite sum of the pseudo phases controlled above. -/
theorem selbergSqrtZetaSignedComplexModel_mul_shift_eq_sum_pseudoPhase
    (kappa T : ℝ) (X : ℕ) {t v w : ℝ}
    (htv : 0 < t + v) (htw : 0 < t + w) :
    selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
        selbergSqrtZetaSignedComplexModel kappa T X (t + w) =
      ∑ omega ∈
          selbergSqrtZetaSignedCollectedFrequencySupport
            (firstZetaApproximationCutoff T) X,
        ∑ nu ∈
            selbergSqrtZetaSignedCollectedFrequencySupport
              (firstZetaApproximationCutoff T) X,
          selbergSqrtZetaSignedPseudoCoeff kappa T X v w omega nu *
            Complex.exp
              (I * selbergSqrtZetaSignedPseudoPhase omega nu v w t) := by
  rw [selbergSqrtZetaSignedComplexModel_mul_shift_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omega homega
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro nu hnu
  unfold selbergSqrtZetaSignedPseudoCoeff
  rw [show
      (Complex.exp (I * kappa) *
          Complex.exp (I * (thetaModel (t + v) : ℂ)) *
        (Complex.exp (I * kappa) *
          Complex.exp (I * (thetaModel (t + w) : ℂ)))) *
        (selbergSqrtZetaSignedCollectedCoeff
              (firstZetaApproximationCutoff T) X omega *
            selbergSqrtZetaSignedCollectedCoeff
              (firstZetaApproximationCutoff T) X nu *
          Complex.exp
            (I * (((omega + nu) * t + omega * v + nu * w) : ℂ))) =
        (selbergSqrtZetaSignedCollectedCoeff
              (firstZetaApproximationCutoff T) X omega *
            selbergSqrtZetaSignedCollectedCoeff
              (firstZetaApproximationCutoff T) X nu) *
          ((Complex.exp (I * kappa) *
              Complex.exp (I * (thetaModel (t + v) : ℂ)) *
            (Complex.exp (I * kappa) *
              Complex.exp (I * (thetaModel (t + w) : ℂ)))) *
            Complex.exp
              (I * (((omega + nu) * t + omega * v + nu * w) : ℂ))) by
      ring]
  rw [show
      selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X omega *
          selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X nu *
        Complex.exp
          (I * ((2 * kappa + omega * v + nu * w : ℝ) : ℂ)) *
        Complex.exp
          (I * selbergSqrtZetaSignedPseudoPhase omega nu v w t) =
        (selbergSqrtZetaSignedCollectedCoeff
              (firstZetaApproximationCutoff T) X omega *
            selbergSqrtZetaSignedCollectedCoeff
              (firstZetaApproximationCutoff T) X nu) *
          (Complex.exp
              (I * ((2 * kappa + omega * v + nu * w : ℝ) : ℂ)) *
            Complex.exp
              (I * selbergSqrtZetaSignedPseudoPhase omega nu v w t)) by
      ring]
  congr 1
  unfold selbergSqrtZetaSignedPseudoPhase
  rw [OscillatoryIntegral.hardyPhase_eq_thetaModel_sub_log
      (n := 1) (by norm_num) htv,
    OscillatoryIntegral.hardyPhase_eq_thetaModel_sub_log
      (n := 1) (by norm_num) htw]
  norm_num
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- Fixed-shift pseudo-correlation budget for the actual collected complex
model. Each frequency pair costs `O(sqrt T)`, uniformly even when its first
phase derivative has a stationary point. -/
theorem norm_integral_selbergSqrtZetaSignedComplexModel_mul_shift_le
    (kappa : ℝ) {T delta : ℝ} (X : ℕ)
    (hT : 1 ≤ T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T)
    {v w : ℝ} (hv : v ∈ Icc 0 delta) (hw : w ∈ Icc 0 delta) :
    ‖∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          selbergSqrtZetaSignedComplexModel kappa T X (t + w)‖ ≤
      ∑ omega ∈
          selbergSqrtZetaSignedCollectedFrequencySupport
            (firstZetaApproximationCutoff T) X,
        ∑ nu ∈
            selbergSqrtZetaSignedCollectedFrequencySupport
              (firstZetaApproximationCutoff T) X,
          (12 * Real.sqrt (4 * T)) *
            (‖selbergSqrtZetaSignedCollectedCoeff
                (firstZetaApproximationCutoff T) X omega‖ *
              ‖selbergSqrtZetaSignedCollectedCoeff
                (firstZetaApproximationCutoff T) X nu‖) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hab : T ≤ 2 * T - delta := by linarith
  have hsummandContAt : ∀ omega nu t, t ∈ Icc T (2 * T - delta) →
      ContinuousAt
        (fun x : ℝ =>
          selbergSqrtZetaSignedPseudoCoeff kappa T X v w omega nu *
            Complex.exp
              (I * selbergSqrtZetaSignedPseudoPhase omega nu v w x)) t := by
    intro omega nu t ht
    have hphase :
        ContinuousAt
          (selbergSqrtZetaSignedPseudoPhase omega nu v w) t :=
      (contDiffAt_selbergSqrtZetaSignedPseudoPhase_two
        (by linarith [hTpos, ht.1, hv.1])
        (by linarith [hTpos, ht.1, hw.1])).continuousAt
    exact continuousAt_const.mul
      ((continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp hphase)).cexp)
  have hsummandInt : ∀ omega nu,
      IntervalIntegrable
        (fun t : ℝ =>
          selbergSqrtZetaSignedPseudoCoeff kappa T X v w omega nu *
            Complex.exp
              (I * selbergSqrtZetaSignedPseudoPhase omega nu v w t))
        volume T (2 * T - delta) := by
    intro omega nu
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact (hsummandContAt omega nu t ht).continuousWithinAt
  have hinnerInt : ∀ omega,
      IntervalIntegrable
        (fun t : ℝ =>
          ∑ nu ∈
              selbergSqrtZetaSignedCollectedFrequencySupport
                (firstZetaApproximationCutoff T) X,
            selbergSqrtZetaSignedPseudoCoeff kappa T X v w omega nu *
              Complex.exp
                (I * selbergSqrtZetaSignedPseudoPhase omega nu v w t))
        volume T (2 * T - delta) := by
    intro omega
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    apply ContinuousAt.continuousWithinAt
    apply tendsto_finset_sum
    intro nu hnu
    exact hsummandContAt omega nu t ht
  have hpoint : ∀ t ∈ uIcc T (2 * T - delta),
      selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          selbergSqrtZetaSignedComplexModel kappa T X (t + w) =
        ∑ omega ∈
            selbergSqrtZetaSignedCollectedFrequencySupport
              (firstZetaApproximationCutoff T) X,
          ∑ nu ∈
              selbergSqrtZetaSignedCollectedFrequencySupport
                (firstZetaApproximationCutoff T) X,
            selbergSqrtZetaSignedPseudoCoeff kappa T X v w omega nu *
              Complex.exp
                (I * selbergSqrtZetaSignedPseudoPhase omega nu v w t) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact
      selbergSqrtZetaSignedComplexModel_mul_shift_eq_sum_pseudoPhase
        kappa T X
        (by linarith [hTpos, ht.1, hv.1])
        (by linarith [hTpos, ht.1, hw.1])
  rw [intervalIntegral.integral_congr hpoint]
  rw [intervalIntegral.integral_finset_sum]
  · calc
      ‖∑ omega ∈
          selbergSqrtZetaSignedCollectedFrequencySupport
            (firstZetaApproximationCutoff T) X,
          ∫ t in T..2 * T - delta,
            ∑ nu ∈
                selbergSqrtZetaSignedCollectedFrequencySupport
                  (firstZetaApproximationCutoff T) X,
              selbergSqrtZetaSignedPseudoCoeff kappa T X v w omega nu *
                Complex.exp
                  (I * selbergSqrtZetaSignedPseudoPhase omega nu v w t)‖ ≤
          ∑ omega ∈
            selbergSqrtZetaSignedCollectedFrequencySupport
              (firstZetaApproximationCutoff T) X,
            ‖∫ t in T..2 * T - delta,
              ∑ nu ∈
                  selbergSqrtZetaSignedCollectedFrequencySupport
                    (firstZetaApproximationCutoff T) X,
                selbergSqrtZetaSignedPseudoCoeff kappa T X v w omega nu *
                  Complex.exp
                    (I * selbergSqrtZetaSignedPseudoPhase omega nu v w t)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ omega ∈
          selbergSqrtZetaSignedCollectedFrequencySupport
            (firstZetaApproximationCutoff T) X,
          ∑ nu ∈
              selbergSqrtZetaSignedCollectedFrequencySupport
                (firstZetaApproximationCutoff T) X,
            (12 * Real.sqrt (4 * T)) *
              (‖selbergSqrtZetaSignedCollectedCoeff
                  (firstZetaApproximationCutoff T) X omega‖ *
                ‖selbergSqrtZetaSignedCollectedCoeff
                  (firstZetaApproximationCutoff T) X nu‖) := by
        apply Finset.sum_le_sum
        intro omega homega
        rw [intervalIntegral.integral_finset_sum]
        · calc
            ‖∑ nu ∈
                selbergSqrtZetaSignedCollectedFrequencySupport
                  (firstZetaApproximationCutoff T) X,
                ∫ t in T..2 * T - delta,
                  selbergSqrtZetaSignedPseudoCoeff kappa T X v w omega nu *
                    Complex.exp
                      (I *
                        selbergSqrtZetaSignedPseudoPhase omega nu v w t)‖ ≤
                ∑ nu ∈
                  selbergSqrtZetaSignedCollectedFrequencySupport
                    (firstZetaApproximationCutoff T) X,
                  ‖∫ t in T..2 * T - delta,
                    selbergSqrtZetaSignedPseudoCoeff kappa T X v w omega nu *
                      Complex.exp
                        (I *
                          selbergSqrtZetaSignedPseudoPhase omega nu v w t)‖ :=
              norm_sum_le _ _
            _ ≤ ∑ nu ∈
                selbergSqrtZetaSignedCollectedFrequencySupport
                  (firstZetaApproximationCutoff T) X,
                (12 * Real.sqrt (4 * T)) *
                  (‖selbergSqrtZetaSignedCollectedCoeff
                      (firstZetaApproximationCutoff T) X omega‖ *
                    ‖selbergSqrtZetaSignedCollectedCoeff
                      (firstZetaApproximationCutoff T) X nu‖) := by
              apply Finset.sum_le_sum
              intro nu hnu
              rw [show
                (∫ t in T..2 * T - delta,
                    selbergSqrtZetaSignedPseudoCoeff
                        kappa T X v w omega nu *
                      Complex.exp
                        (I *
                          selbergSqrtZetaSignedPseudoPhase omega nu v w t)) =
                  selbergSqrtZetaSignedPseudoCoeff
                      kappa T X v w omega nu *
                    ∫ t in T..2 * T - delta,
                      Complex.exp
                        (I *
                          selbergSqrtZetaSignedPseudoPhase omega nu v w t) by
                exact intervalIntegral.integral_const_mul _ _]
              have hphase :=
                norm_integral_cexp_selbergSqrtZetaSignedPseudoPhase_le
                  hT hdelta hroom hv hw
                  (omega := omega) (nu := nu)
              calc
                ‖selbergSqrtZetaSignedPseudoCoeff
                    kappa T X v w omega nu *
                    ∫ t in T..2 * T - delta,
                      Complex.exp
                        (I *
                          selbergSqrtZetaSignedPseudoPhase omega nu v w t)‖ =
                    ‖selbergSqrtZetaSignedPseudoCoeff
                      kappa T X v w omega nu‖ *
                      ‖∫ t in T..2 * T - delta,
                        Complex.exp
                          (I *
                            selbergSqrtZetaSignedPseudoPhase omega nu v w t)‖ := by
                  rw [norm_mul]
                _ ≤ ‖selbergSqrtZetaSignedPseudoCoeff
                      kappa T X v w omega nu‖ *
                      (12 * Real.sqrt (4 * T)) :=
                  mul_le_mul_of_nonneg_left hphase (norm_nonneg _)
                _ = (12 * Real.sqrt (4 * T)) *
                    (‖selbergSqrtZetaSignedCollectedCoeff
                        (firstZetaApproximationCutoff T) X omega‖ *
                      ‖selbergSqrtZetaSignedCollectedCoeff
                        (firstZetaApproximationCutoff T) X nu‖) := by
                  unfold selbergSqrtZetaSignedPseudoCoeff
                  simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
                  ring
        · intro nu hnu
          exact hsummandInt omega nu
  · intro omega homega
    exact hinnerInt omega

end HardyTheorem
