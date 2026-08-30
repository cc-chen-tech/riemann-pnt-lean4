import HardyTheorem.AFEExplicitPoissonSecondDerivative

/-! A whole-mode bound at the square-root stationary endpoint. -/

open Complex Set MeasureTheory

namespace HardyTheorem.AFE

/-- The nearest square-root modes cost `O(K^(-sigma))`, uniformly in the
upper cutoff.  The range includes `m = K-1`, where a unit lower-end gap
is unavailable.  Only a finite endpoint band may be summed using this bound. -/
theorem norm_explicitPoissonMode_near_sqrt_endpoint_le
    {C₁ sigma K N t : ℝ} {m : ℕ}
    (hs : 0 < sigma) (hK : 6 ≤ K) (hN : 2 * K ≤ N)
    (htL : 2 * Real.pi * K ^ 2 ≤ t) (htU : t ≤ 2 * Real.pi * (K + 1) ^ 2)
    (hm : K - 1 ≤ (m : ℝ)) (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    ‖explicitPoissonMode sigma (K + 1) N t (-(m : ℤ))‖ ≤
      (12 * (4 * C₁ + 2) / Real.sqrt (Real.pi / 2) +
        4 * (1 + 4 * C₁) / Real.pi) * K ^ (-sigma) := by
  have hK0 : 0 < K := by linarith
  have ht0 : 0 ≤ t := (show 0 ≤ 2 * Real.pi * K ^ 2 by positivity).trans htL
  let F : ℝ → ℝ := weightedPoissonPhase t (-(m : ℤ))
  let E : ℝ → ℂ := fun u => explicitComplexMellinAmplitude sigma (K + 1) N u *
    Complex.exp (I * F u)
  have hF (u : ℝ) (hu : 0 < u) : ContDiffAt ℝ 2 F u := by
    dsimp only [F, weightedPoissonPhase]
    exact (contDiffAt_const.mul (Real.contDiffAt_log.mpr hu.ne')).sub
      (contDiffAt_const.mul contDiffAt_id)
  have hF_eq : F = OscillatoryIntegral.fourierMellinPhase (m : ℤ) t := by
    funext u
    simpa only [Int.neg_neg] using weightedPoissonPhase_eq_fourierMellinPhase_neg t (-(m : ℤ)) u
  have hleft : ‖∫ u in K..(2 * K), E u‖ ≤
      12 * (4 * C₁ + 2) * K ^ (-sigma) / Real.sqrt (Real.pi / 2) := by
    apply norm_explicitMellin_restricted_phaseIntegral_le_secondDerivative
      hs (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      (by positivity) hC₁0 hC₁ hF
    left
    intro u hu
    have hu0 := hK0.trans_le hu.1
    rw [hF_eq, OscillatoryIntegral.iteratedDeriv_two_fourierMellinPhase _ _ hu0.ne']
    apply (le_div_iff₀ (sq_pos_of_pos hu0)).2
    have hu2 : u ^ 2 ≤ (2 * K) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (show 0 ≤ 2 * K + u by linarith)]
    have hscaled := mul_le_mul_of_nonneg_left hu2 (show 0 ≤ Real.pi / 2 by positivity)
    nlinarith
  have hright : ‖∫ u in (2 * K)..(N + 1), E u‖ ≤
      4 * (1 + 4 * C₁) * (2 * K) ^ (-sigma) / Real.pi := by
    apply norm_explicitMellin_restricted_phaseIntegral_le_firstDerivative
      hs (by linarith) (by linarith) (by linarith) (by linarith) le_rfl
      Real.pi_pos hC₁0 hC₁ hF
    · left
      intro u hu v hv huv
      have hu0 : 0 < u := by linarith [hu.1]
      have hv0 : 0 < v := by linarith [hv.1]
      change deriv (weightedPoissonPhase t (-(m : ℤ))) u ≤
        deriv (weightedPoissonPhase t (-(m : ℤ))) v
      rw [deriv_weightedPoissonPhase_neg_nat t m hu0.ne',
        deriv_weightedPoissonPhase_neg_nat t m hv0.ne']
      have hdiv := div_le_div_of_nonneg_left ht0 hu0 huv
      linarith
    · intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      have hpoly : (K + 1) ^ 2 ≤ K * (2 * K - 3) := by
        nlinarith [sq_nonneg (K - 6)]
      have hdiv : t / u ≤ Real.pi * (2 * K - 3) := by
        calc
          _ ≤ t / (2 * K) := div_le_div_of_nonneg_left ht0 (by positivity) hu.1
          _ ≤ (2 * Real.pi * (K + 1) ^ 2) / (2 * K) :=
            div_le_div_of_nonneg_right htU (by positivity)
          _ ≤ _ := by
            apply (div_le_iff₀ (show 0 < 2 * K by positivity)).2
            nlinarith [mul_le_mul_of_nonneg_left hpoly (show 0 ≤ 2 * Real.pi by positivity)]
      change Real.pi ≤ |deriv (weightedPoissonPhase t (-(m : ℤ))) u|
      rw [deriv_weightedPoissonPhase_neg_nat t m hu0.ne']
      apply le_trans _ (le_abs_self _)
      nlinarith [mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * Real.pi by positivity)]
  have hright' : ‖∫ u in (2 * K)..(N + 1), E u‖ ≤
      4 * (1 + 4 * C₁) * K ^ (-sigma) / Real.pi := by
    refine hright.trans (div_le_div_of_nonneg_right ?_ Real.pi_pos.le)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_nonpos hK0 (by linarith) (neg_nonpos.mpr hs.le)
  have hE_cont : ContinuousOn E (Icc K (N + 1)) := by
    intro u hu
    have hu0 := hK0.trans_le hu.1
    exact ((explicitComplexMellinAmplitude_hasDerivAt sigma (K + 1) N hu0.ne').continuousAt.mul
      ((continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp (hF u hu0).continuousAt)).cexp)).continuousWithinAt
  have hEl : IntervalIntegrable E volume K (2 * K) :=
    (hE_cont.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc (by linarith)
  have hEr : IntervalIntegrable E volume (2 * K) (N + 1) :=
    (hE_cont.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc (by linarith)
  unfold explicitPoissonMode
  rw [show K + 1 - 1 = K by ring]
  change ‖∫ u in K..(N + 1), E u‖ ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hEl hEr]
  calc
    _ ≤ ‖∫ u in K..(2 * K), E u‖ + ‖∫ u in (2 * K)..(N + 1), E u‖ := norm_add_le _ _
    _ ≤ 12 * (4 * C₁ + 2) * K ^ (-sigma) / Real.sqrt (Real.pi / 2) +
        4 * (1 + 4 * C₁) * K ^ (-sigma) / Real.pi := add_le_add hleft hright'
    _ = _ := by ring

end HardyTheorem.AFE
