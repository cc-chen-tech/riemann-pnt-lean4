import HardyTheorem.AFEExplicitPoissonRestrictedCutoff
import HardyTheorem.OscillatoryGammaCoreReplacement
import HardyTheorem.AFEExplicitPoissonIdentity

/-! Gamma replacement for an inner stationary mode, retaining both transitions. -/

open Complex Set MeasureTheory

namespace HardyTheorem.AFE

/-- The Gamma value belonging to negative Poisson index `-m`. -/
noncomputable def poissonGammaTerm (sigma t : ℝ) (m : ℕ) : ℂ :=
  let s : ℂ := (sigma : ℂ) + I * t
  ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ^ (s - 1) *
    (Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ) * (1 - s)) * Complex.Gamma (1 - s))

private theorem core_integrand_eq (sigma t : ℝ) (m : ℕ) {x N u : ℝ}
    (hx : 0 < x) (hu : u ∈ Icc x N) :
    explicitComplexMellinAmplitude sigma x N u *
      Complex.exp (I * weightedPoissonPhase t (-(m : ℤ)) u) =
    (u : ℂ) ^ (-((sigma : ℂ) + I * t)) *
      Complex.exp (I * ((2 * Real.pi * (m : ℝ)) * u)) := by
  rw [← explicitWeightedPoissonCutoff_fourierIntegrand_eq sigma t x N u
    (-(m : ℤ)) (hx.trans_le hu.1), explicitWeightedPoissonCutoff_eq_cpow _ hx hu]
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

private theorem norm_phase_integral_le_length {sigma x N t a b : ℝ} (k : ℤ)
    (hs : 0 ≤ sigma) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ u in a..b, explicitComplexMellinAmplitude sigma x N u *
      Complex.exp (I * weightedPoissonPhase t k u)‖ ≤ a ^ (-sigma) * (b - a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b)
    (f := fun u => explicitComplexMellinAmplitude sigma x N u *
      Complex.exp (I * weightedPoissonPhase t k u)) (C := a ^ (-sigma)) (fun u hu => by
      have hu' : u ∈ Ioc a b := by simpa only [uIoc_of_le hab] using hu
      have hu0 := ha.trans hu'.1
      have he : ‖Complex.exp (I * (weightedPoissonPhase t k u : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [norm_mul, he, mul_one]
      exact (norm_explicitComplexMellinAmplitude_le sigma x N hu0).trans
        (Real.rpow_le_rpow_of_nonpos ha hu'.1.le (neg_nonpos.mpr hs)))
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using h

/-- An actual smoothed Poisson mode minus its Gamma main term.  The lower
transition retains the harmonic gap; only the upper unit transition is
estimated by absolute length. -/
theorem norm_explicitPoissonMode_sub_gamma_le
    {C₁ sigma x t : ℝ} {N m : ℕ}
    (hs0 : 0 < sigma) (hs1 : sigma < 1) (hx : 1 < x) (hxN : x ≤ (N : ℝ))
    (hm : 1 ≤ m) (hgap : 2 * Real.pi * (m : ℝ) * x < t)
    (hfar : 2 * t ≤ 2 * Real.pi * (m : ℝ) * (N : ℝ))
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    ‖explicitPoissonMode sigma x N t (-(m : ℤ)) - poissonGammaTerm sigma t m‖ ≤
      ((3 + 8 * C₁) / Real.pi) * (x - 1) ^ (-sigma) /
        (t / (2 * Real.pi * x) - m) +
      (1 + 4 / (Real.pi * m)) * (N : ℝ) ^ (-sigma) := by
  have hx0 : 0 < x := by linarith
  have ha : 0 < x - 1 := by linarith
  have hN0 : 0 < (N : ℝ) := hx0.trans_le hxN
  have hN1 : 1 ≤ N := by exact_mod_cast (show 1 ≤ (N : ℝ) by linarith)
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  let c : ℝ := 2 * Real.pi * m
  have hc : 0 < c := by dsimp only [c]; positivity
  have ht : 0 < t := (mul_pos hc hx0).trans hgap
  let s : ℂ := (sigma : ℂ) + I * t
  let F : ℝ → ℝ := weightedPoissonPhase t (-(m : ℤ))
  let E : ℝ → ℂ := fun u => explicitComplexMellinAmplitude sigma x N u * Complex.exp (I * F u)
  have hF (u : ℝ) (hu : 0 < u) : ContDiffAt ℝ 2 F u := by
    dsimp only [F, weightedPoissonPhase]
    exact (contDiffAt_const.mul (Real.contDiffAt_log.mpr hu.ne')).sub
      (contDiffAt_const.mul contDiffAt_id)
  have hE : ContinuousOn E (Ioi 0) := by
    intro u hu
    exact ((explicitComplexMellinAmplitude_hasDerivAt sigma x N hu.ne').continuousAt.mul
      ((continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp (hF u hu).continuousAt)).cexp)).continuousWithinAt
  have hi {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable E volume a b :=
    (hE.mono (fun _ hu => ha.trans_le hu.1)).intervalIntegrable_of_Icc hab
  have hsplit : (∫ u in (x - 1)..((N : ℝ) + 1), E u) =
      (∫ u in (x - 1)..x, E u) + (∫ u in x..(N : ℝ), E u) +
        (∫ u in (N : ℝ)..((N : ℝ) + 1), E u) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi ha (by linarith)) (hi hx0 hxN),
      intervalIntegral.integral_add_adjacent_intervals (hi ha (by linarith)) (hi hN0 (by linarith))]
  have hcore : (∫ u in x..(N : ℝ), E u) =
      ∫ u in x..(N : ℝ), (u : ℂ) ^ (-s) * Complex.exp (I * (c * u)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    simpa [E, F, s, c] using
      core_integrand_eq sigma t m hx0 (by simpa only [uIcc_of_le hxN] using hu)
  have hgamma : ‖(∫ u in x..(N : ℝ), E u) - poissonGammaTerm sigma t m‖ ≤
      2 * x ^ (1 - sigma) / (t - c * x) + 8 * (N : ℝ) ^ (-sigma) / c := by
    rw [hcore]
    exact norm_mellinCore_sub_gammaValue_le hs0 hs1 hc hx0 hgap hN1 hfar
  have hg : 0 < t / x - c := sub_pos.mpr ((lt_div_iff₀ hx0).mpr hgap)
  have hleft : ‖∫ u in (x - 1)..x, E u‖ ≤
      4 * (1 + 4 * C₁) * (x - 1) ^ (-sigma) / (t / x - c) := by
    apply norm_explicitMellin_restricted_phaseIntegral_le_firstDerivative
      hs0 hx hxN le_rfl (by linarith) (by linarith) hg hC₁0 hC₁ hF
    · left
      intro u hu v hv huv
      change deriv (weightedPoissonPhase t (-(m : ℤ))) u ≤
        deriv (weightedPoissonPhase t (-(m : ℤ))) v
      rw [deriv_weightedPoissonPhase_neg_nat t m (ha.trans_le hu.1).ne',
        deriv_weightedPoissonPhase_neg_nat t m (ha.trans_le hv.1).ne']
      have hdiv := div_le_div_of_nonneg_left ht.le (ha.trans_le hu.1) huv
      linarith
    · intro u hu
      change t / x - c ≤ |deriv (weightedPoissonPhase t (-(m : ℤ))) u|
      rw [deriv_weightedPoissonPhase_neg_nat t m (ha.trans_le hu.1).ne']
      have hdiv := div_le_div_of_nonneg_left ht.le (ha.trans_le hu.1) hu.2
      change t / x - c ≤ |c - t / u|
      have hneg : c - t / u ≤ 0 := by linarith
      rw [abs_of_nonpos hneg]
      linarith
  have hright : ‖∫ u in (N : ℝ)..((N : ℝ) + 1), E u‖ ≤ (N : ℝ) ^ (-sigma) := by
    simpa only [show (N : ℝ) + 1 - N = 1 by ring, mul_one] using
      (norm_phase_integral_le_length (sigma := sigma) (x := x) (N := N) (t := t)
        (-(m : ℤ)) hs0.le hN0 (show (N : ℝ) ≤ N + 1 by linarith))
  have hraw : ‖explicitPoissonMode sigma x N t (-(m : ℤ)) - poissonGammaTerm sigma t m‖ ≤
      (4 * (1 + 4 * C₁) * (x - 1) ^ (-sigma) / (t / x - c) +
        (2 * x ^ (1 - sigma) / (t - c * x) + 8 * (N : ℝ) ^ (-sigma) / c)) +
          (N : ℝ) ^ (-sigma) := by
    have hid : explicitPoissonMode sigma x N t (-(m : ℤ)) - poissonGammaTerm sigma t m =
        ((∫ u in (x - 1)..x, E u) +
          ((∫ u in x..(N : ℝ), E u) - poissonGammaTerm sigma t m)) +
        (∫ u in (N : ℝ)..((N : ℝ) + 1), E u) := by
      change (∫ u in (x - 1)..((N : ℝ) + 1), E u) - poissonGammaTerm sigma t m = _
      rw [hsplit]
      ring
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hleft hgamma)) hright)
  let b : ℝ := t / (2 * Real.pi * x) - m
  have hb : 0 < b := by
    dsimp only [b]
    apply sub_pos.mpr
    apply (lt_div_iff₀ (show 0 < 2 * Real.pi * x by positivity)).mpr
    nlinarith [hgap]
  have hd : t - c * x = x * (t / x - c) := by field_simp [hx0.ne']
  have hg' : t / x - c = 2 * Real.pi * b := by
    dsimp only [b, c]
    field_simp [hx0.ne', Real.pi_ne_zero]
  have hp : x ^ (1 - sigma) = x * x ^ (-sigma) := by
    rw [show 1 - sigma = 1 + (-sigma) by ring, Real.rpow_add hx0, Real.rpow_one]
  have hraw_eq :
      (4 * (1 + 4 * C₁) * (x - 1) ^ (-sigma) / (t / x - c) +
        (2 * x ^ (1 - sigma) / (t - c * x) + 8 * (N : ℝ) ^ (-sigma) / c)) +
          (N : ℝ) ^ (-sigma) =
      (2 * (1 + 4 * C₁) * (x - 1) ^ (-sigma) + x ^ (-sigma)) / (Real.pi * b) +
        (1 + 4 / (Real.pi * m)) * (N : ℝ) ^ (-sigma) := by
    rw [hd, hg', hp]
    dsimp only [c]
    field_simp [hx0.ne', hb.ne', hm0.ne', Real.pi_ne_zero]
    ring
  rw [hraw_eq] at hraw
  have hpower : x ^ (-sigma) ≤ (x - 1) ^ (-sigma) :=
    Real.rpow_le_rpow_of_nonpos ha (by linarith) (neg_nonpos.mpr hs0.le)
  calc
    _ ≤ (2 * (1 + 4 * C₁) * (x - 1) ^ (-sigma) + x ^ (-sigma)) / (Real.pi * b) +
        (1 + 4 / (Real.pi * m)) * (N : ℝ) ^ (-sigma) := hraw
    _ ≤ (2 * (1 + 4 * C₁) * (x - 1) ^ (-sigma) + (x - 1) ^ (-sigma)) / (Real.pi * b) +
        (1 + 4 / (Real.pi * m)) * (N : ℝ) ^ (-sigma) :=
      add_le_add (div_le_div_of_nonneg_right (add_le_add le_rfl hpower)
        (mul_nonneg Real.pi_pos.le hb.le)) le_rfl
    _ = _ := by
      change _ = ((3 + 8 * C₁) / Real.pi) * (x - 1) ^ (-sigma) / b +
        (1 + 4 / (Real.pi * m)) * (N : ℝ) ^ (-sigma)
      ring_nf

end HardyTheorem.AFE
