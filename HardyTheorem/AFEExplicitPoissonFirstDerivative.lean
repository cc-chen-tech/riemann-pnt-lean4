import HardyTheorem.AFEExplicitPoissonFarTail

/-! A support-aware first-derivative estimate for finite Poisson bands. -/

open Complex Set MeasureTheory Filter
open scoped Topology

namespace HardyTheorem.AFE

/-- Transfer the weighted oscillatory primitive bound through the two unit
transitions. The derivative mass is independent of the upper endpoint. -/
theorem norm_explicitMellin_phaseIntegral_le_firstDerivative
    {F : ℝ → ℝ} {C₁ sigma x N g : ℝ}
    (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N) (hg : 0 < g)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hF : ∀ u : ℝ, 0 < u → ContDiffAt ℝ 2 F u)
    (hmono : MonotoneOn (deriv F) (Icc (x - 1) (N + 1)) ∨
      AntitoneOn (deriv F) (Icc (x - 1) (N + 1)))
    (hgap : ∀ u ∈ Icc (x - 1) (N + 1), g ≤ |deriv F u|) :
    ‖∫ u in (x - 1)..(N + 1), explicitComplexMellinAmplitude sigma x N u *
      Complex.exp (I * F u)‖ ≤ 16 * C₁ * (x - 1) ^ (-sigma) / g := by
  have ha : 0 < x - 1 := by linarith
  have hab : x - 1 ≤ N + 1 := by linarith
  let E : ℝ → ℂ := fun u => u ^ (-sigma) • Complex.exp (I * F u)
  let H : ℝ → ℂ := fun v => ∫ u in (x - 1)..v, E u
  have hE_at (u : ℝ) (hu : 0 < u) : ContinuousAt E u :=
    (Real.continuousAt_rpow_const u (-sigma) (Or.inl hu.ne')).smul
      ((continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp (hF u hu).continuousAt)).cexp)
  have hE_pos : ContinuousOn E (Ioi 0) := fun u hu =>
    (hE_at u hu).continuousWithinAt
  have hE_cont : ContinuousOn E (Icc (x - 1) (N + 1)) :=
    hE_pos.mono (fun _ hu => ha.trans_le hu.1)
  have hE_int : IntervalIntegrable E volume (x - 1) (N + 1) :=
    hE_cont.intervalIntegrable_of_Icc hab
  have hH_deriv (u : ℝ) (hu : u ∈ Icc (x - 1) (N + 1)) :
      HasDerivAt H (E u) u := by
    have hu0 := ha.trans_le hu.1
    exact intervalIntegral.integral_hasDerivAt_right
      ((hE_cont.mono (Icc_subset_Icc le_rfl hu.2)).intervalIntegrable_of_Icc hu.1)
      (hE_pos.stronglyMeasurableAtFilter isOpen_Ioi u hu0) (hE_at u hu0)
  have hH_bound (u : ℝ) (hu : u ∈ Icc (x - 1) (N + 1)) :
      ‖H u‖ ≤ 4 * (x - 1) ^ (-sigma) / g := by
    apply OscillatoryIntegral.norm_integral_rpow_smul_cexp_phase_le_of_monotone_deriv_local
      hu.1 ha hg hs (fun v hv => hF v (ha.trans_le hv.1))
    · rcases hmono with hmono | hanti
      · exact Or.inl (hmono.mono (Icc_subset_Icc le_rfl hu.2))
      · exact Or.inr (hanti.mono (Icc_subset_Icc le_rfl hu.2))
    · intro v hv
      exact hgap v ⟨hv.1, hv.2.trans hu.2⟩
  have hwd_cont : Continuous (explicitIntervalPlateauDeriv x N) :=
    continuous_iff_continuousAt.mpr fun u =>
      (explicitIntervalPlateauDeriv_hasDerivAt x N u).continuousAt
  have hwd_int : IntervalIntegrable (explicitIntervalPlateauDeriv x N)
      volume (x - 1) (N + 1) := hwd_cont.intervalIntegrable (x - 1) (N + 1)
  have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (u := explicitIntervalPlateau x N) (u' := explicitIntervalPlateauDeriv x N)
    (v := H) (v' := E)
    (fun u _ => explicitIntervalPlateau_hasDerivAt x N u)
    (fun u hu => hH_deriv u (by simpa only [uIcc_of_le hab] using hu)) hwd_int hE_int
  have hparts' :
      (∫ u in (x - 1)..(N + 1), explicitIntervalPlateau x N u • E u) =
        -(∫ u in (x - 1)..(N + 1), explicitIntervalPlateauDeriv x N u • H u) := by
    simpa only [explicitIntervalPlateau_eq_zero_of_le (x := x) (N := N) le_rfl,
      explicitIntervalPlateau_eq_zero_of_ge (x := x) (N := N) le_rfl,
      zero_smul, sub_self, zero_sub] using hparts
  have hL1 : (∫ u in (x - 1)..(N + 1), |explicitIntervalPlateauDeriv x N u|) ≤
      4 * C₁ := by
    simpa using intervalIntegral_abs_plateauDeriv_mul_rpow_le
      (p := 0) hx hxN le_rfl hC₁0 hC₁
  calc
    _ = ‖∫ u in (x - 1)..(N + 1), explicitIntervalPlateau x N u • E u‖ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      simp only [explicitComplexMellinAmplitude, explicitMellinAmplitude, mellinRpow,
        E, Complex.real_smul, Complex.ofReal_mul]
      ring
    _ = ‖∫ u in (x - 1)..(N + 1), explicitIntervalPlateauDeriv x N u • H u‖ := by
      rw [hparts', norm_neg]
    _ ≤ ∫ u in (x - 1)..(N + 1),
        |explicitIntervalPlateauDeriv x N u| * (4 * (x - 1) ^ (-sigma) / g) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hab ?_
        ((hwd_cont.abs.intervalIntegrable _ _).mul_const _)
      filter_upwards with u hu
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hH_bound u ⟨hu.1.le, hu.2⟩) (abs_nonneg _)
    _ = (∫ u in (x - 1)..(N + 1), |explicitIntervalPlateauDeriv x N u|) *
        (4 * (x - 1) ^ (-sigma) / g) := intervalIntegral.integral_mul_const _ _
    _ ≤ (4 * C₁) * (4 * (x - 1) ^ (-sigma) / g) :=
      mul_le_mul_of_nonneg_right hL1 (by positivity)
    _ = _ := by ring

end HardyTheorem.AFE
