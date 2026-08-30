import HardyTheorem.AFEExplicitPoissonFirstDerivative

/-! Primitive transfer on restricted intervals, with the right boundary retained. -/

open Complex Set MeasureTheory Filter
open scoped Topology

namespace HardyTheorem.AFE

/-- Integration by parts against a bounded primitive.  No endpoint vanishing
is assumed: the right boundary contributes `|A b| * B`. -/
theorem norm_intervalIntegral_real_smul_le_primitive
    {A A' : ℝ → ℝ} {E : ℝ → ℂ} {a b B : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hA : ∀ u ∈ Icc a b, HasDerivAt A (A' u) u)
    (hAd : ContinuousOn A' (Icc a b)) (hE : ContinuousOn E (Ioi 0))
    (hprim : ∀ v ∈ Icc a b, ‖∫ u in a..v, E u‖ ≤ B) :
    ‖∫ u in a..b, A u • E u‖ ≤ (|A b| + ∫ u in a..b, |A' u|) * B := by
  let H : ℝ → ℂ := fun v => ∫ u in a..v, E u
  have hE_cont : ContinuousOn E (Icc a b) :=
    hE.mono (fun _ hu => ha.trans_le hu.1)
  have hE_int : IntervalIntegrable E volume a b :=
    hE_cont.intervalIntegrable_of_Icc hab
  have hH_deriv (u : ℝ) (hu : u ∈ Icc a b) : HasDerivAt H (E u) u := by
    have hu0 := ha.trans_le hu.1
    exact intervalIntegral.integral_hasDerivAt_right
      ((hE_cont.mono (Icc_subset_Icc le_rfl hu.2)).intervalIntegrable_of_Icc hu.1)
      (hE.stronglyMeasurableAtFilter isOpen_Ioi u hu0)
      (hE.continuousAt (isOpen_Ioi.mem_nhds hu0))
  have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (u := A) (u' := A') (v := H) (v' := E)
    (fun u hu => hA u (by simpa only [uIcc_of_le hab] using hu))
    (fun u hu => hH_deriv u (by simpa only [uIcc_of_le hab] using hu))
    (hAd.intervalIntegrable_of_Icc hab) hE_int
  have hHa : H a = 0 := by simp [H]
  rw [hHa, smul_zero, sub_zero] at hparts
  have htail : ‖∫ u in a..b, A' u • H u‖ ≤ (∫ u in a..b, |A' u|) * B := by
    calc
      _ ≤ ∫ u in a..b, |A' u| * B := by
        refine intervalIntegral.norm_integral_le_of_norm_le hab ?_
          ((hAd.abs.intervalIntegrable_of_Icc hab).mul_const B)
        filter_upwards with u hu
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hprim u ⟨hu.1.le, hu.2⟩) (abs_nonneg _)
      _ = _ := intervalIntegral.integral_mul_const _ _
  calc
    _ = ‖A b • H b - ∫ u in a..b, A' u • H u‖ := congrArg norm hparts
    _ ≤ ‖A b • H b‖ + ‖∫ u in a..b, A' u • H u‖ := norm_sub_le _ _
    _ ≤ |A b| * B + (∫ u in a..b, |A' u|) * B := by
      apply add_le_add _ htail
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hprim b ⟨hab, le_rfl⟩) (abs_nonneg _)
    _ = _ := by ring

/-- The two width-one transitions have bounded variation on every subinterval. -/
theorem intervalIntegral_abs_plateauDeriv_restricted_le
    {C₁ x N a b : ℝ} (hx : 1 < x) (hxN : x ≤ N)
    (hxa : x - 1 ≤ a) (hab : a ≤ b) (hbN : b ≤ N + 1)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    (∫ u in a..b, |explicitIntervalPlateauDeriv x N u|) ≤ 4 * C₁ := by
  have hcont : Continuous (explicitIntervalPlateauDeriv x N) :=
    continuous_iff_continuousAt.mpr fun u =>
      (explicitIntervalPlateauDeriv_hasDerivAt x N u).continuousAt
  calc
    _ ≤ ∫ u in (x - 1)..(N + 1), |explicitIntervalPlateauDeriv x N u| := by
      exact intervalIntegral.integral_mono_interval hxa hab hbN
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) (hcont.abs.intervalIntegrable _ _)
    _ ≤ _ := by
      simpa using intervalIntegral_abs_plateauDeriv_mul_rpow_le
        (p := 0) hx hxN le_rfl hC₁0 hC₁

/-- Transfer a primitive bound through a restricted width-one cutoff. -/
theorem norm_explicitPlateau_restricted_integral_le_primitive
    {E : ℝ → ℂ} {C₁ x N a b B : ℝ} (hx : 1 < x) (hxN : x ≤ N)
    (hxa : x - 1 ≤ a) (hab : a ≤ b) (hbN : b ≤ N + 1) (hB : 0 ≤ B)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hE : ContinuousOn E (Ioi 0))
    (hprim : ∀ v ∈ Icc a b, ‖∫ u in a..v, E u‖ ≤ B) :
    ‖∫ u in a..b, explicitIntervalPlateau x N u • E u‖ ≤ (1 + 4 * C₁) * B := by
  have ha : 0 < a := by linarith
  have hAd : Continuous (explicitIntervalPlateauDeriv x N) :=
    continuous_iff_continuousAt.mpr fun u =>
      (explicitIntervalPlateauDeriv_hasDerivAt x N u).continuousAt
  have hA_bound : |explicitIntervalPlateau x N b| ≤ 1 := by
    rw [abs_of_nonneg (explicitIntervalPlateau_nonneg x N b)]
    exact explicitIntervalPlateau_le_one x N b
  calc
    _ ≤ (|explicitIntervalPlateau x N b| +
        ∫ u in a..b, |explicitIntervalPlateauDeriv x N u|) * B :=
      norm_intervalIntegral_real_smul_le_primitive ha hab
        (fun u _ => explicitIntervalPlateau_hasDerivAt x N u) hAd.continuousOn hE hprim
    _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add hA_bound
      (intervalIntegral_abs_plateauDeriv_restricted_le hx hxN hxa hab hbN hC₁0 hC₁)) hB

/-- First-derivative cancellation survives restriction inside the plateau.
The constant includes the nonzero right boundary, uniformly in `N`. -/
theorem norm_explicitMellin_restricted_phaseIntegral_le_firstDerivative
    {F : ℝ → ℝ} {C₁ sigma x N a b g : ℝ}
    (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N)
    (hxa : x - 1 ≤ a) (hab : a ≤ b) (hbN : b ≤ N + 1) (hg : 0 < g)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hF : ∀ u : ℝ, 0 < u → ContDiffAt ℝ 2 F u)
    (hmono : MonotoneOn (deriv F) (Icc a b) ∨ AntitoneOn (deriv F) (Icc a b))
    (hgap : ∀ u ∈ Icc a b, g ≤ |deriv F u|) :
    ‖∫ u in a..b, explicitComplexMellinAmplitude sigma x N u *
      Complex.exp (I * F u)‖ ≤ 4 * (1 + 4 * C₁) * a ^ (-sigma) / g := by
  have ha : 0 < a := by linarith
  let E : ℝ → ℂ := fun u => u ^ (-sigma) • Complex.exp (I * F u)
  have hE : ContinuousOn E (Ioi 0) := by
    intro u hu
    exact ((Real.continuousAt_rpow_const u (-sigma) (Or.inl hu.ne')).smul
      ((continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp (hF u hu).continuousAt)).cexp)).continuousWithinAt
  have hprim (v : ℝ) (hv : v ∈ Icc a b) : ‖∫ u in a..v, E u‖ ≤
      4 * a ^ (-sigma) / g := by
    apply OscillatoryIntegral.norm_integral_rpow_smul_cexp_phase_le_of_monotone_deriv_local
      hv.1 ha hg hs (fun u hu => hF u (ha.trans_le hu.1))
    · rcases hmono with hmono | hanti
      · exact Or.inl (hmono.mono (Icc_subset_Icc le_rfl hv.2))
      · exact Or.inr (hanti.mono (Icc_subset_Icc le_rfl hv.2))
    · intro u hu
      exact hgap u ⟨hu.1, hu.2.trans hv.2⟩
  calc
    _ = ‖∫ u in a..b, explicitIntervalPlateau x N u • E u‖ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      simp only [explicitComplexMellinAmplitude, explicitMellinAmplitude, mellinRpow,
        E, Complex.real_smul, Complex.ofReal_mul]
      ring
    _ ≤ (1 + 4 * C₁) * (4 * a ^ (-sigma) / g) :=
      norm_explicitPlateau_restricted_integral_le_primitive
        hx hxN hxa hab hbN (by positivity) hC₁0 hC₁ hE hprim
    _ = _ := by ring

end HardyTheorem.AFE
