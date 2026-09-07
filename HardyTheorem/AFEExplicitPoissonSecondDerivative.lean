import HardyTheorem.AFEExplicitPoissonRestrictedCutoff

/-! Cutoff-uniform variation and curvature bounds for the Mellin amplitude. -/

open Complex Set MeasureTheory

namespace HardyTheorem.AFE

private theorem abs_explicitMellinDeriv_le_supported
    {sigma x N u : ℝ} (hs : 0 ≤ sigma) (hu : 0 < u) :
    |explicitMellinAmplitudeDeriv sigma x N u| ≤
      |explicitIntervalPlateauDeriv x N u| * u ^ (-sigma) +
        sigma * u ^ (-sigma - 1) := by
  have hw0 := explicitIntervalPlateau_nonneg x N u
  have hw1 := explicitIntervalPlateau_le_one x N u
  have habspow (p : ℝ) : |u ^ p| = u ^ p :=
    abs_of_nonneg (Real.rpow_nonneg hu.le p)
  rw [explicitMellinAmplitudeDeriv, mellinRpow, mellinRpowDeriv]
  calc
    _ ≤ |explicitIntervalPlateauDeriv x N u * u ^ (-sigma)| +
        |explicitIntervalPlateau x N u * ((-sigma) * u ^ (-sigma - 1))| :=
      abs_add_le _ _
    _ = |explicitIntervalPlateauDeriv x N u| * u ^ (-sigma) +
        explicitIntervalPlateau x N u * (sigma * u ^ (-sigma - 1)) := by
      simp only [abs_mul, habspow, abs_of_nonneg hw0, abs_neg, abs_of_nonneg hs]
    _ ≤ _ := add_le_add le_rfl
      (mul_le_of_le_one_left
        (show 0 ≤ sigma * u ^ (-sigma - 1) by positivity) hw1)

/-- Total variation on an arbitrary positive subinterval of the support.
The cutoff part is confined to the two unit transitions. -/
theorem intervalIntegral_abs_explicitMellinDeriv_restricted_le
    {C₁ sigma x N a b : ℝ} (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N)
    (hxa : x - 1 ≤ a) (hab : a ≤ b) (hbN : b ≤ N + 1)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    (∫ u in a..b, |explicitMellinAmplitudeDeriv sigma x N u|) ≤
      (4 * C₁ + 1) * a ^ (-sigma) := by
  have ha : 0 < a := by linarith
  have hpos {u : ℝ} (hu : u ∈ Icc a b) : 0 < u := ha.trans_le hu.1
  have hpow (p : ℝ) : ContinuousOn (fun u : ℝ => u ^ p) (Icc a b) :=
    fun u hu => (Real.continuousAt_rpow_const u p (Or.inl (hpos hu).ne')).continuousWithinAt
  have hwd : Continuous (explicitIntervalPlateauDeriv x N) :=
    continuous_iff_continuousAt.mpr fun u =>
      (explicitIntervalPlateauDeriv_hasDerivAt x N u).continuousAt
  have hA : ContinuousOn (explicitMellinAmplitudeDeriv sigma x N) (Icc a b) :=
    fun _ hu => (explicitMellinAmplitudeDeriv_hasDerivAt sigma x N
      (hpos hu).ne').continuousAt.continuousWithinAt
  let G₁ : ℝ → ℝ := fun u => |explicitIntervalPlateauDeriv x N u| * u ^ (-sigma)
  let G₀ : ℝ → ℝ := fun u => u ^ (-sigma - 1)
  have hG₁ : IntervalIntegrable G₁ volume a b :=
    (hwd.continuousOn.abs.mul (hpow (-sigma))).intervalIntegrable_of_Icc hab
  have hG₀ : IntervalIntegrable G₀ volume a b :=
    (hpow (-sigma - 1)).intervalIntegrable_of_Icc hab
  have hdom : (∫ u in a..b, |explicitMellinAmplitudeDeriv sigma x N u|) ≤
      (∫ u in a..b, G₁ u) + sigma * ∫ u in a..b, G₀ u := by
    calc
      _ ≤ ∫ u in a..b, G₁ u + sigma * G₀ u := by
        apply intervalIntegral.integral_mono_on hab (hA.abs.intervalIntegrable_of_Icc hab)
          (hG₁.add (hG₀.const_mul sigma))
        intro u hu
        exact abs_explicitMellinDeriv_le_supported hs.le (hpos hu)
      _ = _ := by rw [intervalIntegral.integral_add hG₁ (hG₀.const_mul sigma),
        intervalIntegral.integral_const_mul]
  have hb₁ : (∫ u in a..b, G₁ u) ≤ 4 * C₁ * a ^ (-sigma) := by
    calc
      _ ≤ ∫ u in a..b, |explicitIntervalPlateauDeriv x N u| * a ^ (-sigma) := by
        apply intervalIntegral.integral_mono_on hab hG₁
          ((hwd.abs.intervalIntegrable a b).mul_const _)
        intro u hu
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos ha hu.1 (neg_nonpos.mpr hs.le)) (abs_nonneg _)
      _ = (∫ u in a..b, |explicitIntervalPlateauDeriv x N u|) * a ^ (-sigma) :=
        intervalIntegral.integral_mul_const _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (intervalIntegral_abs_plateauDeriv_restricted_le hx hxN hxa hab hbN hC₁0 hC₁)
        (Real.rpow_nonneg ha.le _)
  have hb₀ : (∫ u in a..b, G₀ u) ≤ a ^ (-sigma) / sigma := by
    have h := MathlibAux.intervalIntegral_rpow_le_left_endpoint
      (r := -sigma - 1) ha hab (by linarith)
    simpa only [show -sigma - 1 + 1 = -sigma by ring,
      show -(-sigma - 1) - 1 = sigma by ring] using h
  refine hdom.trans ((add_le_add hb₁
    (mul_le_mul_of_nonneg_left hb₀ hs.le)).trans_eq ?_)
  field_simp [hs.ne']

/-- Primitive transfer through the complete Mellin amplitude, with the
explicit endpoint and total-variation costs already discharged. -/
theorem norm_explicitMellin_restricted_integral_le_primitive
    {E : ℝ → ℂ} {C₁ sigma x N a b B : ℝ}
    (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N)
    (hxa : x - 1 ≤ a) (hab : a ≤ b) (hbN : b ≤ N + 1) (hB : 0 ≤ B)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hE : ContinuousOn E (Ioi 0))
    (hprim : ∀ v ∈ Icc a b, ‖∫ u in a..v, E u‖ ≤ B) :
    ‖∫ u in a..b, explicitComplexMellinAmplitude sigma x N u * E u‖ ≤
      (4 * C₁ + 2) * a ^ (-sigma) * B := by
  have ha : 0 < a := by linarith
  have hpos {u : ℝ} (hu : u ∈ Icc a b) : 0 < u := ha.trans_le hu.1
  have hAd : ContinuousOn (explicitMellinAmplitudeDeriv sigma x N) (Icc a b) :=
    fun _ hu => (explicitMellinAmplitudeDeriv_hasDerivAt sigma x N
      (hpos hu).ne').continuousAt.continuousWithinAt
  have hb : |explicitMellinAmplitude sigma x N b| ≤ a ^ (-sigma) := by
    have h := norm_explicitComplexMellinAmplitude_le sigma x N (ha.trans_le hab)
    have h' : |explicitMellinAmplitude sigma x N b| ≤ b ^ (-sigma) := by
      simpa only [explicitComplexMellinAmplitude, Complex.norm_real, Real.norm_eq_abs] using h
    exact h'.trans (Real.rpow_le_rpow_of_nonpos ha hab (neg_nonpos.mpr hs.le))
  calc
    _ = ‖∫ u in a..b, explicitMellinAmplitude sigma x N u • E u‖ := by
      simp only [explicitComplexMellinAmplitude, Complex.real_smul]
    _ ≤ (|explicitMellinAmplitude sigma x N b| +
        ∫ u in a..b, |explicitMellinAmplitudeDeriv sigma x N u|) * B :=
      norm_intervalIntegral_real_smul_le_primitive ha hab
        (fun _ hu => explicitMellinAmplitude_hasDerivAt sigma x N (hpos hu).ne') hAd hE hprim
    _ ≤ (a ^ (-sigma) + (4 * C₁ + 1) * a ^ (-sigma)) * B :=
      mul_le_mul_of_nonneg_right (add_le_add hb
        (intervalIntegral_abs_explicitMellinDeriv_restricted_le
          hs hx hxN hxa hab hbN hC₁0 hC₁)) hB
    _ = _ := by ring

/-- Uniform curvature cancellation on restricted support intervals.  Neither
an amplitude-variation bound nor a primitive estimate is assumed. -/
theorem norm_explicitMellin_restricted_phaseIntegral_le_secondDerivative
    {F : ℝ → ℝ} {C₁ sigma x N a b r : ℝ}
    (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N)
    (hxa : x - 1 ≤ a) (hab : a ≤ b) (hbN : b ≤ N + 1) (hr : 0 < r)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hF : ∀ u : ℝ, 0 < u → ContDiffAt ℝ 2 F u)
    (hsecond : (∀ u ∈ Icc a b, r ≤ iteratedDeriv 2 F u) ∨
      (∀ u ∈ Icc a b, iteratedDeriv 2 F u ≤ -r)) :
    ‖∫ u in a..b, explicitComplexMellinAmplitude sigma x N u *
      Complex.exp (I * F u)‖ ≤ 12 * (4 * C₁ + 2) * a ^ (-sigma) / Real.sqrt r := by
  have ha : 0 < a := by linarith
  let E : ℝ → ℂ := fun u => Complex.exp (I * F u)
  have hE : ContinuousOn E (Ioi 0) := by
    intro u hu
    exact ((continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp (hF u hu).continuousAt)).cexp).continuousWithinAt
  have hprim (v : ℝ) (hv : v ∈ Icc a b) :
      ‖∫ u in a..v, E u‖ ≤ 12 / Real.sqrt r := by
    apply OscillatoryIntegral.norm_integral_cexp_phase_le_of_second_deriv_on_Icc
      hv.1 hr (fun u hu => hF u (ha.trans_le hu.1))
    rcases hsecond with hp | hn
    · exact Or.inl (fun u hu => hp u ⟨hu.1, hu.2.trans hv.2⟩)
    · exact Or.inr (fun u hu => hn u ⟨hu.1, hu.2.trans hv.2⟩)
  calc
    _ ≤ (4 * C₁ + 2) * a ^ (-sigma) * (12 / Real.sqrt r) :=
      norm_explicitMellin_restricted_integral_le_primitive
        hs hx hxN hxa hab hbN (by positivity) hC₁0 hC₁ hE hprim
    _ = _ := by ring

end HardyTheorem.AFE
