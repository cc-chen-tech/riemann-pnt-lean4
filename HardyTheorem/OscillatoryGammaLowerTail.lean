import HardyTheorem.OscillatoryGammaTail

/-! The lower nonstationary tail, uniform down to the integrable origin. -/

open Real Complex Set MeasureTheory Filter Topology

namespace HardyTheorem.OscillatoryGammaTail

private theorem mellin_linear_eq_phase (sigma c t : ℝ) {u : ℝ} (hu : 0 < u) :
    (u : ℂ) ^ (-((sigma : ℂ) + I * t)) * Complex.exp (I * (c * u)) =
      u ^ (-sigma) • Complex.exp (I * (c * u - t * Real.log u)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'),
    ← Complex.ofReal_log hu.le, Real.rpow_def_of_pos hu, Complex.real_smul,
    Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A first integration by parts whose bound is independent of the lower
cutoff.  The monotone quotient absorbs the singular radial amplitude. -/
theorem norm_intervalIntegral_mellin_linear_lower_le
    {sigma c t A x : ℝ} (hs : sigma < 1) (hc : 0 ≤ c)
    (hA : 0 < A) (hAx : A ≤ x) (hgap : c * x < t) :
    ‖∫ u in A..x, (u : ℂ) ^ (-((sigma : ℂ) + I * t)) *
      Complex.exp (I * (c * u))‖ ≤ 2 * x ^ (1 - sigma) / (t - c * x) := by
  let r : ℝ → ℝ := fun u => u ^ (1 - sigma) / (t - c * u)
  let F : ℝ → ℝ := fun u => c * u - t * Real.log u
  let E : ℝ → ℂ := fun u => Complex.exp (I * F u)
  let E' : ℝ → ℂ := fun u => E u * (I * ((c - t / u : ℝ) : ℂ))
  let f : ℝ → ℂ := fun u => (u : ℂ) ^ (-((sigma : ℂ) + I * t)) *
    Complex.exp (I * (c * u))
  have hpos {u : ℝ} (hu : u ∈ Icc A x) : 0 < u := hA.trans_le hu.1
  have hden {u : ℝ} (hu : u ∈ Icc A x) : 0 < t - c * u := by
    have := mul_le_mul_of_nonneg_left hu.2 hc
    linarith
  have hr0 {u : ℝ} (hu : u ∈ Icc A x) : 0 ≤ r u :=
    div_nonneg (Real.rpow_nonneg (hpos hu).le _) (hden hu).le
  have hrmono : MonotoneOn r (Icc A x) := by
    intro u hu v hv huv
    dsimp only [r]
    calc
      _ ≤ v ^ (1 - sigma) / (t - c * u) :=
        div_le_div_of_nonneg_right
          (Real.rpow_le_rpow (hpos hu).le huv (by linarith)) (hden hu).le
      _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg (hpos hv).le _)
        (hden hv) (sub_le_sub_left (mul_le_mul_of_nonneg_left huv hc) t)
  have hrdiff {u : ℝ} (hu : u ∈ Icc A x) : DifferentiableAt ℝ r u := by
    exact (Real.hasDerivAt_rpow_const (p := 1 - sigma)
      (Or.inl (hpos hu).ne')).differentiableAt.div
        ((differentiableAt_const t).sub ((differentiableAt_const c).mul differentiableAt_id))
        (hden hu).ne'
  have hrint : IntervalIntegrable (deriv r) volume A x := by
    have hm : MonotoneOn r (uIcc A x) := by simpa only [uIcc_of_le hAx] using hrmono
    exact hm.intervalIntegrable_deriv
  have hvar : (∫ u in A..x, |deriv r u|) = r x - r A := by
    calc
      _ = ∫ u in A..x, deriv r u := by
        apply intervalIntegral.integral_congr_ae
        rw [uIoc_of_le hAx]
        have hne : ∀ᵐ u : ℝ, u ≠ x := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with u hux hu
        have hu' : u ∈ Ioo A x := ⟨hu.1, lt_of_le_of_ne hu.2 hux⟩
        have hn : 0 ≤ deriv r u := by
          rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hu'.1 hu'.2)]
          exact hrmono.derivWithin_nonneg
        exact abs_of_nonneg hn
      _ = _ := intervalIntegral.integral_deriv_eq_sub
        (fun u hu => hrdiff (by simpa only [uIcc_of_le hAx] using hu)) hrint
  have hF {u : ℝ} (hu : u ∈ Icc A x) : HasDerivAt F (c - t / u) u := by
    simpa [F, div_eq_mul_inv] using!
      ((hasDerivAt_id u).const_mul c).sub
        ((Real.hasDerivAt_log (hpos hu).ne').const_mul t)
  have hE {u : ℝ} (hu : u ∈ Icc A x) : HasDerivAt E (E' u) u := by
    simpa only [E, E'] using ((hF hu).ofReal_comp.const_mul I).cexp
  have hEcont : ContinuousOn E (Icc A x) := fun _ hu =>
    (hE hu).continuousAt.continuousWithinAt
  have hE'int : IntervalIntegrable E' volume A x := by
    apply ContinuousOn.intervalIntegrable_of_Icc hAx
    apply hEcont.mul
    apply continuous_const.continuousOn.mul
    apply Complex.continuous_ofReal.continuousOn.comp
    · exact continuous_const.continuousOn.sub
        (continuous_const.continuousOn.div continuous_id.continuousOn
          (fun _ hu => (hpos hu).ne'))
    · intro u _
      exact mem_univ _
  have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (u := r) (u' := deriv r) (v := E) (v' := E')
    (fun u hu => (hrdiff (by simpa only [uIcc_of_le hAx] using hu)).hasDerivAt)
    (fun u hu => hE (by simpa only [uIcc_of_le hAx] using hu)) hrint hE'int
  have halg {u : ℝ} (hu : u ∈ Icc A x) : r u * (c - t / u) = -u ^ (-sigma) := by
    have hp : u ^ (1 - sigma) = u ^ (-sigma) * u := by
      rw [show 1 - sigma = -sigma + 1 by ring, Real.rpow_add (hpos hu), Real.rpow_one]
    dsimp only [r]
    rw [hp, div_mul_eq_mul_div, div_eq_iff (hden hu).ne']
    field_simp [(hpos hu).ne']
    ring
  have hleft : (∫ u in A..x, r u • E' u) = -I * (∫ u in A..x, f u) := by
    calc
      _ = ∫ u in A..x, -I * f u := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hu' : u ∈ Icc A x := by simpa only [uIcc_of_le hAx] using hu
        have heq : f u = u ^ (-sigma) • E u := by
          simpa only [f, E, F, Complex.ofReal_sub, Complex.ofReal_mul] using
            mellin_linear_eq_phase sigma c t (hpos hu')
        have hcplx : (r u : ℂ) * ((c - t / u : ℝ) : ℂ) =
            -((u ^ (-sigma) : ℝ) : ℂ) := by
          exact_mod_cast halg hu'
        change r u • E' u = -I * f u
        rw [heq]
        simp only [E', Complex.real_smul]
        calc
          _ = I * ((r u : ℂ) * ((c - t / u : ℝ) : ℂ)) * E u := by ring
          _ = _ := by rw [hcplx]; ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hparts' := hleft.symm.trans hparts
  have hrem : ‖∫ u in A..x, deriv r u • E u‖ ≤ r x - r A := by
    rw [← hvar]
    refine intervalIntegral.norm_integral_le_of_norm_le hAx ?_ hrint.abs
    filter_upwards with u _
    simp [E, Real.norm_eq_abs]
  have hend : ‖r x • E x - r A • E A‖ ≤ r x + r A := by
    simpa [E, Real.norm_eq_abs, abs_of_nonneg (hr0 ⟨hAx, le_rfl⟩),
      abs_of_nonneg (hr0 ⟨le_rfl, hAx⟩)] using norm_sub_le (r x • E x) (r A • E A)
  calc
    _ = ‖-I * (∫ u in A..x, f u)‖ := by simp [f]
    _ = ‖r x • E x - r A • E A - ∫ u in A..x, deriv r u • E u‖ := by rw [hparts']
    _ ≤ ‖r x • E x - r A • E A‖ + ‖∫ u in A..x, deriv r u • E u‖ := norm_sub_le _ _
    _ ≤ (r x + r A) + (r x - r A) := add_le_add hend hrem
    _ = _ := by dsimp only [r]; ring

/-- Local integrability at zero passes the same uniform bound to the full
lower Gamma tail.  There is no unproved limiting hypothesis. -/
theorem norm_intervalIntegral_mellin_linear_zero_lower_le
    {sigma c t x : ℝ} (hs : sigma < 1) (hc : 0 ≤ c)
    (hx : 0 < x) (hgap : c * x < t) :
    ‖∫ u in (0 : ℝ)..x, (u : ℂ) ^ (-((sigma : ℂ) + I * t)) *
      Complex.exp (I * (c * u))‖ ≤ 2 * x ^ (1 - sigma) / (t - c * x) := by
  let f : ℝ → ℂ := fun u => (u : ℂ) ^ (-((sigma : ℂ) + I * t)) *
    Complex.exp (I * (c * u))
  have hi (a b : ℝ) : IntervalIntegrable f volume a b := by
    apply (intervalIntegral.intervalIntegrable_cpow' (r := -((sigma : ℂ) + I * t))
      (by simp; linarith)).mul_continuousOn
    fun_prop
  have hcont : Continuous (fun A : ℝ => ∫ u in A..x, f u) := by
    have heq : (fun A : ℝ => ∫ u in A..x, f u) =
        fun A : ℝ => -(∫ u in x..A, f u) := by
      funext A
      exact intervalIntegral.integral_symm x A
    rw [heq]
    exact (intervalIntegral.continuous_primitive hi x).neg
  have hlim : Tendsto (fun A : ℝ => ‖∫ u in A..x, f u‖) (𝓝[>] (0 : ℝ))
      (𝓝 ‖∫ u in (0 : ℝ)..x, f u‖) :=
    (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).norm
  apply le_of_tendsto hlim
  have hnear : ∀ᶠ A : ℝ in 𝓝[>] (0 : ℝ), A < x :=
    nhdsWithin_le_nhds (Iio_mem_nhds hx)
  filter_upwards [self_mem_nhdsWithin, hnear] with A hA hAx
  exact norm_intervalIntegral_mellin_linear_lower_le hs hc hA hAx.le hgap

end HardyTheorem.OscillatoryGammaTail
