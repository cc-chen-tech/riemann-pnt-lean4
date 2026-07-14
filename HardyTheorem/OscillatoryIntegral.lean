import Mathlib

open Complex Filter MeasureTheory Set Topology

namespace HardyTheorem.OscillatoryIntegral

private theorem uniform_sign_of_continuous_abs_ge
    {f : ℝ → ℝ} {a b m : ℝ} (hab : a ≤ b) (hm : 0 < m)
    (hf : Continuous f) (haway : ∀ x ∈ Icc a b, m ≤ |f x|) :
    (∀ x ∈ Icc a b, m ≤ f x) ∨
      (∀ x ∈ Icc a b, f x ≤ -m) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  rcases (le_abs.mp (haway a ha)) with ha_pos | ha_neg
  · left
    intro x hx
    by_contra hx_pos
    have hx_neg : f x ≤ -m := by
      rcases le_abs.mp (haway x hx) with h | h
      · exact False.elim (hx_pos h)
      · linarith
    have h_cont : ContinuousOn f (uIcc a x) := hf.continuousOn
    have h_zero_mem : 0 ∈ uIcc (f a) (f x) := by
      rw [mem_uIcc]
      exact Or.inr ⟨by linarith, by linarith⟩
    have h_image : uIcc (f a) (f x) ⊆ f '' uIcc a x :=
      intermediate_value_uIcc h_cont
    obtain ⟨y, hy, hy_zero⟩ := h_image h_zero_mem
    have hax : a ≤ x := hx.1
    have hy' : y ∈ Icc a b := by
      rw [uIcc_of_le hax] at hy
      exact ⟨hy.1, hy.2.trans hx.2⟩
    have := haway y hy'
    rw [hy_zero, abs_zero] at this
    linarith
  · right
    intro x hx
    have ha_neg' : f a ≤ -m := by linarith
    by_contra hx_neg
    have hx_pos : m ≤ f x := by
      rcases le_abs.mp (haway x hx) with h | h
      · exact h
      · exact False.elim (hx_neg (by linarith))
    have h_cont : ContinuousOn f (uIcc a x) := hf.continuousOn
    have h_zero_mem : 0 ∈ uIcc (f a) (f x) := by
      rw [mem_uIcc]
      exact Or.inl ⟨by linarith, by linarith⟩
    have h_image : uIcc (f a) (f x) ⊆ f '' uIcc a x :=
      intermediate_value_uIcc h_cont
    obtain ⟨y, hy, hy_zero⟩ := h_image h_zero_mem
    have hax : a ≤ x := hx.1
    have hy' : y ∈ Icc a b := by
      rw [uIcc_of_le hax] at hy
      exact ⟨hy.1, hy.2.trans hx.2⟩
    have := haway y hy'
    rw [hy_zero, abs_zero] at this
    linarith

private theorem integral_abs_deriv_eq_abs_sub_of_monotone
    {q : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hq_diff : ∀ x ∈ Icc a b, DifferentiableAt ℝ q x)
    (hq_int : IntervalIntegrable (deriv q) MeasureTheory.volume a b)
    (hq_mono : MonotoneOn q (Icc a b) ∨ AntitoneOn q (Icc a b)) :
    ∫ x in a..b, |deriv q x| = |q b - q a| := by
  have h_ftc : ∫ x in a..b, deriv q x = q b - q a := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun x hx => hq_diff x (by simpa [uIcc_of_le hab] using hx)) hq_int
  rcases hq_mono with hmono | hanti
  · have h_deriv_nonneg {x : ℝ} (hx : x ∈ Ioo a b) : 0 ≤ deriv q x := by
      rw [← derivWithin_of_mem_nhds
        (Icc_mem_nhds (a := a) (b := b) hx.1 hx.2)]
      exact hmono.derivWithin_nonneg
    have h_abs : ∫ x in a..b, |deriv q x| = ∫ x in a..b, deriv q x := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le hab]
      have hne : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
      filter_upwards [hne] with x hxb hx
      rw [abs_of_nonneg (h_deriv_nonneg ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩)]
    rw [h_abs, h_ftc]
    exact (abs_of_nonneg (sub_nonneg.mpr
      (hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab))).symm
  · have h_deriv_nonpos {x : ℝ} (hx : x ∈ Ioo a b) : deriv q x ≤ 0 := by
      rw [← derivWithin_of_mem_nhds
        (Icc_mem_nhds (a := a) (b := b) hx.1 hx.2)]
      exact hanti.derivWithin_nonpos
    have h_abs : ∫ x in a..b, |deriv q x| = ∫ x in a..b, -deriv q x := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le hab]
      have hne : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
      filter_upwards [hne] with x hxb hx
      rw [abs_of_nonpos (h_deriv_nonpos ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩)]
    rw [h_abs, intervalIntegral.integral_neg, h_ftc]
    have hsub : q b - q a ≤ 0 :=
      sub_nonpos.mpr (hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
    rw [abs_of_nonpos hsub]

theorem norm_integral_cexp_phase_le_of_monotone_deriv
    {F : ℝ → ℝ} {a b m : ℝ}
    (hab : a ≤ b) (hm : 0 < m)
    (hF : ContDiff ℝ 2 F)
    (hmono : MonotoneOn (deriv F) (Icc a b) ∨
      AntitoneOn (deriv F) (Icc a b))
    (haway : ∀ x ∈ Icc a b, m ≤ |deriv F x|) :
    ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤ 4 / m := by
  let q : ℝ → ℝ := fun x => (deriv F x)⁻¹
  let E : ℝ → ℂ := fun x => Complex.exp (I * F x)
  let E' : ℝ → ℂ := fun x => E x * (I * ((deriv F x : ℝ) : ℂ))
  have hderiv_cont : Continuous (deriv F) := hF.continuous_deriv (by norm_num)
  have hsign := uniform_sign_of_continuous_abs_ge hab hm hderiv_cont haway
  have hp_ne {x : ℝ} (hx : x ∈ Icc a b) : deriv F x ≠ 0 := by
    intro hz
    have h := haway x hx
    rw [hz, abs_zero] at h
    linarith
  have hq_diff : ∀ x ∈ Icc a b, DifferentiableAt ℝ q x := by
    intro x hx
    simpa [q] using (hF.differentiable_deriv_two x).inv (hp_ne hx)
  have hq_mono : MonotoneOn q (Icc a b) ∨ AntitoneOn q (Icc a b) := by
    rcases hsign with hpos | hneg
    · rcases hmono with hpmono | hpanti
      · right
        intro x hx y hy hxy
        exact inv_anti₀ (lt_of_lt_of_le hm (hpos x hx)) (hpmono hx hy hxy)
      · left
        intro x hx y hy hxy
        exact inv_anti₀ (lt_of_lt_of_le hm (hpos y hy)) (hpanti hx hy hxy)
    · rcases hmono with hpmono | hpanti
      · right
        intro x hx y hy hxy
        exact (inv_le_inv_of_neg (lt_of_le_of_lt (hneg y hy) (neg_neg_of_pos hm))
          (lt_of_le_of_lt (hneg x hx) (neg_neg_of_pos hm))).2 (hpmono hx hy hxy)
      · left
        intro x hx y hy hxy
        exact (inv_le_inv_of_neg (lt_of_le_of_lt (hneg x hx) (neg_neg_of_pos hm))
          (lt_of_le_of_lt (hneg y hy) (neg_neg_of_pos hm))).2 (hpanti hx hy hxy)
  have hq_int : IntervalIntegrable (deriv q) MeasureTheory.volume a b := by
    rcases hq_mono with hqmono | hqanti
    · have hqm : MonotoneOn q (uIcc a b) := by
        simpa [uIcc_of_le hab] using hqmono
      exact hqm.intervalIntegrable_deriv
    · have hqm : MonotoneOn (fun x => -q x) (uIcc a b) := by
        simpa [uIcc_of_le hab] using hqanti.neg
      apply hqm.intervalIntegrable_deriv.neg.congr_ae
      filter_upwards with x
      change -(deriv (-q) x) = deriv q x
      rw [deriv.neg]
      simp
  have hvariation : ∫ x in a..b, |deriv q x| = |q b - q a| :=
    integral_abs_deriv_eq_abs_sub_of_monotone hab hq_diff hq_int hq_mono
  have hq_abs {x : ℝ} (hx : x ∈ Icc a b) : |q x| ≤ 1 / m := by
    have hp_abs_pos : 0 < |deriv F x| := abs_pos.mpr (hp_ne hx)
    have hinv : |deriv F x|⁻¹ ≤ m⁻¹ :=
      (inv_le_inv₀ hp_abs_pos hm).2 (haway x hx)
    simpa [q, abs_inv, one_div] using hinv
  have hq_endpoints : |q a| + |q b| ≤ 2 / m := by
    have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
    have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
    have := add_le_add (hq_abs ha) (hq_abs hb)
    calc
      |q a| + |q b| ≤ 1 / m + 1 / m := this
      _ = 2 / m := by ring
  have hq_variation_le : |q b - q a| ≤ 2 / m := by
    calc
      |q b - q a| ≤ |q b| + |q a| := abs_sub _ _
      _ = |q a| + |q b| := add_comm _ _
      _ ≤ 2 / m := hq_endpoints
  have hE_deriv : ∀ x, HasDerivAt E (E' x) x := by
    intro x
    have hreal : HasDerivAt (fun y : ℝ => (F y : ℂ))
        ((deriv F x : ℝ) : ℂ) x :=
      (hF.differentiable (by norm_num) x).hasDerivAt.ofReal_comp
    have harg : HasDerivAt (fun y : ℝ => I * (F y : ℂ))
        (I * ((deriv F x : ℝ) : ℂ)) x := hreal.const_mul I
    simpa [E, E', mul_comm, mul_left_comm, mul_assoc] using harg.cexp
  have hE'_cont : Continuous E' := by
    have hE_cont : Continuous E := by
      exact continuous_iff_continuousAt.mpr fun x => (hE_deriv x).continuousAt
    have hp_complex : Continuous (fun x : ℝ => ((deriv F x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (show Continuous (fun x : ℝ => deriv F x) from hderiv_cont)
    exact hE_cont.mul (continuous_const.mul hp_complex)
  have hE'_int : IntervalIntegrable E' MeasureTheory.volume a b :=
    hE'_cont.intervalIntegrable a b
  have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (a := a) (b := b) (u := q) (u' := deriv q) (v := E) (v' := E')
    (fun x hx => (hq_diff x (by simpa [uIcc_of_le hab] using hx)).hasDerivAt)
    (fun x _ => hE_deriv x) hq_int hE'_int
  have hleft : (∫ x in a..b, q x • E' x) = I * ∫ x in a..b, E x := by
    calc
      (∫ x in a..b, q x • E' x) = ∫ x in a..b, I * E x := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc a b := by simpa [uIcc_of_le hab] using hx
        dsimp [q, E']
        rw [Complex.ofReal_inv]
        have hpc : ((deriv F x : ℝ) : ℂ) ≠ 0 :=
          ofReal_ne_zero.mpr (hp_ne hx')
        calc
          (((deriv F x : ℝ) : ℂ)⁻¹) *
              (E x * (I * ((deriv F x : ℝ) : ℂ))) =
              I * ((((deriv F x : ℝ) : ℂ)⁻¹) * ((deriv F x : ℝ) : ℂ)) * E x := by ring
          _ = I * E x := by rw [inv_mul_cancel₀ hpc, mul_one]
      _ = I * ∫ x in a..b, E x := by
        exact intervalIntegral.integral_const_mul I E
  have hparts' : I * ∫ x in a..b, E x =
      q b • E b - q a • E a - ∫ x in a..b, deriv q x • E x :=
    hleft.symm.trans hparts
  have hrem : ‖∫ x in a..b, deriv q x • E x‖ ≤ ∫ x in a..b, |deriv q x| := by
    refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ hq_int.abs
    filter_upwards with x _
    simp [E, Real.norm_eq_abs]
  calc
    ‖∫ x in a..b, Complex.exp (I * F x)‖ = ‖I * ∫ x in a..b, E x‖ := by
      simp [E]
    _ = ‖q b • E b - q a • E a - ∫ x in a..b, deriv q x • E x‖ := by
      rw [hparts']
    _ ≤ ‖q b • E b - q a • E a‖ + ‖∫ x in a..b, deriv q x • E x‖ :=
      norm_sub_le _ _
    _ ≤ (|q b| + |q a|) + ∫ x in a..b, |deriv q x| := by
      gcongr
      · exact (norm_sub_le _ _).trans_eq (by simp [E, Real.norm_eq_abs])
    _ = (|q a| + |q b|) + |q b - q a| := by rw [hvariation]; ring
    _ ≤ 2 / m + 2 / m := add_le_add hq_endpoints hq_variation_le
    _ = 4 / m := by ring

/-- The phase appearing after inserting the first zeta approximation into Hardy's integral. -/
noncomputable def hardyPhase (n : ℕ) (t : ℝ) : ℝ :=
  t / 2 *
      (Real.log (t / (2 * Real.pi * ((n : ℝ) ^ 2))) - 1) -
    Real.pi / 8

theorem deriv_hardyPhase {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t) :
    deriv (hardyPhase n) t =
      (1 / 2) * Real.log (t / (2 * Real.pi * ((n : ℝ) ^ 2))) := by
  have hn_real : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hc : 2 * Real.pi * ((n : ℝ) ^ 2) ≠ 0 := by
    positivity
  have harg_ne : t / (2 * Real.pi * ((n : ℝ) ^ 2)) ≠ 0 :=
    div_ne_zero (ne_of_gt ht) hc
  have h_arg :
      HasDerivAt (fun x : ℝ => x / (2 * Real.pi * ((n : ℝ) ^ 2)))
        (1 / (2 * Real.pi * ((n : ℝ) ^ 2))) t := by
    convert (hasDerivAt_id t).div_const (2 * Real.pi * ((n : ℝ) ^ 2)) using 1
  have h_log := h_arg.log harg_ne
  have h_linear : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) t := by
    simpa using (hasDerivAt_id t).div_const 2
  have h_phase :
      HasDerivAt (hardyPhase n)
        ((1 / 2) *
          (Real.log (t / (2 * Real.pi * ((n : ℝ) ^ 2))) - 1) +
          (t / 2) *
            ((1 / (2 * Real.pi * ((n : ℝ) ^ 2))) /
              (t / (2 * Real.pi * ((n : ℝ) ^ 2))))) t := by
    convert ((h_linear.mul (h_log.sub_const 1)).sub_const (Real.pi / 8)) using 1
  rw [h_phase.deriv]
  field_simp [ne_of_gt ht, hc]
  ring

theorem iteratedDeriv_two_hardyPhase
    {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (hardyPhase n) t = 1 / (2 * t) := by
  let g : ℝ → ℝ := fun x =>
    (1 / 2) * Real.log (x / (2 * Real.pi * ((n : ℝ) ^ 2)))
  have h_event : deriv (hardyPhase n) =ᶠ[𝓝 t] g := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact deriv_hardyPhase hn hx
  rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h_event.deriv_eq]
  have hn_real : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hc : 2 * Real.pi * ((n : ℝ) ^ 2) ≠ 0 := by
    positivity
  have harg_ne : t / (2 * Real.pi * ((n : ℝ) ^ 2)) ≠ 0 :=
    div_ne_zero (ne_of_gt ht) hc
  have h_arg :
      HasDerivAt (fun x : ℝ => x / (2 * Real.pi * ((n : ℝ) ^ 2)))
        (1 / (2 * Real.pi * ((n : ℝ) ^ 2))) t := by
    convert (hasDerivAt_id t).div_const (2 * Real.pi * ((n : ℝ) ^ 2)) using 1
  have h_g :
      HasDerivAt g
        ((1 / 2) *
          ((1 / (2 * Real.pi * ((n : ℝ) ^ 2))) /
            (t / (2 * Real.pi * ((n : ℝ) ^ 2))))) t := by
    convert (h_arg.log harg_ne).const_mul (1 / 2) using 1
  rw [h_g.deriv]
  field_simp [ne_of_gt ht, hc]

end HardyTheorem.OscillatoryIntegral
