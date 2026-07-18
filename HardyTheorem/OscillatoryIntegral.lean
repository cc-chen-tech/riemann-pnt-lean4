import Mathlib

open Complex Filter MeasureTheory Set Topology

namespace HardyTheorem.OscillatoryIntegral

private theorem uniform_sign_of_continuous_abs_ge
    {f : ℝ → ℝ} {a b m : ℝ} (hab : a ≤ b) (hm : 0 < m)
    (hf : ContinuousOn f (Icc a b)) (haway : ∀ x ∈ Icc a b, m ≤ |f x|) :
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
    have h_cont : ContinuousOn f (uIcc a x) := by
      rw [uIcc_of_le hx.1]
      exact hf.mono (Icc_subset_Icc le_rfl hx.2)
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
    have h_cont : ContinuousOn f (uIcc a x) := by
      rw [uIcc_of_le hx.1]
      exact hf.mono (Icc_subset_Icc le_rfl hx.2)
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

theorem norm_integral_cexp_phase_le_of_monotone_deriv_local
    {F : ℝ → ℝ} {a b m : ℝ}
    (hab : a ≤ b) (hm : 0 < m)
    (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x)
    (hmono : MonotoneOn (deriv F) (Icc a b) ∨
      AntitoneOn (deriv F) (Icc a b))
    (haway : ∀ x ∈ Icc a b, m ≤ |deriv F x|) :
    ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤ 4 / m := by
  let q : ℝ → ℝ := fun x => (deriv F x)⁻¹
  let E : ℝ → ℂ := fun x => Complex.exp (I * F x)
  let E' : ℝ → ℂ := fun x => E x * (I * ((deriv F x : ℝ) : ℂ))
  have hderiv_cont : ContinuousOn (deriv F) (Icc a b) := by
    intro x hx
    exact ((hF x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hsign := uniform_sign_of_continuous_abs_ge hab hm hderiv_cont haway
  have hp_ne {x : ℝ} (hx : x ∈ Icc a b) : deriv F x ≠ 0 := by
    intro hz
    have h := haway x hx
    rw [hz, abs_zero] at h
    linarith
  have hq_diff : ∀ x ∈ Icc a b, DifferentiableAt ℝ q x := by
    intro x hx
    have hp_diff : DifferentiableAt ℝ (deriv F) x :=
      ((hF x hx).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
    simpa [q] using hp_diff.inv (hp_ne hx)
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
  have hE_deriv : ∀ x ∈ Icc a b, HasDerivAt E (E' x) x := by
    intro x hx
    have hreal : HasDerivAt (fun y : ℝ => (F y : ℂ))
        ((deriv F x : ℝ) : ℂ) x :=
      ((hF x hx).differentiableAt (by norm_num)).hasDerivAt.ofReal_comp
    have harg : HasDerivAt (fun y : ℝ => I * (F y : ℂ))
        (I * ((deriv F x : ℝ) : ℂ)) x := hreal.const_mul I
    simpa [E, E', mul_comm, mul_left_comm, mul_assoc] using harg.cexp
  have hE'_cont : ContinuousOn E' (Icc a b) := by
    have hE_cont : ContinuousOn E (Icc a b) := by
      intro x hx
      exact (hE_deriv x hx).continuousAt.continuousWithinAt
    have hp_complex : ContinuousOn (fun x : ℝ => ((deriv F x : ℝ) : ℂ)) (Icc a b) :=
      Complex.continuous_ofReal.continuousOn.comp hderiv_cont (fun _ _ => mem_univ _)
    exact hE_cont.mul (continuous_const.continuousOn.mul hp_complex)
  have hE'_int : IntervalIntegrable E' MeasureTheory.volume a b :=
    hE'_cont.intervalIntegrable_of_Icc hab
  have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (a := a) (b := b) (u := q) (u' := deriv q) (v := E) (v' := E')
    (fun x hx => (hq_diff x (by simpa [uIcc_of_le hab] using hx)).hasDerivAt)
    (fun x hx => hE_deriv x (by simpa [uIcc_of_le hab] using hx)) hq_int hE'_int
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

theorem norm_integral_cexp_phase_le_of_monotone_deriv
    {F : ℝ → ℝ} {a b m : ℝ}
    (hab : a ≤ b) (hm : 0 < m)
    (hF : ContDiff ℝ 2 F)
    (hmono : MonotoneOn (deriv F) (Icc a b) ∨
      AntitoneOn (deriv F) (Icc a b))
    (haway : ∀ x ∈ Icc a b, m ≤ |deriv F x|) :
    ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤ 4 / m :=
  norm_integral_cexp_phase_le_of_monotone_deriv_local hab hm
    (fun _ _ => hF.contDiffAt) hmono haway

/-- The first-derivative oscillatory estimate remains valid after inserting a
positive decreasing power weight.  The constant does not depend on the
length of the interval: integration by parts applies the unweighted estimate
to every initial subinterval. -/
theorem norm_integral_rpow_smul_cexp_phase_le_of_monotone_deriv_local
    {F : ℝ → ℝ} {a b m p : ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hm : 0 < m) (hp : 0 < p)
    (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x)
    (hmono : MonotoneOn (deriv F) (Icc a b) ∨
      AntitoneOn (deriv F) (Icc a b))
    (haway : ∀ x ∈ Icc a b, m ≤ |deriv F x|) :
    ‖∫ x in a..b, x ^ (-p) • Complex.exp (I * F x)‖ ≤
      4 * a ^ (-p) / m := by
  let E : ℝ → ℂ := fun x => Complex.exp (I * F x)
  let G : ℝ → ℂ := fun u => ∫ x in a..u, E x
  let w : ℝ → ℝ := fun x => x ^ (-p)
  let w' : ℝ → ℝ := fun x => (-p) * x ^ (-p - 1)
  have hE_cont : ContinuousOn E (Icc a b) := by
    intro x hx
    exact (continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp
        (hF x hx).continuousAt)).cexp.continuousWithinAt
  have hG_deriv (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt G (E x) x := by
    dsimp only [G]
    have hE_int_ax : IntervalIntegrable E volume a x :=
      (hE_cont.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1
    have hE_at : ContinuousAt E x :=
      (continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp
          (hF x hx).continuousAt)).cexp
    obtain ⟨u, hu_nhds, huF⟩ :=
      (hF x hx).contDiffOn (m := 0) (by norm_num) (by simp)
    obtain ⟨v, hvu, hv_open, hxv⟩ := mem_nhds_iff.mp hu_nhds
    have hE_cont_v : ContinuousOn E v := by
      apply continuousOn_of_forall_continuousAt
      intro y hy
      have huy : u ∈ nhds y :=
        mem_of_superset (hv_open.mem_nhds hy) hvu
      have hFy : ContinuousAt F y :=
        (huF y (hvu hy)).continuousWithinAt.continuousAt huy
      exact (continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp hFy)).cexp
    have hE_meas : StronglyMeasurableAtFilter E (nhds x) volume :=
      hE_cont_v.stronglyMeasurableAtFilter hv_open x hxv
    exact intervalIntegral.integral_hasDerivAt_right
      hE_int_ax hE_meas hE_at
  have hw_deriv : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
    dsimp only [w, w']
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (Real.hasDerivAt_rpow_const (p := -p) (Or.inl hx0))
  have hw'_cont : ContinuousOn w' (Icc a b) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
    exact (continuousAt_const.mul
      (Real.continuousAt_rpow_const x (-p - 1) (Or.inl hx0))).continuousWithinAt
  have hw'_int : IntervalIntegrable w' volume a b :=
    hw'_cont.intervalIntegrable_of_Icc hab
  have hE_int : IntervalIntegrable E volume a b :=
    hE_cont.intervalIntegrable_of_Icc hab
  have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (a := a) (b := b) (u := w) (u' := w') (v := G) (v' := E)
    (fun x hx => hw_deriv x (by simpa [uIcc_of_le hab] using hx))
    (fun x hx => hG_deriv x (by simpa [uIcc_of_le hab] using hx)) hw'_int hE_int
  have hG_zero : G a = 0 := by simp [G]
  have hG_bound : ∀ x ∈ Icc a b, ‖G x‖ ≤ 4 / m := by
    intro x hx
    dsimp only [G]
    apply norm_integral_cexp_phase_le_of_monotone_deriv_local hx.1 hm
      (fun y hy => hF y ⟨hy.1, hy.2.trans hx.2⟩)
    · rcases hmono with hmono | hanti
      · exact Or.inl (hmono.mono (Icc_subset_Icc le_rfl hx.2))
      · exact Or.inr (hanti.mono (Icc_subset_Icc le_rfl hx.2))
    · intro y hy
      exact haway y ⟨hy.1, hy.2.trans hx.2⟩
  have hw_nonneg : ∀ x ∈ Icc a b, 0 ≤ w x := by
    intro x hx
    exact Real.rpow_nonneg (le_of_lt (ha.trans_le hx.1)) (-p)
  have hw'_nonpos : ∀ x ∈ Icc a b, w' x ≤ 0 := by
    intro x hx
    dsimp only [w']
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (Real.rpow_nonneg (le_of_lt (ha.trans_le hx.1)) (-p - 1))
  have hK_nonneg : 0 ≤ 4 / m := by positivity
  have hrem :
      ‖∫ x in a..b, w' x • G x‖ ≤
        (4 / m) * (w a - w b) := by
    have hmajor_int : IntervalIntegrable (fun x => (-w' x) * (4 / m)) volume a b :=
      hw'_int.neg.mul_const (4 / m)
    calc
      ‖∫ x in a..b, w' x • G x‖ ≤
          ∫ x in a..b, (-w' x) * (4 / m) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ hmajor_int
        filter_upwards with x hx
        have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2⟩
        have hrewrite : w' x • G x = (-w' x) • (-G x) := by simp
        have hnorm : ‖(-w' x) • (-G x)‖ = (-w' x) * ‖-G x‖ :=
          norm_smul_of_nonneg (neg_nonneg.mpr (hw'_nonpos x hx')) (-G x)
        rw [hrewrite, hnorm, norm_neg]
        exact mul_le_mul_of_nonneg_left (hG_bound x hx') (neg_nonneg.mpr (hw'_nonpos x hx'))
      _ = (4 / m) * ∫ x in a..b, -w' x := by
        rw [intervalIntegral.integral_mul_const]
        ring
      _ = (4 / m) * (w a - w b) := by
        rw [intervalIntegral.integral_neg,
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun x hx => hw_deriv x (by simpa [uIcc_of_le hab] using hx)) hw'_int]
        ring
  have hboundary : ‖w b • G b‖ ≤ w b * (4 / m) := by
    have hnorm : ‖w b • G b‖ = w b * ‖G b‖ :=
      norm_smul_of_nonneg (hw_nonneg b ⟨hab, le_rfl⟩) (G b)
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (hG_bound b ⟨hab, le_rfl⟩)
      (hw_nonneg b ⟨hab, le_rfl⟩)
  have hparts' :
      (∫ x in a..b, w x • E x) =
        w b • G b - ∫ x in a..b, w' x • G x := by
    simpa [hG_zero] using hparts
  calc
    ‖∫ x in a..b, x ^ (-p) • Complex.exp (I * F x)‖ =
        ‖∫ x in a..b, w x • E x‖ := by rfl
    _ = ‖w b • G b - ∫ x in a..b, w' x • G x‖ := by rw [hparts']
    _ ≤ ‖w b • G b‖ + ‖∫ x in a..b, w' x • G x‖ := norm_sub_le _ _
    _ ≤ w b * (4 / m) + (4 / m) * (w a - w b) := add_le_add hboundary hrem
    _ = 4 * a ^ (-p) / m := by dsimp [w]; ring

/-- Global-smoothness wrapper for the local weighted first-derivative
oscillatory estimate. -/
theorem norm_integral_rpow_smul_cexp_phase_le_of_monotone_deriv
    {F : ℝ → ℝ} {a b m p : ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hm : 0 < m) (hp : 0 < p)
    (hF : ContDiff ℝ 2 F)
    (hmono : MonotoneOn (deriv F) (Icc a b) ∨
      AntitoneOn (deriv F) (Icc a b))
    (haway : ∀ x ∈ Icc a b, m ≤ |deriv F x|) :
    ‖∫ x in a..b, x ^ (-p) • Complex.exp (I * F x)‖ ≤
      4 * a ^ (-p) / m :=
  norm_integral_rpow_smul_cexp_phase_le_of_monotone_deriv_local
    hab ha hm hp (fun _ _ => hF.contDiffAt) hmono haway

/-- The phase obtained by combining a nonzero Fourier mode with the Mellin
oscillation `x ^ (-I * t)`. -/
noncomputable def fourierMellinPhase (k : ℤ) (t x : ℝ) : ℝ :=
  2 * Real.pi * (k : ℝ) * x - t * Real.log x

private lemma hasDerivAt_fourierMellinPhase
    (k : ℤ) (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fourierMellinPhase k t)
      (2 * Real.pi * (k : ℝ) - t / x) x := by
  unfold fourierMellinPhase
  convert (((hasDerivAt_id x).const_mul (2 * Real.pi * (k : ℝ))).sub
    ((Real.hasDerivAt_log hx).const_mul t)) using 1
  all_goals simp only [inv_eq_one_div]
  all_goals ring

/-- A nonzero Fourier mode gains one inverse power of its frequency after it
is combined with Mellin oscillation.  The range `|t| ≤ a` keeps every mode
uniformly nonstationary on `[a, b]`. -/
theorem norm_integral_rpow_smul_cexp_fourierMellinPhase_le
    {a b t p : ℝ} (hab : a ≤ b) (ha : 0 < a) (hp : 0 < p)
    (ht : |t| ≤ a) (k : ℤ) (hk : k ≠ 0) :
    ‖∫ x in a..b, x ^ (-p) •
        Complex.exp (I * fourierMellinPhase k t x)‖ ≤
      4 * a ^ (-p) / ((2 * Real.pi - 1) * |(k : ℝ)|) := by
  let m : ℝ := (2 * Real.pi - 1) * |(k : ℝ)|
  have hfactor : 0 < 2 * Real.pi - 1 := by
    nlinarith [Real.pi_gt_three]
  have hkcast : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hkabspos : 0 < |(k : ℝ)| := abs_pos.mpr hkcast
  have hkabsone : 1 ≤ |(k : ℝ)| := by
    exact_mod_cast Int.one_le_abs hk
  have hm : 0 < m := mul_pos hfactor hkabspos
  have hF : ∀ x ∈ Icc a b,
      ContDiffAt ℝ 2 (fourierMellinPhase k t) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
    unfold fourierMellinPhase
    exact ((contDiffAt_const.mul contDiffAt_id).sub
      (contDiffAt_const.mul (Real.contDiffAt_log.2 hx0)))
  have hderiv : ∀ x ∈ Icc a b,
      deriv (fourierMellinPhase k t) x =
        2 * Real.pi * (k : ℝ) - t / x := by
    intro x hx
    exact (hasDerivAt_fourierMellinPhase k t
      (ne_of_gt (ha.trans_le hx.1))).deriv
  have hmono :
      MonotoneOn (deriv (fourierMellinPhase k t)) (Icc a b) ∨
        AntitoneOn (deriv (fourierMellinPhase k t)) (Icc a b) := by
    rcases le_total 0 t with ht0 | ht0
    · left
      intro x hx y hy hxy
      rw [hderiv x hx, hderiv y hy]
      have hxpos : 0 < x := ha.trans_le hx.1
      have hypos : 0 < y := hxpos.trans_le hxy
      have hdiv : t / y ≤ t / x := by
        exact (div_le_div_iff₀ hypos hxpos).2
          (mul_le_mul_of_nonneg_left hxy ht0)
      linarith
    · right
      intro x hx y hy hxy
      rw [hderiv x hx, hderiv y hy]
      have hxpos : 0 < x := ha.trans_le hx.1
      have hypos : 0 < y := hxpos.trans_le hxy
      have hdiv : t / x ≤ t / y := by
        exact (div_le_div_iff₀ hxpos hypos).2
          (mul_le_mul_of_nonpos_left hxy ht0)
      linarith
  have haway : ∀ x ∈ Icc a b,
      m ≤ |deriv (fourierMellinPhase k t) x| := by
    intro x hx
    rw [hderiv x hx]
    have hxpos : 0 < x := ha.trans_le hx.1
    have habsx : |x| = x := abs_of_pos hxpos
    have htx : |t| ≤ x := ht.trans hx.1
    have hratio : |t / x| ≤ 1 := by
      rw [abs_div, habsx]
      exact (div_le_one hxpos).2 htx
    have hfreq : |2 * Real.pi * (k : ℝ)| =
        2 * Real.pi * |(k : ℝ)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos Real.pi_pos]
    have htriangle : |2 * Real.pi * (k : ℝ)| ≤
        |2 * Real.pi * (k : ℝ) - t / x| + |t / x| := by
      calc
        |2 * Real.pi * (k : ℝ)| =
            |(2 * Real.pi * (k : ℝ) - t / x) + t / x| := by ring_nf
        _ ≤ |2 * Real.pi * (k : ℝ) - t / x| + |t / x| := abs_add_le _ _
    dsimp only [m]
    rw [hfreq] at htriangle
    nlinarith
  simpa [fourierMellinPhase, m] using
    norm_integral_rpow_smul_cexp_phase_le_of_monotone_deriv_local
      hab ha hm hp hF hmono haway

private theorem deriv_growth_of_second_deriv_lower
    {F : ℝ → ℝ} {a b r : ℝ}
    (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x)
    (hsecond : ∀ x ∈ Icc a b, r ≤ iteratedDeriv 2 F x)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    r * (y - x) ≤ deriv F y - deriv F x := by
  have hsecond' : ∀ z ∈ interior (Icc a b), r ≤ deriv (deriv F) z := by
    intro z hz
    have hz' : z ∈ Icc a b := interior_subset hz
    simpa [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one] using
      hsecond z hz'
  exact Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc a b)
    (by
      intro z hz
      exact ((hF z hz).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt)
    (by
      intro z hz
      exact (((hF z (interior_subset hz)).derivWithin (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).differentiableWithinAt)
    hsecond' x hx y hy hxy

private theorem monotoneOn_deriv_of_second_deriv_lower
    {F : ℝ → ℝ} {a b r : ℝ} (hr : 0 ≤ r)
    (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x)
    (hsecond : ∀ x ∈ Icc a b, r ≤ iteratedDeriv 2 F x) :
    MonotoneOn (deriv F) (Icc a b) := by
  intro x hx y hy hxy
  have hgrowth := deriv_growth_of_second_deriv_lower hF hsecond hx hy hxy
  have : 0 ≤ r * (y - x) := mul_nonneg hr (sub_nonneg.mpr hxy)
  linarith

private theorem norm_integral_cexp_phase_le_length
    {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤ b - a := by
  calc
    ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤
        ∫ x in a..b, ‖Complex.exp (I * F x)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ _x in a..b, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp
    _ = b - a := by simp

private theorem norm_intervalIntegral_le_three_parts
    {f : ℝ → ℂ} {a l u b : ℝ}
    (hal : a ≤ l) (hlu : l ≤ u) (hub : u ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    ‖∫ x in a..b, f x‖ ≤
      ‖∫ x in a..l, f x‖ + ‖∫ x in l..u, f x‖ + ‖∫ x in u..b, f x‖ := by
  have hal_int : IntervalIntegrable f MeasureTheory.volume a l :=
    (hf.mono (Icc_subset_Icc le_rfl (hlu.trans hub))).intervalIntegrable_of_Icc hal
  have hlu_int : IntervalIntegrable f MeasureTheory.volume l u :=
    (hf.mono (Icc_subset_Icc hal hub)).intervalIntegrable_of_Icc hlu
  have hub_int : IntervalIntegrable f MeasureTheory.volume u b :=
    (hf.mono (Icc_subset_Icc (hal.trans hlu) le_rfl)).intervalIntegrable_of_Icc hub
  have hsplit₁ : (∫ x in a..l, f x) + ∫ x in l..u, f x = ∫ x in a..u, f x :=
    intervalIntegral.integral_add_adjacent_intervals hal_int hlu_int
  have hsplit₂ : (∫ x in a..u, f x) + ∫ x in u..b, f x = ∫ x in a..b, f x :=
    intervalIntegral.integral_add_adjacent_intervals (hal_int.trans hlu_int) hub_int
  rw [← hsplit₂, ← hsplit₁]
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

private theorem norm_integral_cexp_phase_le_of_second_deriv_lower
    {F : ℝ → ℝ} {a b r : ℝ}
    (hab : a ≤ b) (hr : 0 < r)
    (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x)
    (hsecond : ∀ x ∈ Icc a b, r ≤ iteratedDeriv 2 F x) :
    ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤ 12 / Real.sqrt r := by
  let s := Real.sqrt r
  let d := 1 / s
  have hs : 0 < s := by simpa [s] using Real.sqrt_pos.2 hr
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have hs_sq : s ^ 2 = r := by
    simpa [s] using Real.sq_sqrt (le_of_lt hr)
  have hrd : r * d = s := by
    dsimp [d]
    rw [← hs_sq]
    field_simp [hs_ne]
  have hd : 0 < d := one_div_pos.mpr hs
  have hmono : MonotoneOn (deriv F) (Icc a b) :=
    monotoneOn_deriv_of_second_deriv_lower (le_of_lt hr) hF hsecond
  have hderiv_cont : ContinuousOn (deriv F) (Icc a b) := by
    intro x hx
    exact ((hF x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hE_cont : ContinuousOn (fun x : ℝ => Complex.exp (I * F x)) (Icc a b) := by
    have hF_cont : ContinuousOn F (Icc a b) := fun x hx => (hF x hx).continuousAt.continuousWithinAt
    exact (continuous_const.continuousOn.mul
      (Complex.continuous_ofReal.continuousOn.comp hF_cont (fun _ _ => mem_univ _))).cexp
  have htotal_bound : d + 4 / s ≤ 12 / s := by
    calc
      d + 4 / s = 5 / s := by dsimp [d]; ring
      _ ≤ 12 / s := (div_le_div_iff_of_pos_right hs).2 (by norm_num)
  have htotal_two_bound : 4 / s + 2 * d + 4 / s ≤ 12 / s := by
    calc
      4 / s + 2 * d + 4 / s = 10 / s := by dsimp [d]; ring
      _ ≤ 12 / s := (div_le_div_iff_of_pos_right hs).2 (by norm_num)
  by_cases ha_nonneg : 0 ≤ deriv F a
  · let u := min b (a + d)
    have hau : a ≤ u := by
      dsimp [u]
      exact le_min hab (by linarith)
    have hub : u ≤ b := by exact min_le_left _ _
    have hmiddle : ‖∫ x in a..u, Complex.exp (I * F x)‖ ≤ d := by
      exact (norm_integral_cexp_phase_le_length hau).trans (by
        dsimp [u]
        have := min_le_right b (a + d)
        linarith)
    have hright : ‖∫ x in u..b, Complex.exp (I * F x)‖ ≤ 4 / s := by
      by_cases hub_eq : u = b
      · rw [hub_eq, intervalIntegral.integral_same, norm_zero]
        positivity
      · have hu_eq : u = a + d := by
          dsimp [u]
          rcases le_total b (a + d) with h | h
          · have : u = b := by dsimp [u]; exact min_eq_left h
            exact False.elim (hub_eq this)
          · exact min_eq_right h
        have hu_mem : u ∈ Icc a b := ⟨hau, hub⟩
        have ha_mem : a ∈ Icc a b := ⟨le_rfl, hab⟩
        have hgrowth := deriv_growth_of_second_deriv_lower hF hsecond ha_mem hu_mem hau
        have hpu : s ≤ deriv F u := by
          rw [hu_eq] at hgrowth ⊢
          nlinarith [hrd]
        apply norm_integral_cexp_phase_le_of_monotone_deriv_local hub hs
          (fun x hx => hF x ⟨hau.trans hx.1, hx.2⟩)
          (Or.inl (hmono.mono (by
            intro x hx
            exact ⟨hau.trans hx.1, hx.2⟩)))
        intro x hx
        have hx' : x ∈ Icc a b := ⟨hau.trans hx.1, hx.2⟩
        have hp : s ≤ deriv F x := hpu.trans (hmono hu_mem hx' hx.1)
        exact le_abs.mpr (Or.inl hp)
    calc
      ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤
          ‖∫ x in a..a, Complex.exp (I * F x)‖ +
            ‖∫ x in a..u, Complex.exp (I * F x)‖ +
              ‖∫ x in u..b, Complex.exp (I * F x)‖ :=
        norm_intervalIntegral_le_three_parts le_rfl hau hub hE_cont
      _ ≤ 0 + d + 4 / s := add_le_add (add_le_add (by simp) hmiddle) hright
      _ = d + 4 / s := by ring
      _ ≤ 12 / s := htotal_bound
  · have ha_neg : deriv F a < 0 := lt_of_not_ge ha_nonneg
    by_cases hb_nonpos : deriv F b ≤ 0
    · let l := max a (b - d)
      have hal : a ≤ l := by exact le_max_left _ _
      have hlb : l ≤ b := by
        dsimp [l]
        exact max_le hab (by linarith)
      have hmiddle : ‖∫ x in l..b, Complex.exp (I * F x)‖ ≤ d := by
        exact (norm_integral_cexp_phase_le_length hlb).trans (by
          dsimp [l]
          have := le_max_right a (b - d)
          linarith)
      have hleft : ‖∫ x in a..l, Complex.exp (I * F x)‖ ≤ 4 / s := by
        by_cases hal_eq : l = a
        · rw [hal_eq, intervalIntegral.integral_same, norm_zero]
          positivity
        · have hl_eq : l = b - d := by
            dsimp [l]
            rcases le_total (b - d) a with h | h
            · have : l = a := by dsimp [l]; exact max_eq_left h
              exact False.elim (hal_eq this)
            · exact max_eq_right h
          have hl_mem : l ∈ Icc a b := ⟨hal, hlb⟩
          have hb_mem : b ∈ Icc a b := ⟨hab, le_rfl⟩
          have hgrowth := deriv_growth_of_second_deriv_lower hF hsecond hl_mem hb_mem hlb
          have hpl : deriv F l ≤ -s := by
            rw [hl_eq] at hgrowth ⊢
            nlinarith [hrd]
          apply norm_integral_cexp_phase_le_of_monotone_deriv_local hal hs
            (fun x hx => hF x ⟨hx.1, hx.2.trans hlb⟩)
            (Or.inl (hmono.mono (by
              intro x hx
              exact ⟨hx.1, hx.2.trans hlb⟩)))
          intro x hx
          have hx' : x ∈ Icc a b := ⟨hx.1, hx.2.trans hlb⟩
          have hp : deriv F x ≤ -s := (hmono hx' hl_mem hx.2).trans hpl
          exact le_abs.mpr (Or.inr (by linarith))
      calc
        ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤
            ‖∫ x in a..l, Complex.exp (I * F x)‖ +
              ‖∫ x in l..b, Complex.exp (I * F x)‖ +
                ‖∫ x in b..b, Complex.exp (I * F x)‖ :=
          norm_intervalIntegral_le_three_parts hal hlb le_rfl hE_cont
        _ ≤ 4 / s + d + 0 := add_le_add (add_le_add hleft hmiddle) (by simp)
        _ = d + 4 / s := by ring
        _ ≤ 12 / s := htotal_bound
    · have hb_pos : 0 < deriv F b := lt_of_not_ge hb_nonpos
      have hzero_mem : 0 ∈ Icc (deriv F a) (deriv F b) :=
        ⟨le_of_lt ha_neg, le_of_lt hb_pos⟩
      obtain ⟨c, hc, hc_zero⟩ :=
        (intermediate_value_Icc hab hderiv_cont) hzero_mem
      let l := max a (c - d)
      let u := min b (c + d)
      have hal : a ≤ l := le_max_left _ _
      have hlc : l ≤ c := by
        dsimp [l]
        exact max_le hc.1 (by linarith)
      have hcu : c ≤ u := by
        dsimp [u]
        exact le_min hc.2 (by linarith)
      have hub : u ≤ b := min_le_left _ _
      have hmiddle : ‖∫ x in l..u, Complex.exp (I * F x)‖ ≤ 2 * d := by
        exact (norm_integral_cexp_phase_le_length (hlc.trans hcu)).trans (by
          dsimp [l, u]
          have hlower := le_max_right a (c - d)
          have hupper := min_le_right b (c + d)
          linarith)
      have hleft : ‖∫ x in a..l, Complex.exp (I * F x)‖ ≤ 4 / s := by
        by_cases hal_eq : l = a
        · rw [hal_eq, intervalIntegral.integral_same, norm_zero]
          positivity
        · have hl_eq : l = c - d := by
            dsimp [l]
            rcases le_total (c - d) a with h | h
            · have : l = a := by dsimp [l]; exact max_eq_left h
              exact False.elim (hal_eq this)
            · exact max_eq_right h
          have hl_mem : l ∈ Icc a b := ⟨hal, hlc.trans hc.2⟩
          have hgrowth := deriv_growth_of_second_deriv_lower hF hsecond hl_mem hc hlc
          have hpl : deriv F l ≤ -s := by
            rw [hl_eq] at hgrowth ⊢
            rw [hc_zero] at hgrowth
            nlinarith [hrd]
          apply norm_integral_cexp_phase_le_of_monotone_deriv_local hal hs
            (fun x hx => hF x ⟨hx.1, hx.2.trans (hlc.trans hc.2)⟩)
            (Or.inl (hmono.mono (by
              intro x hx
              exact ⟨hx.1, hx.2.trans (hlc.trans hc.2)⟩)))
          intro x hx
          have hx' : x ∈ Icc a b := ⟨hx.1, hx.2.trans (hlc.trans hc.2)⟩
          have hp : deriv F x ≤ -s := (hmono hx' hl_mem hx.2).trans hpl
          exact le_abs.mpr (Or.inr (by linarith))
      have hright : ‖∫ x in u..b, Complex.exp (I * F x)‖ ≤ 4 / s := by
        by_cases hub_eq : u = b
        · rw [hub_eq, intervalIntegral.integral_same, norm_zero]
          positivity
        · have hu_eq : u = c + d := by
            dsimp [u]
            rcases le_total b (c + d) with h | h
            · have : u = b := by dsimp [u]; exact min_eq_left h
              exact False.elim (hub_eq this)
            · exact min_eq_right h
          have hu_mem : u ∈ Icc a b := ⟨hc.1.trans hcu, hub⟩
          have hgrowth := deriv_growth_of_second_deriv_lower hF hsecond hc hu_mem hcu
          have hpu : s ≤ deriv F u := by
            rw [hu_eq] at hgrowth ⊢
            rw [hc_zero] at hgrowth
            nlinarith [hrd]
          apply norm_integral_cexp_phase_le_of_monotone_deriv_local hub hs
            (fun x hx => hF x ⟨(hc.1.trans hcu).trans hx.1, hx.2⟩)
            (Or.inl (hmono.mono (by
              intro x hx
              exact ⟨(hc.1.trans hcu).trans hx.1, hx.2⟩)))
          intro x hx
          have hx' : x ∈ Icc a b := ⟨(hc.1.trans hcu).trans hx.1, hx.2⟩
          have hp : s ≤ deriv F x := hpu.trans (hmono hu_mem hx' hx.1)
          exact le_abs.mpr (Or.inl hp)
      calc
        ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤
            ‖∫ x in a..l, Complex.exp (I * F x)‖ +
              ‖∫ x in l..u, Complex.exp (I * F x)‖ +
                ‖∫ x in u..b, Complex.exp (I * F x)‖ :=
          norm_intervalIntegral_le_three_parts hal (hlc.trans hcu) hub hE_cont
        _ ≤ 4 / s + 2 * d + 4 / s := add_le_add (add_le_add hleft hmiddle) hright
        _ ≤ 12 / s := htotal_two_bound

private theorem norm_integral_cexp_phase_le_of_second_deriv_local
    {F : ℝ → ℝ} {a b r : ℝ}
    (hab : a ≤ b) (hr : 0 < r)
    (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x)
    (hsecond : (∀ x ∈ Icc a b, r ≤ iteratedDeriv 2 F x) ∨
      (∀ x ∈ Icc a b, iteratedDeriv 2 F x ≤ -r)) :
    ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤ 12 / Real.sqrt r := by
  rcases hsecond with hpositive | hnegative
  · exact norm_integral_cexp_phase_le_of_second_deriv_lower hab hr hF hpositive
  · let G : ℝ → ℝ := fun x => -F x
    have hG : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 G x := by
      intro x hx
      exact (hF x hx).neg
    have hGsecond : ∀ x ∈ Icc a b, r ≤ iteratedDeriv 2 G x := by
      intro x hx
      rw [show G = fun y => -F y by rfl, iteratedDeriv_fun_neg]
      linarith [hnegative x hx]
    have hbound :=
      norm_integral_cexp_phase_le_of_second_deriv_lower hab hr hG hGsecond
    have hE_cont : ContinuousOn (fun x : ℝ => Complex.exp (I * F x)) (Icc a b) := by
      have hF_cont : ContinuousOn F (Icc a b) :=
        fun x hx => (hF x hx).continuousAt.continuousWithinAt
      exact (continuous_const.continuousOn.mul
        (Complex.continuous_ofReal.continuousOn.comp hF_cont (fun _ _ => mem_univ _))).cexp
    have hE_int : IntervalIntegrable (fun x : ℝ => Complex.exp (I * F x))
        MeasureTheory.volume a b := hE_cont.intervalIntegrable_of_Icc hab
    have hconj_integral :
        (∫ x in a..b, Complex.exp (I * G x)) =
          star (∫ x in a..b, Complex.exp (I * F x)) := by
      calc
        (∫ x in a..b, Complex.exp (I * G x)) =
            ∫ x in a..b, star (Complex.exp (I * F x)) := by
          apply intervalIntegral.integral_congr
          intro x _
          change Complex.exp (I * (-(F x) : ℝ)) =
            (starRingEnd ℂ) (Complex.exp (I * F x))
          rw [← Complex.exp_conj]
          congr 1
          simp
        _ = star (∫ x in a..b, Complex.exp (I * F x)) := by
          exact Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hE_int
    rw [hconj_integral, norm_star] at hbound
    exact hbound

/-- A second-derivative oscillatory integral estimate with an explicit absolute constant.
The second derivative may have either sign, but its sign is fixed on the interval. -/
theorem norm_integral_cexp_phase_le_of_second_deriv
    {F : ℝ → ℝ} {a b r : ℝ}
    (hab : a ≤ b) (hr : 0 < r)
    (hF : ContDiff ℝ 2 F)
    (hsecond : (∀ x ∈ Icc a b, r ≤ iteratedDeriv 2 F x) ∨
      (∀ x ∈ Icc a b, iteratedDeriv 2 F x ≤ -r)) :
    ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤ 12 / Real.sqrt r :=
  norm_integral_cexp_phase_le_of_second_deriv_local hab hr
    (fun _ _ => hF.contDiffAt) hsecond

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

theorem contDiffAt_hardyPhase_two
    {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ 2 (hardyPhase n) t := by
  have hn_real : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hc : 2 * Real.pi * ((n : ℝ) ^ 2) ≠ 0 := by
    positivity
  have harg_ne : t / (2 * Real.pi * ((n : ℝ) ^ 2)) ≠ 0 :=
    div_ne_zero (ne_of_gt ht) hc
  have harg : ContDiffAt ℝ 2
      (fun x : ℝ => x / (2 * Real.pi * ((n : ℝ) ^ 2))) t :=
    contDiffAt_id.div_const _
  have hlinear : ContDiffAt ℝ 2 (fun x : ℝ => x / 2) t :=
    contDiffAt_id.div_const 2
  simpa [hardyPhase] using
    (hlinear.mul ((harg.log harg_ne).sub contDiffAt_const)).sub contDiffAt_const

/-- The Hardy first-approximation phase satisfies a uniform second-derivative estimate
on every dyadic interval `[T, 2T]` with `T ≥ 1`. -/
theorem norm_integral_cexp_hardyPhase_le
    {n : ℕ} (hn : n ≠ 0) {T : ℝ} (hT : 1 ≤ T) :
    ‖∫ t in T..(2 * T), Complex.exp (I * hardyPhase n t)‖ ≤
      12 * Real.sqrt (4 * T) := by
  have hT_pos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hab : T ≤ 2 * T := by linarith
  have hr : 0 < 1 / (4 * T) := one_div_pos.mpr (by positivity)
  have hlocal : ∀ x ∈ Icc T (2 * T), ContDiffAt ℝ 2 (hardyPhase n) x := by
    intro x hx
    exact contDiffAt_hardyPhase_two hn (lt_of_lt_of_le hT_pos hx.1)
  have hsecond : ∀ x ∈ Icc T (2 * T),
      1 / (4 * T) ≤ iteratedDeriv 2 (hardyPhase n) x := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le hT_pos hx.1
    rw [iteratedDeriv_two_hardyPhase hn hx_pos]
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * T) (by positivity : 0 < 2 * x)).2
    nlinarith [hx.2]
  have hbound := norm_integral_cexp_phase_le_of_second_deriv_local hab hr hlocal
    (Or.inl hsecond)
  calc
    ‖∫ t in T..(2 * T), Complex.exp (I * hardyPhase n t)‖ ≤
        12 / Real.sqrt (1 / (4 * T)) := hbound
    _ = 12 * Real.sqrt (4 * T) := by
      rw [one_div, Real.sqrt_inv]
      simp [div_eq_mul_inv]

end HardyTheorem.OscillatoryIntegral
