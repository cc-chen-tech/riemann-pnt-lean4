import HardyTheorem.OscillatoryGammaTail

open Real Complex Set MeasureTheory Filter Topology

namespace HardyTheorem.OscillatoryDampedGammaTail

/-!
# A damping-uniform oscillatory Gamma tail

The Gamma-ray boundary passage needs a first-derivative estimate which is
uniform as a positive exponential damping parameter tends to zero.  We first
record the elementary bounded-primitive argument for a general positive
decreasing `C¹` weight, then specialize it to `u⁻ᵖ exp (-r u)`.
-/

private theorem norm_intervalIntegral_weight_smul_cexp_phase_le
    {F w w' : ℝ → ℝ} {a b m : ℝ}
    (hab : a ≤ b) (hm : 0 < m)
    (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x)
    (hmono : MonotoneOn (deriv F) (Icc a b) ∨
      AntitoneOn (deriv F) (Icc a b))
    (haway : ∀ x ∈ Icc a b, m ≤ |deriv F x|)
    (hw_deriv : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x)
    (hw'_cont : ContinuousOn w' (Icc a b))
    (hw_nonneg : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hw'_nonpos : ∀ x ∈ Icc a b, w' x ≤ 0) :
    ‖∫ x in a..b, w x • Complex.exp (I * F x)‖ ≤
      4 * w a / m := by
  let E : ℝ → ℂ := fun x => Complex.exp (I * F x)
  let G : ℝ → ℂ := fun u => ∫ x in a..u, E x
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
      have huy : u ∈ nhds y := mem_of_superset (hv_open.mem_nhds hy) hvu
      have hFy : ContinuousAt F y :=
        (huF y (hvu hy)).continuousWithinAt.continuousAt huy
      exact (continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp hFy)).cexp
    have hE_meas : StronglyMeasurableAtFilter E (nhds x) volume :=
      hE_cont_v.stronglyMeasurableAtFilter hv_open x hxv
    exact intervalIntegral.integral_hasDerivAt_right
      hE_int_ax hE_meas hE_at
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
    apply OscillatoryIntegral.norm_integral_cexp_phase_le_of_monotone_deriv_local
      hx.1 hm (fun y hy => hF y ⟨hy.1, hy.2.trans hx.2⟩)
    · rcases hmono with hmono | hanti
      · exact Or.inl (hmono.mono (Icc_subset_Icc le_rfl hx.2))
      · exact Or.inr (hanti.mono (Icc_subset_Icc le_rfl hx.2))
    · intro y hy
      exact haway y ⟨hy.1, hy.2.trans hx.2⟩
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
        exact mul_le_mul_of_nonneg_left (hG_bound x hx')
          (neg_nonneg.mpr (hw'_nonpos x hx'))
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
    ‖∫ x in a..b, w x • Complex.exp (I * F x)‖ =
        ‖∫ x in a..b, w x • E x‖ := by rfl
    _ = ‖w b • G b - ∫ x in a..b, w' x • G x‖ := by rw [hparts']
    _ ≤ ‖w b • G b‖ + ‖∫ x in a..b, w' x • G x‖ := norm_sub_le _ _
    _ ≤ w b * (4 / m) + (4 / m) * (w a - w b) :=
      add_le_add hboundary hrem
    _ = 4 * w a / m := by ring

private noncomputable def dampedGammaPhase (z : ℂ) (c u : ℝ) : ℝ :=
  -c * u + z.im * Real.log u

private noncomputable def dampedGammaWeight (z : ℂ) (r u : ℝ) : ℝ :=
  Real.exp (-(1 - z.re) * Real.log u - r * u)

private noncomputable def dampedGammaWeightDeriv (z : ℂ) (r u : ℝ) : ℝ :=
  (-(1 - z.re) / u - r) * dampedGammaWeight z r u

private lemma dampedGamma_integrand_eq
    (z : ℂ) (r c : ℝ) {u : ℝ} (hu : 0 < u) :
    (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
        Complex.exp (-I * (c * u)) =
      dampedGammaWeight z r u •
        Complex.exp (I * dampedGammaPhase z c u) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne')]
  rw [Complex.real_smul, dampedGammaWeight]
  push_cast
  simp only [dampedGammaPhase]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_log hu.le]
  apply Complex.ext
  · simp
    ring
  · simp
    ring

/-- Exponential damping does not worsen the non-stationary Gamma tail. -/
theorem norm_intervalIntegral_cpow_mul_exp_neg_mul_cexp_neg_linear_le
    {z : ℂ} {r c A B : ℝ}
    (hAB : A ≤ B) (hA : 0 < A) (hz1 : z.re < 1)
    (hr : 0 ≤ r) (hc : 0 < c) (him : 2 * |z.im| ≤ c * A) :
    ‖∫ u in A..B,
        (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
          Complex.exp (-I * (c * u))‖ ≤
      8 * A ^ (z.re - 1) / c := by
  let p : ℝ := 1 - z.re
  let m : ℝ := c / 2
  let F : ℝ → ℝ := dampedGammaPhase z c
  let w : ℝ → ℝ := dampedGammaWeight z r
  let w' : ℝ → ℝ := dampedGammaWeightDeriv z r
  have hp : 0 < p := by dsimp [p]; linarith
  have hm : 0 < m := by dsimp [m]; positivity
  have hF : ∀ u ∈ Icc A B, ContDiffAt ℝ 2 F u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (hA.trans_le hu.1)
    dsimp only [F, dampedGammaPhase]
    exact (contDiffAt_const.mul contDiffAt_id).add
      (contDiffAt_const.mul (Real.contDiffAt_log.2 hu0))
  have hphaseDeriv : ∀ u ∈ Icc A B, deriv F u = -c + z.im / u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (hA.trans_le hu.1)
    change deriv (fun v : ℝ => -c * v + z.im * Real.log v) u =
      -c + z.im / u
    simpa [div_eq_mul_inv, Pi.add_def, Pi.mul_def] using
      (((hasDerivAt_id u).const_mul (-c)).add
        ((Real.hasDerivAt_log hu0).const_mul z.im)).deriv
  have hmono : MonotoneOn (deriv F) (Icc A B) ∨
      AntitoneOn (deriv F) (Icc A B) := by
    rcases le_total 0 z.im with him0 | him0
    · right
      intro u hu v hv huv
      rw [hphaseDeriv u hu, hphaseDeriv v hv]
      have hupos : 0 < u := hA.trans_le hu.1
      have hvpos : 0 < v := hupos.trans_le huv
      have hdiv : z.im / v ≤ z.im / u :=
        (div_le_div_iff₀ hvpos hupos).2
          (mul_le_mul_of_nonneg_left huv him0)
      linarith
    · left
      intro u hu v hv huv
      rw [hphaseDeriv u hu, hphaseDeriv v hv]
      have hupos : 0 < u := hA.trans_le hu.1
      have hvpos : 0 < v := hupos.trans_le huv
      have hdiv : z.im / u ≤ z.im / v :=
        (div_le_div_iff₀ hupos hvpos).2
          (mul_le_mul_of_nonpos_left huv him0)
      linarith
  have haway : ∀ u ∈ Icc A B, m ≤ |deriv F u| := by
    intro u hu
    rw [hphaseDeriv u hu]
    have hupos : 0 < u := hA.trans_le hu.1
    have himA : |z.im| ≤ c * A / 2 := by linarith
    have hratio : |z.im / u| ≤ c / 2 := by
      rw [abs_div, abs_of_pos hupos, div_le_iff₀ hupos]
      have hcu : c * A ≤ c * u := mul_le_mul_of_nonneg_left hu.1 hc.le
      nlinarith
    have htriangle : c ≤ |-c + z.im / u| + |z.im / u| := by
      calc
        c = |-c| := by rw [abs_neg, abs_of_pos hc]
        _ = |(-c + z.im / u) + (-(z.im / u))| := by ring_nf
        _ ≤ |-c + z.im / u| + |-(z.im / u)| := abs_add_le _ _
        _ = |-c + z.im / u| + |z.im / u| := by rw [abs_neg]
    dsimp only [m]
    linarith
  have hw_deriv : ∀ u ∈ Icc A B, HasDerivAt w (w' u) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (hA.trans_le hu.1)
    change HasDerivAt
      (fun v : ℝ => Real.exp (-(1 - z.re) * Real.log v - r * v))
      ((-(1 - z.re) / u - r) *
        Real.exp (-(1 - z.re) * Real.log u - r * u)) u
    have hinner :=
      ((Real.hasDerivAt_log hu0).const_mul (-(1 - z.re))).sub
        ((hasDerivAt_id u).const_mul r)
    simpa [div_eq_mul_inv, Pi.sub_def, Pi.mul_def, mul_comm] using hinner.exp
  have hw'_cont : ContinuousOn w' (Icc A B) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (hA.trans_le hu.1)
    dsimp only [w', dampedGammaWeightDeriv]
    have hweight : ContinuousAt (dampedGammaWeight z r) u := by
      unfold dampedGammaWeight
      fun_prop
    exact (((continuousAt_const.div continuousAt_id hu0).sub continuousAt_const).mul
      hweight).continuousWithinAt
  have hw_nonneg : ∀ u ∈ Icc A B, 0 ≤ w u := by
    intro u hu
    dsimp only [w, dampedGammaWeight]
    exact (Real.exp_pos _).le
  have hw'_nonpos : ∀ u ∈ Icc A B, w' u ≤ 0 := by
    intro u hu
    have hupos : 0 < u := hA.trans_le hu.1
    dsimp only [w', dampedGammaWeightDeriv, dampedGammaWeight]
    have hcoeff : -(1 - z.re) / u - r ≤ 0 := by
      have : -(1 - z.re) / u ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hupos.le
      linarith
    exact mul_nonpos_of_nonpos_of_nonneg hcoeff (Real.exp_pos _).le
  have hraw := norm_intervalIntegral_weight_smul_cexp_phase_le
    hAB hm hF hmono haway hw_deriv hw'_cont hw_nonneg hw'_nonpos
  have heq :
      (∫ u in A..B,
        (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
          Complex.exp (-I * (c * u))) =
      ∫ u in A..B, w u • Complex.exp (I * F u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have huIcc : u ∈ Icc A B := by simpa [uIcc_of_le hAB] using hu
    simpa [w, F] using dampedGamma_integrand_eq z r c (hA.trans_le huIcc.1)
  rw [heq]
  have hwA : w A ≤ A ^ (z.re - 1) := by
    have hwAeq : w A = A ^ (z.re - 1) * Real.exp (-r * A) := by
      dsimp only [w, dampedGammaWeight]
      rw [Real.rpow_def_of_pos hA]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hwAeq]
    have hexp_le : Real.exp (-r * A) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [mul_nonneg hr hA.le]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hA.le _) hexp_le
  calc
    ‖∫ u in A..B, w u • Complex.exp (I * F u)‖ ≤ 4 * w A / m := hraw
    _ ≤ 4 * A ^ (z.re - 1) / m := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwA (by norm_num)) hm.le
    _ = 8 * A ^ (z.re - 1) / c := by
      dsimp [m]
      field_simp [hc.ne']
      norm_num

end HardyTheorem.OscillatoryDampedGammaTail
