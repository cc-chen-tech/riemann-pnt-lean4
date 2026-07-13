import ZeroFreeRegion.MeromorphicAux
import Mathlib.Analysis.Meromorphic.Divisor

open Complex Filter Set Topology
open scoped Topology

namespace ZeroFreeRegion

noncomputable def normalizedRiemannZetaCarrier (s : ℂ) : ℂ :=
  riemannZetaEntireRegularization s / (s + 2) ^ 4

lemma diffContOnCl_normalizedRiemannZetaCarrier :
    DiffContOnCl ℂ normalizedRiemannZetaCarrier
      (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := by
  apply DifferentiableOn.diffContOnCl
  intro s hs
  have hclosure : closure (Complex.re ⁻¹' Ioo (0 : ℝ) 1) ⊆
      Complex.re ⁻¹' Icc (0 : ℝ) 1 :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self)
      (isClosed_Icc.preimage continuous_re)
  have hscc := hclosure hs
  have hs2 : s + 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hscc.1]
  unfold normalizedRiemannZetaCarrier
  exact (differentiable_riemannZetaEntireRegularization.differentiableAt.div
    ((differentiableAt_id.add_const 2).pow 4) (pow_ne_zero 4 hs2)).differentiableWithinAt

lemma normalizedRiemannZetaCarrier_isBigO_riemannZetaEntireRegularization :
    normalizedRiemannZetaCarrier
      =O[comap (_root_.abs ∘ Complex.im) atTop ⊓
          𝓟 (Complex.re ⁻¹' Ioo (0 : ℝ) 1)]
        riemannZetaEntireRegularization := by
  apply Asymptotics.IsBigO.of_bound 1
  rw [eventually_inf_principal]
  filter_upwards [] with s hs
  have hs2 : 1 ≤ ‖s + 2‖ := by
    have hre : 2 ≤ |(s + 2).re| := by
      simp
      rw [abs_of_nonneg (by linarith [hs.1])]
      linarith [hs.1]
    exact one_le_two.trans (hre.trans (Complex.abs_re_le_norm (s + 2)))
  have hpow : 1 ≤ ‖(s + 2) ^ 4‖ := by
    rw [norm_pow]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hs2 4]
  simp only [normalizedRiemannZetaCarrier, norm_div, one_mul]
  exact div_le_self (norm_nonneg _) hpow

theorem normalizedRiemannZetaCarrier_isBigO_exp_exp_on_zero_one :
    ∃ c < Real.pi, ∃ B : ℝ,
      normalizedRiemannZetaCarrier
        =O[comap (_root_.abs ∘ Complex.im) atTop ⊓
            𝓟 (Complex.re ⁻¹' Ioo (0 : ℝ) 1)]
          fun z : ℂ => Real.exp (B * Real.exp (c * |z.im|)) := by
  rcases riemannZetaEntireRegularization_isBigO_exp_exp_on_zero_one with
    ⟨c, hc, B, hQ⟩
  exact ⟨c, hc, B,
    normalizedRiemannZetaCarrier_isBigO_riemannZetaEntireRegularization.trans hQ⟩

lemma norm_normalizedRiemannZetaCarrier_le_sixteen_of_re_zero
    (s : ℂ) (hsre : s.re = 0) (hsim : 1 ≤ |s.im|) :
    ‖normalizedRiemannZetaCarrier s‖ ≤ 16 := by
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hsim
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hsre
  have hs_eq : s = Complex.I * s.im := by
    apply Complex.ext <;> simp [hsre]
  have hzeta : ‖riemannZeta s‖ ≤ 4 * |s.im| ^ 2 := by
    calc
      ‖riemannZeta s‖ = ‖riemannZeta (Complex.I * s.im)‖ :=
        congrArg (fun z : ℂ => ‖riemannZeta z‖) hs_eq
      _ ≤ 4 * |s.im| ^ 2 :=
        norm_riemannZeta_I_mul_le_four_mul_abs_sq s.im hsim
  have hs_norm : ‖s‖ ≤ 2 * |s.im| := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = |s.im| := by simp [hsre]
      _ ≤ 2 * |s.im| := by nlinarith [abs_nonneg s.im]
  have hs_sub_norm : ‖s - 1‖ ≤ 2 * |s.im| := by
    calc
      ‖s - 1‖ ≤ |(s - 1).re| + |(s - 1).im| :=
        Complex.norm_le_abs_re_add_abs_im (s - 1)
      _ = 1 + |s.im| := by simp [hsre]
      _ ≤ 2 * |s.im| := by linarith
  have hden : |s.im| ^ 4 ≤ ‖(s + 2) ^ 4‖ := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by
      simpa using Complex.abs_im_le_norm (s + 2)) 4
  have hden_pos : 0 < ‖(s + 2) ^ 4‖ := by
    have ht : 0 < |s.im| := lt_of_lt_of_le zero_lt_one hsim
    exact (pow_pos ht 4).trans_le hden
  rw [normalizedRiemannZetaCarrier,
    riemannZetaEntireRegularization_eq_mul_riemannZeta hs0 hs1, norm_div,
    norm_mul, norm_mul]
  apply (div_le_iff₀ hden_pos).2
  have hnum : ‖s‖ * ‖s - 1‖ * ‖riemannZeta s‖ ≤ 16 * |s.im| ^ 4 := by
    calc
      ‖s‖ * ‖s - 1‖ * ‖riemannZeta s‖ ≤
          (2 * |s.im|) * (2 * |s.im|) * (4 * |s.im| ^ 2) := by gcongr
      _ = 16 * |s.im| ^ 4 := by ring
  exact hnum.trans (mul_le_mul_of_nonneg_left hden (by norm_num))

lemma norm_normalizedRiemannZetaCarrier_le_sixteen_of_re_one
    (s : ℂ) (hsre : s.re = 1) (hsim : 1 ≤ |s.im|) :
    ‖normalizedRiemannZetaCarrier s‖ ≤ 16 := by
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hsre
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hsim
  have hs_norm : ‖s‖ ≤ 2 * |s.im| := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = 1 + |s.im| := by simp [hsre]
      _ ≤ 2 * |s.im| := by linarith
  have hs_sub_norm : ‖s - 1‖ ≤ 2 * |s.im| := by
    calc
      ‖s - 1‖ ≤ |(s - 1).re| + |(s - 1).im| :=
        Complex.norm_le_abs_re_add_abs_im (s - 1)
      _ = |s.im| := by simp [hsre]
      _ ≤ 2 * |s.im| := by nlinarith [abs_nonneg s.im]
  have hzeta :=
    norm_riemannZeta_le_two_mul_norm_of_one_le_re_of_one_le_abs_im
      s (by rw [hsre]) hsim
  have hzeta' : ‖riemannZeta s‖ ≤ 4 * |s.im| ^ 2 := by
    have ht : |s.im| ≤ |s.im| ^ 2 := by nlinarith [sq_nonneg (|s.im| - 1)]
    nlinarith
  have hden : |s.im| ^ 4 ≤ ‖(s + 2) ^ 4‖ := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by
      simpa using Complex.abs_im_le_norm (s + 2)) 4
  have hden_pos : 0 < ‖(s + 2) ^ 4‖ := by
    have ht : 0 < |s.im| := lt_of_lt_of_le zero_lt_one hsim
    exact (pow_pos ht 4).trans_le hden
  rw [normalizedRiemannZetaCarrier,
    riemannZetaEntireRegularization_eq_mul_riemannZeta hs0 hs1, norm_div,
    norm_mul, norm_mul]
  apply (div_le_iff₀ hden_pos).2
  have hnum : ‖s‖ * ‖s - 1‖ * ‖riemannZeta s‖ ≤ 16 * |s.im| ^ 4 := by
    calc
      ‖s‖ * ‖s - 1‖ * ‖riemannZeta s‖ ≤
          (2 * |s.im|) * (2 * |s.im|) * (4 * |s.im| ^ 2) := by gcongr
      _ = 16 * |s.im| ^ 4 := by ring
  exact hnum.trans (mul_le_mul_of_nonneg_left hden (by norm_num))

lemma exists_norm_normalizedRiemannZetaCarrier_boundary_le :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ s : ℂ, s.re = 0 → ‖normalizedRiemannZetaCarrier s‖ ≤ C) ∧
      (∀ s : ℂ, s.re = 1 → ‖normalizedRiemannZetaCarrier s‖ ≤ C) := by
  have hcont0 : Continuous (fun t : ℝ =>
      ‖normalizedRiemannZetaCarrier (Complex.I * t)‖) := by
    apply Continuous.norm
    unfold normalizedRiemannZetaCarrier
    apply Continuous.div
    · exact differentiable_riemannZetaEntireRegularization.continuous.comp (by fun_prop)
    · fun_prop
    · intro t
      apply pow_ne_zero
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
  have hcont1 : Continuous (fun t : ℝ =>
      ‖normalizedRiemannZetaCarrier (1 + Complex.I * t)‖) := by
    apply Continuous.norm
    unfold normalizedRiemannZetaCarrier
    apply Continuous.div
    · exact differentiable_riemannZetaEntireRegularization.continuous.comp (by fun_prop)
    · fun_prop
    · intro t
      apply pow_ne_zero
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
  rcases isCompact_Icc.bddAbove_image hcont0.continuousOn with ⟨M0, hM0⟩
  rcases isCompact_Icc.bddAbove_image hcont1.continuousOn with ⟨M1, hM1⟩
  refine ⟨max 16 (max M0 M1), le_trans (by norm_num) (le_max_left _ _), ?_, ?_⟩
  · intro s hsre
    by_cases ht : 1 ≤ |s.im|
    · exact (norm_normalizedRiemannZetaCarrier_le_sixteen_of_re_zero s hsre ht).trans
        (le_max_left _ _)
    · have ht' : s.im ∈ Icc (-1 : ℝ) 1 := by
        exact abs_le.mp (le_of_not_ge ht)
      have hs_eq : s = Complex.I * s.im := by
        apply Complex.ext <;> simp [hsre]
      have hm : ‖normalizedRiemannZetaCarrier (Complex.I * s.im)‖ ≤ M0 :=
        hM0 (mem_image_of_mem _ ht')
      rw [hs_eq]
      exact hm.trans ((le_max_left M0 M1).trans (le_max_right 16 (max M0 M1)))
  · intro s hsre
    by_cases ht : 1 ≤ |s.im|
    · exact (norm_normalizedRiemannZetaCarrier_le_sixteen_of_re_one s hsre ht).trans
        (le_max_left _ _)
    · have ht' : s.im ∈ Icc (-1 : ℝ) 1 := by
        exact abs_le.mp (le_of_not_ge ht)
      have hs_eq : s = 1 + Complex.I * s.im := by
        apply Complex.ext <;> simp [hsre]
      have hm : ‖normalizedRiemannZetaCarrier (1 + Complex.I * s.im)‖ ≤ M1 :=
        hM1 (mem_image_of_mem _ ht')
      rw [hs_eq]
      exact hm.trans ((le_max_right M0 M1).trans (le_max_right 16 (max M0 M1)))

theorem exists_norm_normalizedRiemannZetaCarrier_le_on_zero_one :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc (0 : ℝ) 1 →
      ‖normalizedRiemannZetaCarrier s‖ ≤ C := by
  rcases exists_norm_normalizedRiemannZetaCarrier_boundary_le with
    ⟨C, hC, hC0, hC1⟩
  refine ⟨C, hC, ?_⟩
  intro s hs
  apply PhragmenLindelof.vertical_strip
    diffContOnCl_normalizedRiemannZetaCarrier
    (show ∃ c < Real.pi / ((1 : ℝ) - 0), ∃ B : ℝ,
      normalizedRiemannZetaCarrier
        =O[comap (_root_.abs ∘ Complex.im) atTop ⊓
            𝓟 (Complex.re ⁻¹' Ioo (0 : ℝ) 1)]
          fun z : ℂ => Real.exp (B * Real.exp (c * |z.im|)) by
      simpa using normalizedRiemannZetaCarrier_isBigO_exp_exp_on_zero_one)
    hC0 hC1 hs.1 hs.2

theorem exists_norm_riemannZeta_le_polynomial_on_zero_one :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      s.re ∈ Icc (0 : ℝ) 1 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ 4 := by
  rcases exists_norm_normalizedRiemannZetaCarrier_le_on_zero_one with
    ⟨C, hC, hnormalized⟩
  refine ⟨C, hC, ?_⟩
  intro s hsre hsim
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hsim
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hsim
  have hs2 : s + 2 ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp at hre
    linarith [hsre.1]
  have hnorm := hnormalized s hsre
  rw [normalizedRiemannZetaCarrier,
    riemannZetaEntireRegularization_eq_mul_riemannZeta hs0 hs1, norm_div,
    norm_mul, norm_mul] at hnorm
  have hden_pos : 0 < ‖(s + 2) ^ 4‖ := norm_pos_iff.mpr (pow_ne_zero 4 hs2)
  have hQ : ‖s‖ * ‖s - 1‖ * ‖riemannZeta s‖ ≤ C * ‖(s + 2) ^ 4‖ :=
    (div_le_iff₀ hden_pos).mp hnorm
  have hs_norm : 1 ≤ ‖s‖ := hsim.trans (Complex.abs_im_le_norm s)
  have hs_sub_norm : 1 ≤ ‖s - 1‖ := by
    have : |s.im| = |(s - 1).im| := by simp
    rw [this] at hsim
    exact hsim.trans (Complex.abs_im_le_norm (s - 1))
  have hzeta_le_Q : ‖riemannZeta s‖ ≤ ‖s‖ * ‖s - 1‖ * ‖riemannZeta s‖ := by
    have hone : 1 ≤ ‖s‖ * ‖s - 1‖ := by
      nlinarith [mul_le_mul hs_norm hs_sub_norm zero_le_one (norm_nonneg s)]
    exact le_mul_of_one_le_left (norm_nonneg _) hone
  have hs_add_norm : ‖s + 2‖ ≤ |s.im| + 3 := by
    calc
      ‖s + 2‖ ≤ |(s + 2).re| + |(s + 2).im| :=
        Complex.norm_le_abs_re_add_abs_im (s + 2)
      _ = s.re + 2 + |s.im| := by
        have hre : (s + 2).re = s.re + 2 := by norm_num
        have him : (s + 2).im = s.im := by norm_num
        rw [hre, him]
        rw [abs_of_nonneg (by linarith [hsre.1])]
      _ ≤ |s.im| + 3 := by linarith [hsre.2]
  have hden_le : ‖(s + 2) ^ 4‖ ≤ (|s.im| + 3) ^ 4 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hs_add_norm 4
  exact hzeta_le_Q.trans (hQ.trans
    (mul_le_mul_of_nonneg_left hden_le hC))

/-- Polynomial zeta growth on the wider strip needed by the Jensen/Borel
disks.  The critical part `0 ≤ Re(s) ≤ 1` comes from Phragmen--Lindelof; the
right part uses the Abel bound. -/
theorem exists_norm_riemannZeta_le_polynomial_on_zero_four :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      s.re ∈ Icc (0 : ℝ) 4 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ 4 := by
  rcases exists_norm_riemannZeta_le_polynomial_on_zero_one with
    ⟨C0, hC0, hleft⟩
  let C := max C0 8
  refine ⟨C, hC0.trans (le_max_left _ _), ?_⟩
  intro s hsre hsim
  by_cases hs1 : s.re ≤ 1
  · exact (hleft s ⟨hsre.1, hs1⟩ hsim).trans
      (mul_le_mul_of_nonneg_right (le_max_left C0 8)
        (pow_nonneg (by positivity) 4))
  · have hs14 : s.re ∈ Icc (1 : ℝ) 4 := ⟨le_of_not_ge hs1, hsre.2⟩
    have hbase :=
      norm_riemannZeta_le_two_mul_norm_of_one_le_re_of_one_le_abs_im
        s hs14.1 hsim
    have hnorm : ‖s‖ ≤ |s.im| + 4 := by
      calc
        ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ = s.re + |s.im| := by rw [abs_of_nonneg (by linarith [hs14.1])]
        _ ≤ |s.im| + 4 := by linarith [hs14.2]
    have hlinear : ‖riemannZeta s‖ ≤ 4 * (|s.im| + 4) := by
      nlinarith
    have hshift : |s.im| + 4 ≤ 2 * (|s.im| + 3) := by
      linarith [abs_nonneg s.im]
    have hx : 1 ≤ |s.im| + 3 := by linarith [abs_nonneg s.im]
    have hxpow : |s.im| + 3 ≤ (|s.im| + 3) ^ 4 := by
      simpa using pow_le_pow_right₀ hx (by norm_num : (1 : ℕ) ≤ 4)
    calc
      ‖riemannZeta s‖ ≤ 4 * (|s.im| + 4) := hlinear
      _ ≤ 8 * (|s.im| + 3) := by nlinarith
      _ ≤ 8 * (|s.im| + 3) ^ 4 := mul_le_mul_of_nonneg_left hxpow (by norm_num)
      _ ≤ C * (|s.im| + 3) ^ 4 :=
        mul_le_mul_of_nonneg_right (le_max_right C0 8) (pow_nonneg (by positivity) 4)

/-- A three-quarter-radius Borel--Caratheodory/Cauchy estimate.  Reserving only
one quarter of the analytic disk, rather than one half, lets a zeta disk
centered at `2 + I*t` reach `Re(s) = 1` while its outer boundary remains in a
fixed polynomial-growth strip. -/
lemma norm_logDeriv_le_six_mul_div_of_analyticOnNhd_nonzero_re_log_bound
    {g : ℂ → ℂ} {c z : ℂ} {R M ρ : ℝ}
    (hR : 0 < R) (hM : 0 < M) (hρ : 0 < ρ)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hgne : ∀ w ∈ Metric.closedBall c R, g w ≠ 0)
    (hre : ∀ w ∈ Metric.ball c R,
      Real.log ‖g w‖ - Real.log ‖g c‖ ≤ M)
    (hzρ : dist z c + ρ ≤ 3 * R / 4) :
    ‖logDeriv g z‖ ≤ 6 * M / ρ := by
  obtain ⟨h, hh, hhc, hhderiv, _hhexp, hhre⟩ :=
    exists_normalized_analytic_log_primitive_on_ball hR hg hgne
  have hmaps : MapsTo h (Metric.ball c R) {w : ℂ | w.re ≤ M} := by
    intro w hw
    change (h w).re ≤ M
    rw [hhre w hw]
    exact hre w hw
  have hclosed_subset : Metric.closedBall z ρ ⊆ Metric.ball c R := by
    intro w hw
    have hwz : dist w z ≤ ρ := Metric.mem_closedBall.mp hw
    have hwc : dist w c ≤ dist w z + dist z c := dist_triangle _ _ _
    apply Metric.mem_ball.mpr
    linarith
  have hdiff_closed : DifferentiableOn ℂ h (Metric.closedBall z ρ) :=
    hh.differentiableOn.mono hclosed_subset
  have hdiff : DiffContOnCl ℂ h (Metric.ball z ρ) :=
    hdiff_closed.diffContOnCl_ball subset_rfl
  have hnorm : ∀ w ∈ Metric.sphere z ρ, ‖h w‖ ≤ 6 * M := by
    intro w hw
    have hwz : dist w z = ρ := Metric.mem_sphere.mp hw
    have hwc : dist w c ≤ dist w z + dist z c := dist_triangle _ _ _
    have hwc_three_quarters : ‖w - c‖ ≤ 3 * R / 4 := by
      rw [← dist_eq_norm]
      linarith
    have hwc_lt : ‖w - c‖ < R := by linarith
    have hw_ball : w ∈ Metric.ball c R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hwc_lt
    have hbc := borelCaratheodory_zero_centered
      hM hh.differentiableOn hmaps hR hw_ball hhc
    have hden : 0 < R - ‖w - c‖ := by linarith
    have hratio : ‖w - c‖ / (R - ‖w - c‖) ≤ 3 := by
      rw [div_le_iff₀ hden]
      linarith
    calc
      ‖h w‖ ≤ 2 * M * ‖w - c‖ / (R - ‖w - c‖) := hbc
      _ = (2 * M) * (‖w - c‖ / (R - ‖w - c‖)) := by ring
      _ ≤ (2 * M) * 3 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 6 * M := by ring
  have hz_ball : z ∈ Metric.ball c R := by
    apply Metric.mem_ball.mpr
    linarith
  have hcauchy : ‖deriv h z‖ ≤ (6 * M) / ρ :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdiff hnorm
  simpa [hhderiv z hz_ball] using hcauchy

/-- Three-quarter-radius moving-interior form with separate boundary and
center logarithmic bounds. -/
lemma norm_logDeriv_le_six_mul_max_sub_div_of_sphere_log_norm_le_of_center_lower
    {g : ℂ → ℂ} {c z : ℂ} {R B C0 ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hgne : ∀ w ∈ Metric.closedBall c R, g w ≠ 0)
    (hcenter : C0 ≤ Real.log ‖g c‖)
    (hsphere : ∀ w ∈ Metric.sphere c R, Real.log ‖g w‖ ≤ B)
    (hzρ : dist z c + ρ ≤ 3 * R / 4) :
    ‖logDeriv g z‖ ≤ 6 * max (B - C0) 1 / ρ := by
  let M : ℝ := max (B - C0) 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hdiff : DiffContOnCl ℂ g (Metric.ball c R) :=
    hg.differentiableOn.diffContOnCl_ball subset_rfl
  have hsphere_norm : ∀ w ∈ Metric.sphere c R, ‖g w‖ ≤ Real.exp B := by
    intro w hw
    have hexp := Real.exp_le_exp.mpr (hsphere w hw)
    rw [Real.exp_log (norm_pos_iff.mpr
      (hgne w (Metric.sphere_subset_closedBall hw)))] at hexp
    exact hexp
  have hclosed_norm : ∀ w ∈ Metric.closedBall c R, ‖g w‖ ≤ Real.exp B := by
    intro w hw
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball hdiff
    · intro u hu
      exact hsphere_norm u (Metric.frontier_ball_subset_sphere hu)
    · rw [closure_ball c hR.ne']
      exact hw
  have hre : ∀ w ∈ Metric.ball c R,
      Real.log ‖g w‖ - Real.log ‖g c‖ ≤ M := by
    intro w hw
    have hw_closed : w ∈ Metric.closedBall c R :=
      Metric.ball_subset_closedBall hw
    have hlog_w : Real.log ‖g w‖ ≤ B := by
      have hlog := Real.log_le_log
        (norm_pos_iff.mpr (hgne w hw_closed)) (hclosed_norm w hw_closed)
      simpa using hlog
    have hsum : Real.log ‖g w‖ - Real.log ‖g c‖ ≤ B - C0 := by
      linarith
    exact hsum.trans (le_max_left _ _)
  simpa [M] using
    norm_logDeriv_le_six_mul_div_of_analyticOnNhd_nonzero_re_log_bound
      hR hM hρ hg hgne hre hzρ

/-- Three-quarter-radius Borel/Cauchy bound for the mixed zero-removed zeta
unit. -/
lemma norm_logDeriv_mixedCanonicalRegularUnit_riemannZetaDivisor_le_three_quarters
    {c z : ℂ} {r b B ρ : ℝ} {g : ℂ → ℂ}
    (hc : (3 / 2 : ℝ) ≤ c.re) (hr : 0 < r) (hrb : r < b) (hρ : 0 < ρ)
    (havoid : ∀ w : ℂ, w ∈ Metric.closedBall c b → w ≠ 1)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c b))
    (hgne : ∀ u : (Metric.closedBall c b : Set ℂ), g u ≠ 0)
    (hfactor : riemannZeta =ᶠ[codiscreteWithin (Metric.closedBall c b)]
      (∏ᶠ u, (· - u) ^
        MeromorphicOn.divisor riemannZeta (Metric.closedBall c b) u) * g)
    (hsphere_ne : ∀ w ∈ Metric.sphere c r, riemannZeta w ≠ 0)
    (hsphere_log : ∀ w ∈ Metric.sphere c r, Real.log ‖riemannZeta w‖ ≤ B)
    (hzρ : dist z c + ρ ≤ 3 * r / 4) :
    ‖logDeriv
        (mixedCanonicalRegularUnit c r
          (riemannZetaDivisorSupport c b)
          (riemannZetaDivisorMultiplicity c b) g) z‖ ≤
      6 * max (B + Real.log 3) 1 / ρ := by
  let h := mixedCanonicalRegularUnit c r
    (riemannZetaDivisorSupport c b)
    (riemannZetaDivisorMultiplicity c b) g
  have hh : AnalyticOnNhd ℂ h (Metric.closedBall c r) :=
    analyticOnNhd_mixedCanonicalRegularUnit hrb.le hg
  have hhne : ∀ w ∈ Metric.closedBall c r, h w ≠ 0 := by
    intro w hw
    exact mixedCanonicalRegularUnit_riemannZetaDivisor_ne_zero_closedBall
      hrb havoid hg hgne hfactor hsphere_ne hw
  have hcenter : (1 / 3 : ℝ) ≤ ‖h c‖ :=
    (one_third_le_norm_riemannZeta_of_three_halves_le_re c hc).trans
      (norm_riemannZeta_le_norm_mixedCanonicalRegularUnit_riemannZetaDivisor_center
        hr hrb havoid hg hgne hfactor)
  have hlog_center : -Real.log 3 ≤ Real.log ‖h c‖ := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 3) hcenter
    simpa [one_div, Real.log_inv] using hlog
  have hsphere_h : ∀ w ∈ Metric.sphere c r, Real.log ‖h w‖ ≤ B := by
    intro w hw
    rw [show ‖h w‖ = ‖riemannZeta w‖ by
      exact
        norm_mixedCanonicalRegularUnit_riemannZetaDivisor_eq_norm_riemannZeta_on_sphere
          hrb havoid hg hgne hfactor hw]
    exact hsphere_log w hw
  have hbound :=
    norm_logDeriv_le_six_mul_max_sub_div_of_sphere_log_norm_le_of_center_lower
      hr hρ hh hhne hlog_center hsphere_h hzρ
  simpa [sub_neg_eq_add] using hbound

/-- Uniform regular-part estimate after removing all zeta divisor principal
parts, with a three-quarter retained Borel disk. -/
lemma norm_regularized_logDeriv_riemannZeta_le_mixedCanonical_bound_three_quarters
    {c z : ℂ} {d r b B ρ : ℝ} {g : ℂ → ℂ}
    (hc : (3 / 2 : ℝ) ≤ c.re) (hd : 0 ≤ d) (hdr : d < r) (hrb : r < b)
    (hρ : 0 < ρ)
    (havoid : ∀ w : ℂ, w ∈ Metric.closedBall c b → w ≠ 1)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c b))
    (hgne : ∀ u : (Metric.closedBall c b : Set ℂ), g u ≠ 0)
    (hfactor : riemannZeta =ᶠ[codiscreteWithin (Metric.closedBall c b)]
      (∏ᶠ u, (· - u) ^
        MeromorphicOn.divisor riemannZeta (Metric.closedBall c b) u) * g)
    (hsphere_ne : ∀ w ∈ Metric.sphere c r, riemannZeta w ≠ 0)
    (hsphere_log : ∀ w ∈ Metric.sphere c r, Real.log ‖riemannZeta w‖ ≤ B)
    (hz : z ∈ Metric.closedBall c d) (hzeta : riemannZeta z ≠ 0)
    (hzρ : dist z c + ρ ≤ 3 * r / 4) :
    ‖logDeriv riemannZeta z -
        ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
          (Metric.closedBall c b) u : ℂ) * (z - u)⁻¹‖ ≤
      6 * max (B + Real.log 3) 1 / ρ +
        (∑ᶠ u, (MeromorphicOn.divisor riemannZeta
          (Metric.closedBall c b) u : ℝ)) / (r - d) := by
  let D := MeromorphicOn.divisor riemannZeta (Metric.closedBall c b)
  have hD_nonneg : 0 ≤ D := divisor_riemannZeta_closedBall_nonneg havoid
  have hD_finite : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall c b)
  have hunit :=
    norm_logDeriv_mixedCanonicalRegularUnit_riemannZetaDivisor_le_three_quarters
      hc (hd.trans_lt hdr) hrb hρ havoid hg hgne hfactor
        hsphere_ne hsphere_log hzρ
  have hcorr := norm_logDeriv_mixedCanonicalZeroProduct_le_sum_div
    (zeros := hD_finite.toFinset) (m := fun u => (D u).toNat)
    hd hdr hz
  rw [logDeriv_mixedCanonicalZeroProduct hdr hz] at hcorr
  rw [sum_toNat_eq_finsum_cast_of_nonneg_finiteSupport
    hD_finite (fun u => hD_nonneg u)] at hcorr
  have hidentity :=
    regularized_logDeriv_riemannZeta_eq_mixedCanonicalRegularUnit_sub_correction
      hdr hrb havoid hg hgne hfactor hz hzeta
  rw [hidentity]
  exact (norm_sub_le _ _).trans (add_le_add hunit hcorr)

/-- Good-circle selection plus Jensen counting, with the strengthened
three-quarter retained disk.  The right-hand side is deterministic and does
not depend on the selected circle or the nearest zero. -/
lemma norm_regularized_logDeriv_riemannZeta_le_of_good_radius_and_jensen_three_quarters
    {d a q b R t M K rho : ℝ}
    (hd : 0 ≤ d) (hda : d < a) (haq : a < q) (hqb : q < b)
    (hbR : b < R) (hheight : R < |t|) (hM : 1 ≤ M)
    (hrho : 0 < rho) (hgeom : d + rho ≤ 3 * a / 4)
    (houter : ∀ z : ℂ,
      z ∈ Metric.sphere ((2 : ℂ) + I * t) R → ‖riemannZeta z‖ ≤ M)
    (hinner : ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) q,
      Real.log ‖riemannZeta z‖ ≤ K) :
    ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) d,
      riemannZeta z ≠ 0 →
      ‖logDeriv riemannZeta z -
          ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
            (Metric.closedBall ((2 : ℂ) + I * t) b) u : ℂ) * (z - u)⁻¹‖ ≤
        6 * max (K + Real.log 3) 1 / rho +
          ((Real.log M + Real.log 3) / Real.log (R / b)) / (a - d) := by
  classical
  let c : ℂ := (2 : ℂ) + I * t
  let D := MeromorphicOn.divisor riemannZeta (Metric.closedBall c b)
  have ha : 0 < a := hd.trans_lt hda
  have hb : 0 < b := ha.trans haq |>.trans hqb
  have havoid : ∀ w : ℂ, w ∈ Metric.closedBall c b → w ≠ 1 := by
    intro w hw
    exact closedBall_sigma_it_ne_one_of_height_add_le
      (z := w) (σ := 2) (t := t) (R := b) (H := |t| - b)
        (by simpa [c] using hw) (by linarith) (by linarith)
  rcases exists_good_radius_separated_from_riemannZeta_zeros_closedBall_strictly_inside
      ha haq hqb havoid with
    ⟨_zeros, r, _hzeros, hrpos, hr, _hsep, hsphere_ne⟩
  rcases exists_analytic_nonzero_factorization_riemannZeta_closedBall havoid with
    ⟨g, hg, hgne, hfactor⟩
  have hsphere_log : ∀ w ∈ Metric.sphere c r,
      Real.log ‖riemannZeta w‖ ≤ K := by
    intro w hw
    apply hinner w
    have hw_closed : w ∈ Metric.closedBall c r :=
      Metric.sphere_subset_closedBall hw
    simpa [c] using Metric.closedBall_subset_closedBall hr.2 hw_closed
  have hD_nonneg : 0 ≤ D := divisor_riemannZeta_closedBall_nonneg havoid
  have hmass_nonneg : 0 ≤ ∑ᶠ u, (D u : ℝ) := by
    apply finsum_nonneg
    intro u
    exact_mod_cast hD_nonneg u
  have hmass : (∑ᶠ u, (D u : ℝ)) ≤
      (Real.log M + Real.log 3) / Real.log (R / b) := by
    simpa [c, D] using
      finsum_divisor_riemannZeta_closedBall_le_log_bound_div
        hb hbR hheight hM houter
  intro z hz hzeta
  have hdr : d < r := hda.trans_le hr.1
  have hrb : r < b := hr.2.trans_lt hqb
  have hzdist : dist z c ≤ d := by
    simpa [c, Metric.mem_closedBall] using hz
  have hzrho : dist z c + rho ≤ 3 * r / 4 := by
    nlinarith [hr.1]
  have hlocal :=
    norm_regularized_logDeriv_riemannZeta_le_mixedCanonical_bound_three_quarters
      (c := c) (d := d) (r := r) (b := b) (B := K) (ρ := rho)
      (by norm_num [c]) hd hdr hrb hrho havoid hg hgne hfactor
        hsphere_ne hsphere_log (by simpa [c] using hz) hzeta hzrho
  have had : 0 < a - d := sub_pos.mpr hda
  have hradial : (∑ᶠ u, (D u : ℝ)) / (r - d) ≤
      (∑ᶠ u, (D u : ℝ)) / (a - d) :=
    div_le_div_of_nonneg_left hmass_nonneg had (sub_le_sub_right hr.1 d)
  have hmass_div : (∑ᶠ u, (D u : ℝ)) / (a - d) ≤
      ((Real.log M + Real.log 3) / Real.log (R / b)) / (a - d) :=
    div_le_div_of_nonneg_right hmass had.le
  simpa [c, D] using
    hlocal.trans (add_le_add_right (hradial.trans hmass_div) _)

/-- The fixed Jensen disks centered at `2 + I*t` inherit the global
polynomial zeta-growth estimate uniformly. -/
lemma norm_riemannZeta_le_fixed_jensen_closedBall
    {C r t : ℝ}
    (hC : 0 ≤ C)
    (hpoly : ∀ s : ℂ, s.re ∈ Icc (0 : ℝ) 4 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ 4)
    (hr : r ≤ 7 / 4) (ht : 4 ≤ |t|)
    {z : ℂ} (hz : z ∈ Metric.closedBall ((2 : ℂ) + I * t) r) :
    ‖riemannZeta z‖ ≤ max C 1 * (|t| + 5) ^ 4 := by
  have hdist : ‖z - ((2 : ℂ) + I * t)‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hre_abs : |z.re - 2| ≤ r := by
    have := Complex.abs_re_le_norm (z - ((2 : ℂ) + I * t))
    simpa using this.trans hdist
  have him_abs : |z.im - t| ≤ r := by
    have := Complex.abs_im_le_norm (z - ((2 : ℂ) + I * t))
    simpa using this.trans hdist
  have hzre : z.re ∈ Icc (0 : ℝ) 4 := by
    constructor <;> rw [abs_le] at hre_abs <;> linarith
  have hzim_lower : 1 ≤ |z.im| := by
    have htri : |t| ≤ |z.im - t| + |z.im| := by
      calc
        |t| = |(t - z.im) + z.im| := by ring_nf
        _ ≤ |t - z.im| + |z.im| := abs_add_le _ _
        _ = |z.im - t| + |z.im| := by rw [abs_sub_comm]
    linarith
  have hzim_upper : |z.im| ≤ |t| + r := by
    calc
      |z.im| = |(z.im - t) + t| := by ring_nf
      _ ≤ |z.im - t| + |t| := abs_add_le _ _
      _ ≤ |t| + r := by linarith
  have hbase : |z.im| + 3 ≤ |t| + 5 := by linarith
  calc
    ‖riemannZeta z‖ ≤ C * (|z.im| + 3) ^ 4 := hpoly z hzre hzim_lower
    _ ≤ C * (|t| + 5) ^ 4 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hbase 4) hC
    _ ≤ max C 1 * (|t| + 5) ^ 4 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by positivity) 4)

/-- Logarithmic form of the fixed Jensen-disk growth bound. -/
lemma log_norm_riemannZeta_le_fixed_jensen_closedBall
    {C r t : ℝ}
    (hC : 0 ≤ C)
    (hpoly : ∀ s : ℂ, s.re ∈ Icc (0 : ℝ) 4 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ 4)
    (hr : r ≤ 7 / 4) (ht : 4 ≤ |t|)
    {z : ℂ} (hz : z ∈ Metric.closedBall ((2 : ℂ) + I * t) r) :
    Real.log ‖riemannZeta z‖ ≤
      Real.log (max C 1) + 4 * Real.log (|t| + 5) := by
  have hnorm := norm_riemannZeta_le_fixed_jensen_closedBall
    hC hpoly hr ht hz
  have hA : 1 ≤ max C 1 := le_max_right _ _
  have hApos : 0 < max C 1 := zero_lt_one.trans_le hA
  have hxpos : 0 < |t| + 5 := by positivity
  have hMpos : 0 < max C 1 * (|t| + 5) ^ 4 :=
    mul_pos hApos (pow_pos hxpos 4)
  by_cases hzeta : ‖riemannZeta z‖ = 0
  · rw [hzeta, Real.log_zero]
    have hlogA : 0 ≤ Real.log (max C 1) := Real.log_nonneg hA
    have hlogx : 0 ≤ Real.log (|t| + 5) :=
      Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  · have hzeta_pos : 0 < ‖riemannZeta z‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzeta)
    have hlog := Real.log_le_log hzeta_pos hnorm
    rw [Real.log_mul hApos.ne' (pow_ne_zero 4 hxpos.ne'), Real.log_pow] at hlog
    norm_num at hlog ⊢
    exact hlog

/-- Unconditional regular-part estimate at every nonzero zeta value in the
fixed disk reaching `Re(s) = 1`.  All Jensen/Borel inputs are discharged by
the polynomial zeta growth theorem above; no vertical-growth premise remains. -/
theorem exists_fixed_disk_regularized_logDeriv_riemannZeta_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ t : ℝ, 4 ≤ |t| →
      ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) 1,
        riemannZeta z ≠ 0 →
        ‖logDeriv riemannZeta z -
            ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
              (Metric.closedBall ((2 : ℂ) + I * t) (17 / 10 : ℝ)) u : ℂ) *
                (z - u)⁻¹‖ ≤
          6 * max
              (Real.log A + 4 * Real.log (|t| + 5) + Real.log 3) 1 /
                (1 / 16 : ℝ) +
            ((Real.log (A * (|t| + 5) ^ 4) + Real.log 3) /
                Real.log ((7 / 4 : ℝ) / (17 / 10 : ℝ))) /
              ((3 / 2 : ℝ) - 1) := by
  rcases exists_norm_riemannZeta_le_polynomial_on_zero_four with
    ⟨C, hC, hpoly⟩
  let A : ℝ := max C 1
  have hA : 1 ≤ A := le_max_right _ _
  refine ⟨A, hA, ?_⟩
  intro t ht z hz hzeta
  let M : ℝ := A * (|t| + 5) ^ 4
  let K : ℝ := Real.log A + 4 * Real.log (|t| + 5)
  have hM : 1 ≤ M := by
    have hx : 1 ≤ |t| + 5 := by linarith [abs_nonneg t]
    have hxpow : 1 ≤ (|t| + 5) ^ 4 := one_le_pow₀ hx
    exact one_le_mul_of_one_le_of_one_le hA hxpow
  have houter : ∀ w : ℂ,
      w ∈ Metric.sphere ((2 : ℂ) + I * t) (7 / 4 : ℝ) →
        ‖riemannZeta w‖ ≤ M := by
    intro w hw
    have hwc : w ∈ Metric.closedBall ((2 : ℂ) + I * t) (7 / 4 : ℝ) :=
      Metric.sphere_subset_closedBall hw
    simpa [A, M] using
      norm_riemannZeta_le_fixed_jensen_closedBall hC hpoly (by norm_num) ht hwc
  have hinner : ∀ w ∈ Metric.closedBall
      ((2 : ℂ) + I * t) (8 / 5 : ℝ), Real.log ‖riemannZeta w‖ ≤ K := by
    intro w hw
    simpa [A, K] using
      log_norm_riemannZeta_le_fixed_jensen_closedBall hC hpoly (by norm_num) ht hw
  have hbound :=
    norm_regularized_logDeriv_riemannZeta_le_of_good_radius_and_jensen_three_quarters
      (d := (1 : ℝ)) (a := (3 / 2 : ℝ)) (q := (8 / 5 : ℝ))
      (b := (17 / 10 : ℝ)) (R := (7 / 4 : ℝ)) (t := t)
      (M := M) (K := K) (rho := (1 / 16 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by linarith) hM (by norm_num) (by norm_num)
      houter hinner z hz hzeta
  simpa [A, M, K] using hbound

/-- Uniform logarithmic regular-part estimate at nonzero zeta values in the
boundary disk.  This is the unconditional `O(log |t|)` input needed by
zero-repulsion arguments: the only singular terms left are the explicitly
displayed local zeta-zero principal parts. -/
theorem exists_regularized_logDeriv_riemannZeta_log_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 4 ≤ |t| →
      ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) 1,
        riemannZeta z ≠ 0 →
        ‖logDeriv riemannZeta z -
            ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
              (Metric.closedBall ((2 : ℂ) + I * t) (17 / 10 : ℝ)) u : ℂ) *
                (z - u)⁻¹‖ ≤
          B * (1 + Real.log (|t| + 5)) := by
  rcases exists_fixed_disk_regularized_logDeriv_riemannZeta_bound with
    ⟨A, hA, hfixed⟩
  let c0 : ℝ := Real.log A + Real.log 3
  let D : ℝ := Real.log ((7 / 4 : ℝ) / (17 / 10 : ℝ))
  let E : ℝ := D⁻¹
  let m : ℝ := max c0 1
  let B : ℝ := 96 * m + 384 + (2 * c0 + 8) * E
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    exact add_nonneg (Real.log_nonneg hA) (Real.log_nonneg (by norm_num))
  have hD : 0 < D := by
    dsimp [D]
    apply Real.log_pos
    norm_num
  have hE : 0 < E := by simp [E, hD]
  have hm : 0 ≤ m := hc0.trans (le_max_left _ _)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro t ht z hz hzeta
  have hbound := hfixed t ht z hz hzeta
  let L : ℝ := Real.log (|t| + 5)
  have hx : 1 ≤ |t| + 5 := by linarith [abs_nonneg t]
  have hxpos : 0 < |t| + 5 := zero_lt_one.trans_le hx
  have hL : 0 ≤ L := by exact Real.log_nonneg hx
  have hlogM : Real.log (A * (|t| + 5) ^ 4) = Real.log A + 4 * L := by
    rw [Real.log_mul hApos.ne' (pow_ne_zero 4 hxpos.ne'), Real.log_pow]
    simp [L]
  rw [hlogM] at hbound
  have hmax : max (c0 + 4 * L) 1 ≤ m + 4 * L := by
    apply max_le
    · simpa [m, add_comm] using
        (add_le_add_right (le_max_left c0 (1 : ℝ)) (4 * L))
    · have : 1 ≤ m := le_max_right c0 (1 : ℝ)
      linarith
  have hconst : 0 ≤ 96 * m + 2 * c0 * E := by positivity
  have hslope : 0 ≤ 384 + 8 * E := by positivity
  have hrewrite :
      6 * max (Real.log A + 4 * L + Real.log 3) 1 / (1 / 16 : ℝ) +
          ((Real.log A + 4 * L + Real.log 3) / D) / ((3 / 2 : ℝ) - 1) =
        96 * max (c0 + 4 * L) 1 + 2 * (c0 + 4 * L) * E := by
    dsimp [c0, E]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    norm_num
    ring
  rw [hrewrite] at hbound
  apply hbound.trans
  have hmain :
      96 * max (c0 + 4 * L) 1 + 2 * (c0 + 4 * L) * E ≤
        (96 * m + 2 * c0 * E) + (384 + 8 * E) * L := by
    nlinarith
  apply hmain.trans
  dsimp [B]
  nlinarith

/-- Every local zeta-zero principal part has nonnegative real part when
evaluated on or to the right of `Re(s)=1`. -/
lemma re_finsum_riemannZeta_divisor_mul_inv_nonneg
    {c z : ℂ} {b : ℝ}
    (havoid : ∀ u : ℂ, u ∈ Metric.closedBall c b → u ≠ 1)
    (hzre : 1 ≤ z.re) :
    0 ≤ (∑ᶠ u, (MeromorphicOn.divisor riemannZeta
      (Metric.closedBall c b) u : ℂ) * (z - u)⁻¹).re := by
  classical
  let D := MeromorphicOn.divisor riemannZeta (Metric.closedBall c b)
  have hD : 0 ≤ D := divisor_riemannZeta_closedBall_nonneg havoid
  have hfinite : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall c b)
  let F : Finset ℂ := hfinite.toFinset
  have hsupp : (fun u : ℂ => (D u : ℂ) * (z - u)⁻¹).support ⊆ F := by
    intro u hu
    apply hfinite.mem_toFinset.mpr
    by_contra hDu
    have hDu0 : D u = 0 := by simpa [Function.mem_support] using hDu
    simp [hDu0] at hu
  have hterm : ∀ u ∈ F, 0 ≤ ((D u : ℂ) * (z - u)⁻¹).re := by
    intro u hu
    have hu_support : u ∈ D.support := hfinite.mem_toFinset.mp hu
    have hu_closed : u ∈ Metric.closedBall c b := D.supportWithinDomain hu_support
    have hu_analytic : AnalyticAt ℂ riemannZeta u :=
      analyticOnNhd_riemannZeta_ne_one u (havoid u hu_closed)
    have hu_zero : riemannZeta u = 0 := by
      by_contra hne
      have horder : meromorphicOrderAt riemannZeta u = 0 :=
        (hu_analytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).2 hne
      have hDu0 : D u = 0 := by
        dsimp [D]
        rw [MeromorphicOn.divisor_apply
          (meromorphicOn_riemannZeta_closedBall c b) hu_closed, horder]
        simp
      have hDne : D u ≠ 0 := by
        simpa [Function.mem_support] using hu_support
      exact hDne hDu0
    have hure : u.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hu_zero
    have hinv : 0 ≤ ((z - u)⁻¹).re := by
      rw [Complex.inv_re]
      apply div_nonneg
      · simp only [sub_re]
        linarith
      · exact Complex.normSq_nonneg _
    rw [Complex.mul_re]
    change 0 ≤ (D u : ℝ) * ((z - u)⁻¹).re - 0 * ((z - u)⁻¹).im
    simpa using mul_nonneg (by exact_mod_cast hD u) hinv
  calc
    0 ≤ ∑ u ∈ F, ((D u : ℂ) * (z - u)⁻¹).re :=
      Finset.sum_nonneg fun u hu => hterm u hu
    _ = (∑ u ∈ F, (D u : ℂ) * (z - u)⁻¹).re := by simp
    _ = (∑ᶠ u, (D u : ℂ) * (z - u)⁻¹).re := by
      congr 1
      exact (finsum_eq_sum_of_support_subset
        (fun u : ℂ => (D u : ℂ) * (z - u)⁻¹) hsupp).symm

/-- A same-height zeta zero inside the factorization disk contributes at
least the unit principal part to the real part of the full divisor sum. -/
lemma one_div_le_re_finsum_riemannZeta_divisor_mul_inv
    {c s rho : ℂ} {b : ℝ}
    (havoid : ∀ u : ℂ, u ∈ Metric.closedBall c b → u ≠ 1)
    (hsre : 1 ≤ s.re) (hrho : rho ∈ Metric.closedBall c b)
    (hzero : riemannZeta rho = 0) (him : rho.im = s.im)
    (hsub : 0 < s.re - rho.re) :
    1 / (s.re - rho.re) ≤
      (∑ᶠ u, (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall c b) u : ℂ) * (s - u)⁻¹).re := by
  classical
  let D := MeromorphicOn.divisor riemannZeta (Metric.closedBall c b)
  have hD : 0 ≤ D := divisor_riemannZeta_closedBall_nonneg havoid
  have hfinite : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall c b)
  let F : Finset ℂ := hfinite.toFinset
  have hrho_analytic : AnalyticAt ℂ riemannZeta rho :=
    analyticOnNhd_riemannZeta_ne_one rho (havoid rho hrho)
  have hDrho_ne : D rho ≠ 0 := by
    intro hDrho
    have horder : meromorphicOrderAt riemannZeta rho = 0 := by
      have := MeromorphicOn.divisor_apply
        (meromorphicOn_riemannZeta_closedBall c b) hrho
      rw [this] at hDrho
      rcases WithTop.untop₀_eq_zero.mp hDrho with hzero_order | htop
      · exact hzero_order
      · have heq := hrho_analytic.meromorphicOrderAt_eq
        rw [htop] at heq
        have han_top : analyticOrderAt riemannZeta rho = ⊤ := by
          simpa using heq.symm
        exact ((analyticOrderAt_riemannZeta_ne_top_of_ne_one
          (havoid rho hrho)) han_top).elim
    exact ((hrho_analytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mp
      horder) hzero
  have hrhoF : rho ∈ F := by
    apply hfinite.mem_toFinset.mpr
    simpa [Function.mem_support] using hDrho_ne
  have hpoint : ∀ u ∈ F, 0 ≤ ((D u : ℂ) * (s - u)⁻¹).re := by
    intro u hu
    have hu_support : u ∈ D.support := hfinite.mem_toFinset.mp hu
    have hu_closed : u ∈ Metric.closedBall c b := D.supportWithinDomain hu_support
    have hu_analytic : AnalyticAt ℂ riemannZeta u :=
      analyticOnNhd_riemannZeta_ne_one u (havoid u hu_closed)
    have hu_zero : riemannZeta u = 0 := by
      by_contra hne
      have horder : meromorphicOrderAt riemannZeta u = 0 :=
        (hu_analytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).2 hne
      have hDu0 : D u = 0 := by
        dsimp [D]
        rw [MeromorphicOn.divisor_apply
          (meromorphicOn_riemannZeta_closedBall c b) hu_closed, horder]
        simp
      have hDne : D u ≠ 0 := by
        simpa [Function.mem_support] using hu_support
      exact hDne hDu0
    have hure : u.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hu_zero
    have hinv : 0 ≤ ((s - u)⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg (by simp only [sub_re]; linarith) (Complex.normSq_nonneg _)
    rw [Complex.mul_re]
    change 0 ≤ (D u : ℝ) * ((s - u)⁻¹).re - 0 * ((s - u)⁻¹).im
    simpa using mul_nonneg (by exact_mod_cast hD u) hinv
  have hDrho_one : (1 : ℝ) ≤ D rho := by
    have hnonneg : (0 : ℤ) ≤ D rho := hD rho
    have : (1 : ℤ) ≤ D rho := by omega
    exact_mod_cast this
  have hinv_re : ((s - rho)⁻¹).re = 1 / (s.re - rho.re) :=
    inv_sub_same_im_re him hsub
  have hcandidate :
      1 / (s.re - rho.re) ≤ ((D rho : ℂ) * (s - rho)⁻¹).re := by
    rw [Complex.mul_re]
    change 1 / (s.re - rho.re) ≤
      (D rho : ℝ) * ((s - rho)⁻¹).re - 0 * ((s - rho)⁻¹).im
    rw [zero_mul, sub_zero, hinv_re]
    have hinv_nonneg : 0 ≤ 1 / (s.re - rho.re) := by positivity
    simpa using mul_le_mul_of_nonneg_right hDrho_one hinv_nonneg
  have hsum : ((D rho : ℂ) * (s - rho)⁻¹).re ≤
      ∑ u ∈ F, ((D u : ℂ) * (s - u)⁻¹).re := by
    exact Finset.single_le_sum (fun u hu => hpoint u hu) hrhoF
  have hsupp : (fun u : ℂ => (D u : ℂ) * (s - u)⁻¹).support ⊆ F := by
    intro u hu
    apply hfinite.mem_toFinset.mpr
    by_contra hDu
    have hDu0 : D u = 0 := by simpa [Function.mem_support] using hDu
    simp [hDu0] at hu
  calc
    1 / (s.re - rho.re) ≤ ((D rho : ℂ) * (s - rho)⁻¹).re := hcandidate
    _ ≤ ∑ u ∈ F, ((D u : ℂ) * (s - u)⁻¹).re := hsum
    _ = (∑ u ∈ F, (D u : ℂ) * (s - u)⁻¹).re := by simp
    _ = (∑ᶠ u, (D u : ℂ) * (s - u)⁻¹).re := by
      congr 1
      exact (finsum_eq_sum_of_support_subset
        (fun u : ℂ => (D u : ℂ) * (s - u)⁻¹) hsupp).symm

/-- Zero-repulsion estimate obtained by retaining one same-height zero from
the full divisor principal-part sum. -/
theorem exists_re_neg_deriv_div_riemannZeta_le_neg_inv_add_log_bound
    : ∃ B : ℝ, 0 ≤ B ∧ ∀ σ β t : ℝ,
      1 ≤ σ → σ ≤ 2 → 4 ≤ |t| → (3 / 10 : ℝ) ≤ β → β < 1 →
      riemannZeta ((β : ℂ) + I * t) = 0 →
      (-deriv riemannZeta ((σ : ℂ) + I * t) /
          riemannZeta ((σ : ℂ) + I * t)).re ≤
        -1 / (σ - β) + B * (1 + Real.log (|t| + 5)) := by
  rcases exists_regularized_logDeriv_riemannZeta_log_bound with
    ⟨B, hB, hregular⟩
  refine ⟨B, hB, ?_⟩
  intro σ β t hσ1 hσ2 ht hβ0 hβ1 hzero
  let c : ℂ := (2 : ℂ) + I * t
  let s : ℂ := (σ : ℂ) + I * t
  let rho : ℂ := (β : ℂ) + I * t
  let S : ℂ := ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
    (Metric.closedBall c (17 / 10 : ℝ)) u : ℂ) * (s - u)⁻¹
  let Rpart : ℂ := logDeriv riemannZeta s - S
  have hs : s ∈ Metric.closedBall c 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : s - c = ((σ - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s, c]
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have hrho : rho ∈ Metric.closedBall c (17 / 10 : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : rho - c = ((β - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [rho, c]
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have havoid : ∀ u : ℂ,
      u ∈ Metric.closedBall c (17 / 10 : ℝ) → u ≠ 1 := by
    intro u hu
    exact closedBall_sigma_it_ne_one_of_height_add_le
      (z := u) (σ := 2) (t := t) (R := (17 / 10 : ℝ))
      (H := |t| - (17 / 10 : ℝ)) (by simpa [c] using hu)
      (by linarith) (by linarith)
  have hs_ne : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [s, hσ1])
  have hRnorm : ‖Rpart‖ ≤ B * (1 + Real.log (|t| + 5)) := by
    simpa [Rpart, S, s, c] using hregular t ht s hs hs_ne
  have hprincipal : 1 / (σ - β) ≤ S.re := by
    have hsub : 0 < s.re - rho.re := by simp [s, rho]; linarith
    have h := one_div_le_re_finsum_riemannZeta_divisor_mul_inv
      havoid (by simp [s, hσ1]) hrho (by simpa [rho] using hzero)
      (by simp [s, rho]) hsub
    simpa [S, s, rho, c] using h
  have hdecomp : logDeriv riemannZeta s = Rpart + S := by
    dsimp [Rpart]
    ring
  have hreal : (-logDeriv riemannZeta s).re + 1 / (σ - β) ≤ ‖Rpart‖ := by
    have hnegR : -Rpart.re ≤ ‖Rpart‖ :=
      (neg_le_abs Rpart.re).trans (Complex.abs_re_le_norm Rpart)
    rw [hdecomp]
    simp only [neg_re, add_re]
    linarith
  calc
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re
        = (-logDeriv riemannZeta s).re := by
          simp [s, neg_logDeriv_riemannZeta_eq_neg_deriv_div]
    _ ≤ ‖Rpart‖ - 1 / (σ - β) := by linarith
    _ ≤ B * (1 + Real.log (|t| + 5)) - 1 / (σ - β) :=
      sub_le_sub_right hRnorm _
    _ = -1 / (σ - β) + B * (1 + Real.log (|t| + 5)) := by ring

/-- Uniform real-part boundary-strip estimate.  The local zero principal
parts have the favorable sign, so the all-divisor regular-part norm bound
controls `Re(-zeta'/zeta)` without requiring a zero-free disk. -/
theorem exists_re_neg_deriv_div_riemannZeta_boundary_log_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ σ t : ℝ,
      1 ≤ σ → σ ≤ 2 → 4 ≤ |t| →
      (-deriv riemannZeta ((σ : ℂ) + I * t) /
          riemannZeta ((σ : ℂ) + I * t)).re ≤
        B * (1 + Real.log (|t| + 5)) := by
  rcases exists_regularized_logDeriv_riemannZeta_log_bound with
    ⟨B, hB, hregular⟩
  refine ⟨B, hB, ?_⟩
  intro σ t hσ1 hσ2 ht
  let c : ℂ := (2 : ℂ) + I * t
  let s : ℂ := (σ : ℂ) + I * t
  let S : ℂ := ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
    (Metric.closedBall c (17 / 10 : ℝ)) u : ℂ) * (s - u)⁻¹
  let Rpart : ℂ := logDeriv riemannZeta s - S
  have hs : s ∈ Metric.closedBall c 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : s - c = ((σ - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s, c]
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have havoid : ∀ u : ℂ,
      u ∈ Metric.closedBall c (17 / 10 : ℝ) → u ≠ 1 := by
    intro u hu
    exact closedBall_sigma_it_ne_one_of_height_add_le
      (z := u) (σ := 2) (t := t) (R := (17 / 10 : ℝ))
      (H := |t| - (17 / 10 : ℝ)) (by simpa [c] using hu)
      (by linarith) (by linarith)
  have hs_ne : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [s, hσ1])
  have hRnorm : ‖Rpart‖ ≤ B * (1 + Real.log (|t| + 5)) := by
    simpa [Rpart, S, s, c] using hregular t ht s hs hs_ne
  have hprincipal : 0 ≤ S.re := by
    simpa [S] using re_finsum_riemannZeta_divisor_mul_inv_nonneg
      havoid (by simp [s, hσ1])
  have hdecomp : logDeriv riemannZeta s = Rpart + S := by
    dsimp [Rpart]
    ring
  have hreal : (-logDeriv riemannZeta s).re ≤ ‖Rpart‖ := by
    have hnegR : -Rpart.re ≤ ‖Rpart‖ :=
      (neg_le_abs Rpart.re).trans (Complex.abs_re_le_norm Rpart)
    rw [hdecomp]
    simp only [neg_re, add_re]
    linarith
  calc
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re
        = (-logDeriv riemannZeta s).re := by
          simp [s, neg_logDeriv_riemannZeta_eq_neg_deriv_div]
    _ ≤ ‖Rpart‖ := hreal
    _ ≤ B * (1 + Real.log (|t| + 5)) := hRnorm

lemma one_add_log_abs_add_five_le_three_log_abs {t : ℝ} (ht : 4 ≤ |t|) :
    1 + Real.log (|t| + 5) ≤ 3 * Real.log |t| := by
  have htpos : 0 < |t| := by linarith
  have hargpos : 0 < |t| + 5 := by positivity
  have hsq : |t| + 5 ≤ |t| ^ 2 := by
    nlinarith [sq_nonneg (|t| - 4)]
  have hlogsq : Real.log (|t| + 5) ≤ Real.log (|t| ^ 2) :=
    Real.log_le_log hargpos hsq
  have hlogpow : Real.log (|t| ^ 2) = 2 * Real.log |t| := by
    rw [Real.log_pow]
    norm_num
  rw [hlogpow] at hlogsq
  have hone : 1 ≤ Real.log |t| :=
    (log_abs_gt_one_of_three_le (by linarith)).le
  linarith

/-- Exact `C log |t|` form of the uniform real-part boundary-strip estimate. -/
theorem exists_ReNegDerivDivVerticalLogBound :
    ∃ C T0 : ℝ, ReNegDerivDivVerticalLogBound C T0 := by
  rcases exists_re_neg_deriv_div_riemannZeta_boundary_log_bound with
    ⟨B, hB, hbound⟩
  refine ⟨3 * B, 4, mul_nonneg (by norm_num) hB, by norm_num, ?_⟩
  intro σ t hσ1 hσ2 ht
  have hsafe := hbound σ t hσ1 hσ2 ht
  calc
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re
        ≤ B * (1 + Real.log (|t| + 5)) := hsafe
    _ ≤ B * (3 * Real.log |t|) :=
      mul_le_mul_of_nonneg_left (one_add_log_abs_add_five_le_three_log_abs ht) hB
    _ = (3 * B) * Real.log |t| := by ring

/-- Exact logarithmic zero-repulsion estimate for candidate zeros lying in
the fixed Jensen disk. -/
theorem exists_re_neg_deriv_div_riemannZeta_le_neg_inv_add_log_abs_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ β t : ℝ,
      1 ≤ σ → σ ≤ 2 → 4 ≤ |t| → (3 / 10 : ℝ) ≤ β → β < 1 →
      riemannZeta ((β : ℂ) + I * t) = 0 →
      (-deriv riemannZeta ((σ : ℂ) + I * t) /
          riemannZeta ((σ : ℂ) + I * t)).re ≤
        -1 / (σ - β) + C * Real.log |t| := by
  rcases exists_re_neg_deriv_div_riemannZeta_le_neg_inv_add_log_bound with
    ⟨B, hB, hbound⟩
  refine ⟨3 * B, mul_nonneg (by norm_num) hB, ?_⟩
  intro σ β t hσ1 hσ2 ht hβ0 hβ1 hzero
  have hsafe := hbound σ β t hσ1 hσ2 ht hβ0 hβ1 hzero
  calc
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re
        ≤ -1 / (σ - β) + B * (1 + Real.log (|t| + 5)) := hsafe
    _ ≤ -1 / (σ - β) + B * (3 * Real.log |t|) :=
      by
        simpa [add_comm] using
          add_le_add_left
            (mul_le_mul_of_nonneg_left
              (one_add_log_abs_add_five_le_three_log_abs ht) hB)
            (-1 / (σ - β))
    _ = -1 / (σ - β) + (3 * B) * Real.log |t| := by ring

/-- The classical de la Vallee Poussin zero-free region.  The proof combines
the uniform all-divisor regular-part estimate, candidate-principal-part
separation, the boundary-strip real-part bound at heights `t` and `2t`, and
the already formalized 3-4-1 closure. -/
theorem classical_zero_free_region_proved : classical_zero_free_region := by
  rcases exists_re_neg_deriv_div_riemannZeta_le_neg_inv_add_log_abs_bound with
    ⟨Czero, hCzero, hzero⟩
  rcases exists_ReNegDerivDivVerticalLogBound with
    ⟨Cvertical, Tvertical, hvertical⟩
  rcases hvertical with ⟨hCvertical, hTvertical, hvertical⟩
  let T0 : ℝ := max 4 Tvertical
  let B : ℝ := max Czero (max (Cvertical + 2) (2 * Cvertical))
  have hT0 : 2 ≤ T0 := by
    exact (by norm_num : (2 : ℝ) ≤ 4).trans (le_max_left _ _)
  have hB : 0 ≤ B := hCzero.trans (le_max_left _ _)
  apply classical_zero_free_region_of_sigma_log_shift_estimates_same_const
    B T0 hB hT0
  · intro a c β t ha _hc ha_log ht hβ1 _hβlower hsub hζ
    have ht4 : 4 ≤ |t| := (le_max_left 4 Tvertical).trans ht
    have htvertical : Tvertical ≤ |t| :=
      (le_max_right 4 Tvertical).trans ht
    let σ : ℝ := 1 + a / Real.log |t|
    have hσ1 : 1 ≤ σ :=
      (sigmaOf_log_gt_one hT0 ha ht).le
    have hσ2 : σ ≤ 2 := sigmaOf_log_le_two hT0 ha_log ht
    by_cases hβ : (3 / 10 : ℝ) ≤ β
    · have hcand := hzero σ β t hσ1 hσ2 ht4 hβ hβ1 hζ
      have hlog_nonneg : 0 ≤ Real.log |t| :=
        (log_abs_pos_of_two_le (hT0.trans ht)).le
      have hCB : Czero ≤ B := le_max_left _ _
      calc
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re
            ≤ -1 / (σ - β) + Czero * Real.log |t| := hcand
        _ ≤ -1 / (σ - β) + B * Real.log |t| :=
          by
            simpa [add_comm] using
              add_le_add_left
                (mul_le_mul_of_nonneg_right hCB hlog_nonneg)
                (-1 / (σ - β))
    · have hbase := hvertical σ t hσ1 hσ2 htvertical
      have hlog_one : 1 ≤ Real.log |t| :=
        (log_abs_gt_one_of_three_le (by linarith [ht4])).le
      have hinv : 1 / (σ - β) ≤ 2 * Real.log |t| := by
        have hden : 0 < σ - β := by simpa [σ] using hsub
        have hone : 1 / (σ - β) ≤ 2 := by
          apply (div_le_iff₀ hden).2
          have hβlt : β < 3 / 10 := lt_of_not_ge hβ
          nlinarith
        linarith
      have hCsmall : Cvertical + 2 ≤ B :=
        (le_max_left (Cvertical + 2) (2 * Cvertical)).trans
          (le_max_right Czero _)
      have hcoef : (Cvertical + 2) * Real.log |t| ≤ B * Real.log |t| :=
        mul_le_mul_of_nonneg_right hCsmall
          (zero_le_one.trans hlog_one)
      calc
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re
            ≤ Cvertical * Real.log |t| := hbase
        _ = (Cvertical + 2) * Real.log |t| - 2 * Real.log |t| := by ring
        _ ≤ (Cvertical + 2) * Real.log |t| - 1 / (σ - β) :=
          sub_le_sub_left hinv _
        _ = -1 / (σ - β) + (Cvertical + 2) * Real.log |t| := by ring
        _ ≤ -1 / (σ - β) + B * Real.log |t| :=
          by
            simpa [add_comm] using
              add_le_add_left hcoef (-1 / (σ - β))
  · intro a t ha ha_log ht
    have htvertical : Tvertical ≤ |t| :=
      (le_max_right 4 Tvertical).trans ht
    let σ : ℝ := 1 + a / Real.log |t|
    have hσ1 : 1 ≤ σ := (sigmaOf_log_gt_one hT0 ha ht).le
    have hσ2 : σ ≤ 2 := sigmaOf_log_le_two hT0 ha_log ht
    have hheight2 : Tvertical ≤ |2 * t| := by
      rw [abs_mul]
      norm_num
      nlinarith [abs_nonneg t]
    have hbase := hvertical σ (2 * t) hσ1 hσ2 hheight2
    have hlog2 : Real.log |2 * t| ≤ 2 * Real.log |t| :=
      log_abs_two_mul_le_two_log_abs (hT0.trans ht)
    have hlog_nonneg : 0 ≤ Real.log |t| :=
      (log_abs_pos_of_two_le (hT0.trans ht)).le
    have hCtwo : 2 * Cvertical ≤ B :=
      (le_max_right (Cvertical + 2) (2 * Cvertical)).trans
        (le_max_right Czero _)
    calc
      (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re
          ≤ Cvertical * Real.log |2 * t| := by
            convert hbase using 1 <;> push_cast <;> ring
      _ ≤ Cvertical * (2 * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hlog2 hCvertical
      _ = (2 * Cvertical) * Real.log |t| := by ring
      _ ≤ B * Real.log |t| :=
        mul_le_mul_of_nonneg_right hCtwo hlog_nonneg

end ZeroFreeRegion
