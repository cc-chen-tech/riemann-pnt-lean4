import HardyTheorem.FirstZetaApproximation

open Complex MeasureTheory Set

namespace HardyTheorem

/-- The elementary phase occurring in the vertical Stirling approximation to
`Gammaℝ (1 / 2 + I * t)`. -/
noncomputable def thetaModel (t : ℝ) : ℝ :=
  t / 2 * Real.log (t / (2 * Real.pi)) - t / 2 - Real.pi / 8

/-- The periodic Bernoulli remainder kernel in the first neglected term of
the logarithmic Stirling expansion at `1 / 4 + I * t / 2`. -/
noncomputable def verticalStirlingBernoulliKernel (t u : ℝ) : ℂ :=
  ((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ) /
    (((1 / 4 : ℂ) + I * t / 2 + u) ^ 2)

private lemma exists_periodizedBernoulli_two_norm_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℝ,
      ‖((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ ≤ A := by
  let f : AddCircle (1 : ℝ) → ℝ := fun x =>
    ‖((periodizedBernoulli 2 x : ℝ) : ℂ)‖
  have hf : Continuous f := by
    dsimp [f]
    exact continuous_norm.comp
      (Complex.continuous_ofReal.comp
        (periodizedBernoulli.continuous (by norm_num : 2 ≠ 1)))
  obtain ⟨M, hM⟩ := bddAbove_def.mp
    (isCompact_univ.bddAbove_image hf.continuousOn)
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro u
  exact (hM _ ⟨(u : AddCircle (1 : ℝ)), Set.mem_univ _, rfl⟩).trans
    (le_max_left _ _)

private lemma norm_verticalStirlingBernoulliKernel_le
    {A t u : ℝ} (hA : 0 ≤ A) (ht : 0 < t) (htu : t ≤ u)
    (hbern :
      ‖((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ ≤ A) :
    ‖verticalStirlingBernoulliKernel t u‖ ≤ A * u ^ (-2 : ℝ) := by
  have hu : 0 < u := ht.trans_le htu
  let z : ℂ := (1 / 4 : ℂ) + I * t / 2 + u
  have hre : u ≤ z.re := by
    dsimp [z]
    norm_num
  have huz : u ≤ ‖z‖ :=
    hre.trans (le_abs_self z.re |>.trans (Complex.abs_re_le_norm z))
  have hzpos : 0 < ‖z‖ := hu.trans_le huz
  rw [verticalStirlingBernoulliKernel, norm_div, norm_pow]
  change
    ‖((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ / ‖z‖ ^ 2 ≤
      A * u ^ (-2 : ℝ)
  rw [Real.rpow_neg (le_of_lt hu), Real.rpow_two]
  have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
  have hz2 : 0 < ‖z‖ ^ 2 := sq_pos_of_pos hzpos
  have hsq : u ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  calc
    _ ≤ A / ‖z‖ ^ 2 := div_le_div_of_nonneg_right hbern hz2.le
    _ ≤ A / u ^ 2 := div_le_div_of_nonneg_left hA hu2 hsq
    _ = A * (u ^ 2)⁻¹ := by rw [div_eq_mul_inv]

private lemma norm_verticalStirlingBernoulliKernel_le_low
    {A t u : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    (hbern :
      ‖((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ ≤ A) :
    ‖verticalStirlingBernoulliKernel t u‖ ≤ 4 * A / t ^ 2 := by
  let z : ℂ := (1 / 4 : ℂ) + I * t / 2 + u
  have him_eq : z.im = t / 2 := by
    dsimp [z]
    simp
  have him : t / 2 ≤ ‖z‖ := by
    rw [← him_eq]
    exact (le_abs_self z.im).trans (Complex.abs_im_le_norm z)
  have him0 : 0 < t / 2 := half_pos ht
  have hz0 : 0 < ‖z‖ := him0.trans_le him
  have hsq : (t / 2) ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  rw [verticalStirlingBernoulliKernel, norm_div, norm_pow]
  change
    ‖((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ / ‖z‖ ^ 2 ≤
      4 * A / t ^ 2
  calc
    _ ≤ A / ‖z‖ ^ 2 :=
      div_le_div_of_nonneg_right hbern (sq_nonneg _)
    _ ≤ A / (t / 2) ^ 2 :=
      div_le_div_of_nonneg_left hA (sq_pos_of_pos him0) hsq
    _ = 4 * A / t ^ 2 := by field_simp [ht.ne']; ring

/-- The high tail of the periodic-Bernoulli remainder in vertical Stirling is
`O(1/t)`.  This is the quantitative part of the Euler-summation remainder;
the omitted compact interval is handled separately in the full formula. -/
theorem exists_norm_integral_Ioi_verticalStirlingBernoulliKernel_le_inv :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖∫ u in Set.Ioi t, verticalStirlingBernoulliKernel t u‖ ≤ C / t := by
  obtain ⟨A, hA, hbern⟩ := exists_periodizedBernoulli_two_norm_bound
  refine ⟨A, hA, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let g : ℝ → ℝ := fun u => A * u ^ (-2 : ℝ)
  have hg : IntegrableOn g (Set.Ioi t) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ht0).const_mul A
  have hpoint : ∀ᵐ u ∂volume.restrict (Set.Ioi t),
      ‖verticalStirlingBernoulliKernel t u‖ ≤ g u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_verticalStirlingBernoulliKernel_le hA ht0 hu.le (hbern u)
  calc
    ‖∫ u in Set.Ioi t, verticalStirlingBernoulliKernel t u‖ ≤
        ∫ u in Set.Ioi t, g u :=
      MeasureTheory.norm_integral_le_of_norm_le hg hpoint
    _ = A * (∫ u in Set.Ioi t, u ^ (-2 : ℝ)) :=
      by dsimp [g]; rw [MeasureTheory.integral_const_mul]
    _ = A / t := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) ht0]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      field_simp [ht0.ne']

/-- The complete periodic-Bernoulli remainder integral in the vertical
logarithmic Stirling formula is `O(1/t)`. -/
theorem exists_norm_integral_Ioi_zero_verticalStirlingBernoulliKernel_le_inv :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖∫ u in Set.Ioi (0 : ℝ), verticalStirlingBernoulliKernel t u‖ ≤ C / t := by
  obtain ⟨A, hA, hbern⟩ := exists_periodizedBernoulli_two_norm_bound
  refine ⟨5 * A, mul_nonneg (by norm_num) hA, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let F : ℝ → ℂ := verticalStirlingBernoulliKernel t
  let g : ℝ → ℝ := fun u => A * u ^ (-2 : ℝ)
  have hFcont : Continuous F := by
    dsimp [F, verticalStirlingBernoulliKernel]
    apply Continuous.div
    · exact Complex.continuous_ofReal.comp
        ((periodizedBernoulli.continuous (by norm_num : 2 ≠ 1)).comp
          continuous_quotient_mk')
    · fun_prop
    · intro u
      apply pow_ne_zero
      intro hzero
      have him := congrArg Complex.im hzero
      simp at him
      linarith
  have hinterval : IntervalIntegrable F volume 0 t := hFcont.intervalIntegrable _ _
  have hg : IntegrableOn g (Set.Ioi t) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ht0).const_mul A
  have hpoint : ∀ᵐ u ∂volume.restrict (Set.Ioi t), ‖F u‖ ≤ g u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_verticalStirlingBernoulliKernel_le hA ht0 hu.le (hbern u)
  have hFtail : IntegrableOn F (Set.Ioi t) := by
    change Integrable F (volume.restrict (Set.Ioi t))
    change Integrable g (volume.restrict (Set.Ioi t)) at hg
    exact hg.mono' hFcont.aestronglyMeasurable.restrict hpoint
  have htail : ‖∫ u in Set.Ioi t, F u‖ ≤ A / t := by
    calc
      ‖∫ u in Set.Ioi t, F u‖ ≤ ∫ u in Set.Ioi t, g u :=
        MeasureTheory.norm_integral_le_of_norm_le hg hpoint
      _ = A * (∫ u in Set.Ioi t, u ^ (-2 : ℝ)) := by
        dsimp [g]
        rw [MeasureTheory.integral_const_mul]
      _ = A / t := by
        rw [integral_Ioi_rpow_of_lt (by norm_num) ht0]
        rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
        field_simp [ht0.ne']
  have hlow : ‖∫ u in (0 : ℝ)..t, F u‖ ≤ 4 * A / t := by
    have hconst := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := F) (a := 0) (b := t) (C := 4 * A / t ^ 2)
      (fun u _hu => norm_verticalStirlingBernoulliKernel_le_low hA ht0 (hbern u))
    rw [sub_zero, abs_of_pos ht0] at hconst
    calc
      _ ≤ (4 * A / t ^ 2) * t := hconst
      _ = 4 * A / t := by field_simp [ht0.ne']
  have hsplit :
      (∫ u in (0 : ℝ)..t, F u) + ∫ u in Set.Ioi t, F u =
        ∫ u in Set.Ioi (0 : ℝ), F u :=
    intervalIntegral.integral_interval_add_Ioi' hinterval hFtail
  rw [← hsplit]
  calc
    ‖(∫ u in (0 : ℝ)..t, F u) + ∫ u in Set.Ioi t, F u‖ ≤
        ‖∫ u in (0 : ℝ)..t, F u‖ + ‖∫ u in Set.Ioi t, F u‖ := norm_add_le _ _
    _ ≤ 4 * A / t + A / t := add_le_add hlow htail
    _ = 5 * A / t := by ring

end HardyTheorem
