import PrimeNumberTheorem.MWKFCubicAFECompletedTime

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem.MWKFCubic

/-!
# A depth-independent two-endpoint product majorant

The small-product exponent is -1/2, from the actual residue-one contour
shift. The large-product exponent is -X-1/2. Their pullback retains the
absolute quadratic Jacobian and requires a nonzero shift. There is no
completion-depth factor and no claimed uniform bound over all shifts.
-/

noncomputable def cubicAFEEndpointPower (X P : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun P : ℝ ↦ P ^ (-1 / 2 : ℝ)) P +
    (Ioi (1 : ℝ)).indicator (fun P : ℝ ↦ P ^ (-X - 1 / 2)) P

theorem cubicAFEEndpointPower_nonneg (X P : ℝ) : 0 ≤ cubicAFEEndpointPower X P := by
  unfold cubicAFEEndpointPower
  apply add_nonneg
  · by_cases hp : P ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem hp]
      exact Real.rpow_nonneg hp.1.le _
    · rw [indicator_of_notMem hp]
  · by_cases hp : P ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem hp]
      exact Real.rpow_nonneg (zero_lt_one.trans hp).le _
    · rw [indicator_of_notMem hp]

theorem measurable_cubicAFEEndpointPower (X : ℝ) : Measurable (cubicAFEEndpointPower X) :=
  ((measurable_id.pow measurable_const).indicator measurableSet_Ioc).add
    ((measurable_id.pow measurable_const).indicator measurableSet_Ioi)

theorem cubicAFEEndpointPower_small (X : ℝ) {P : ℝ} (hP : 0 < P) (hP1 : P ≤ 1) :
    cubicAFEEndpointPower X P = P ^ (-1 / 2 : ℝ) := by
  rw [cubicAFEEndpointPower, indicator_of_mem (show P ∈ Ioc (0 : ℝ) 1 from ⟨hP, hP1⟩),
    indicator_of_notMem (show P ∉ Ioi (1 : ℝ) from not_lt.mpr hP1), add_zero]

theorem cubicAFEEndpointPower_large (X : ℝ) {P : ℝ} (hP : 1 < P) :
    cubicAFEEndpointPower X P = P ^ (-X - 1 / 2) := by
  rw [cubicAFEEndpointPower,
    indicator_of_notMem (show P ∉ Ioc (0 : ℝ) 1 from fun hp ↦ (not_le.mpr hP) hp.2),
    indicator_of_mem (show P ∈ Ioi (1 : ℝ) from hP), zero_add]

theorem integrable_cubicAFEEndpointPower {X : ℝ} (hX : 1 / 2 < X) :
    Integrable (cubicAFEEndpointPower X) := by
  have hsmall : IntegrableOn (fun P : ℝ ↦ P ^ (-1 / 2 : ℝ)) (Ioc (0 : ℝ) 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by norm_num)
  exact (hsmall.integrable_indicator measurableSet_Ioc).add
    ((integrableOn_Ioi_rpow_of_lt (by linarith : -X - 1 / 2 < -1) zero_lt_one).integrable_indicator
      measurableSet_Ioi)

theorem norm_cubicAFEWeightedProduct_le_endpointPower (t : ℝ) {X P : ℝ}
    (hX : 1 / 2 < X) (hP : 0 < P) :
    ‖((P ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * cubicAFERealProductWeightVertical t X P‖ ≤
      (1 + cubicAFEWeightNormMass t (-1 / 4) + cubicAFEWeightNormMass t X) * cubicAFEEndpointPower X P := by
  rw [norm_mul, Complex.norm_of_nonneg (Real.rpow_nonneg hP.le _)]
  by_cases hp1 : P ≤ 1
  · rw [cubicAFEEndpointPower_small X hP hp1]
    have hb := norm_cubicAFERealProductWeightVertical_le_of_le_one t (X := X) (by linarith) hP hp1
    have hc : 1 + cubicAFEWeightNormMass t (-1 / 4) ≤
        1 + cubicAFEWeightNormMass t (-1 / 4) + cubicAFEWeightNormMass t X :=
      le_add_of_nonneg_right (cubicAFEWeightNormMass_nonneg t X)
    exact (mul_le_mul_of_nonneg_left (hb.trans hc) (Real.rpow_nonneg hP.le _)).trans_eq (by ring)
  · rw [cubicAFEEndpointPower_large X (lt_of_not_ge hp1)]
    calc
      _ ≤ P ^ (-1 / 2 : ℝ) * (cubicAFEWeightNormMass t X * P ^ (-X)) :=
        mul_le_mul_of_nonneg_left (norm_cubicAFERealProductWeightVertical_le t X hP)
          (Real.rpow_nonneg hP.le _)
      _ = cubicAFEWeightNormMass t X * P ^ (-X - 1 / 2) := by
        rw [show -X - 1 / 2 = (-1 / 2 : ℝ) + -X by ring, Real.rpow_add hP]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by linarith [cubicAFEWeightNormMass_nonneg t (-1 / 4)]) (Real.rpow_nonneg hP.le _)

/-- The two-endpoint majorant is integrable on the entire two-positive-index
domain. The inverse Jacobian factor is s/|delta|; it is not discarded. -/
theorem integrableOn_cubicAFEEndpointPower_quadratic {X r s δ : ℝ}
    (hX : 1 / 2 < X) (hr : 0 < r) (hs : 0 < s) (hδ : δ ≠ 0) :
    IntegrableOn (fun x : ℝ ↦ cubicAFEEndpointPower X (x * (δ + r * x) / s))
      {x : ℝ | 0 < x ∧ 0 < δ + r * x} := by
  let D : Set ℝ := {x : ℝ | 0 < x ∧ 0 < δ + r * x}
  let Q : ℝ → ℝ := fun x ↦ x * (δ + r * x) / s
  let Q' : ℝ → ℝ := fun x ↦ (δ + 2 * r * x) / s
  let F := cubicAFEEndpointPower X
  let c : ℝ := |δ| / s
  have hc : 0 < c := div_pos (abs_pos.mpr hδ) hs
  have hD : MeasurableSet D :=
    ((isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt continuous_const (continuous_const.add (continuous_const.mul continuous_id)))).measurableSet
  have hd (x : ℝ) : HasDerivAt Q (Q' x) x := by
    dsimp [Q, Q']
    exact (((hasDerivAt_id x).mul
      (((hasDerivAt_id x).const_mul r).const_add δ)).div_const s).congr_deriv
      (by simp only [id_eq]; ring)
  have hQ : Continuous Q := by dsimp [Q]; fun_prop
  have hmin (x : ℝ) (hx : x ∈ D) : c ≤ |Q' x| := by
    have hnum : |δ| ≤ δ + 2 * r * x := by
      rcases le_total 0 δ with hpos | hneg
      · rw [abs_of_nonneg hpos]
        nlinarith [mul_pos hr hx.1]
      · rw [abs_of_nonpos hneg]
        linarith [hx.2]
    exact (div_le_div_of_nonneg_right hnum hs.le).trans (le_abs_self _)
  have hinj : InjOn Q D := by
    intro x hx y hy hxy
    have heq : x * (δ + r * x) = y * (δ + r * y) := by
      have hh := congrArg (fun u : ℝ ↦ u * s) hxy
      simpa only [Q, div_mul_cancel₀ _ hs.ne'] using hh
    have hf : (x - y) * (δ + r * (x + y)) = 0 := by nlinarith [heq]
    have hp : 0 < δ + r * (x + y) := by nlinarith [hx.2, mul_pos hr hy.1]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hp.ne')
  have hi : IntegrableOn (fun x ↦ |Q' x| • F (Q x)) D :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul hD
      (fun x _ ↦ (hd x).hasDerivWithinAt) hinj F).mp (integrable_cubicAFEEndpointPower hX).integrableOn
  have hm : Measurable (fun x ↦ F (Q x)) := (measurable_cubicAFEEndpointPower X).comp hQ.measurable
  apply (hi.norm.const_mul c⁻¹).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hD] with x hx
  change ‖F (Q x)‖ ≤ c⁻¹ * ‖|Q' x| • F (Q x)‖
  simp only [norm_smul, Real.norm_eq_abs, abs_abs]
  calc
    _ = c⁻¹ * (c * ‖F (Q x)‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, Real.norm_eq_abs]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hmin x hx) (norm_nonneg _)) (inv_nonneg.mpr hc.le)

end PrimeNumberTheorem.MWKFCubic
