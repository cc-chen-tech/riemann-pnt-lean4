import PrimeNumberTheorem.FirstOrderPerron

set_option maxHeartbeats 800000

/-!
# Translation invariance of first-order Perron truncation

The ordinary Perron integral is only conditionally convergent, so translating
its symmetric truncation is not a formal consequence of a change of variables
in an improper integral.  This file proves the needed statement directly: the
difference between a translated and an untranslated truncation is the
difference of two finite endpoint integrals, each bounded by `O(|a| / W)`.
-/

open Complex MeasureTheory Set Filter Topology

namespace PrimeNumberTheorem

private noncomputable def firstOrderPerronKernel (c u : ℝ) (w : ℝ) : ℂ :=
  Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
    ((c : ℂ) + 2 * Real.pi * w * Complex.I)

private lemma continuous_firstOrderPerronKernel
    {c u : ℝ} (hc : 0 < c) :
    Continuous (firstOrderPerronKernel c u) := by
  have hden : ∀ w : ℝ,
      (c : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
    intro w h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  unfold firstOrderPerronKernel
  exact (by fun_prop : Continuous fun w : ℝ =>
    Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u)).div₀
      (by fun_prop) hden

private lemma norm_firstOrderPerronKernel_le
    {c u w X : ℝ} (hX : 0 < X) (hw : X ≤ |w|) :
    ‖firstOrderPerronKernel c u w‖ ≤
      Real.exp (c * u) / (2 * Real.pi * X) := by
  have hsmall_pos : 0 < 2 * Real.pi * X := by positivity
  rw [firstOrderPerronKernel, norm_div, Complex.norm_exp]
  have hre :
      (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u).re = c * u := by
    simp
  rw [hre]
  have him_le : 2 * Real.pi * |w| ≤
      ‖(c : ℂ) + 2 * Real.pi * w * Complex.I‖ := by
    have hbase := abs_im_le_norm
      ((c : ℂ) + 2 * Real.pi * w * Complex.I)
    simpa [abs_mul, abs_of_pos Real.pi_pos] using hbase
  have hX_le : 2 * Real.pi * X ≤
      ‖(c : ℂ) + 2 * Real.pi * w * Complex.I‖ :=
    (mul_le_mul_of_nonneg_left hw (by positivity)).trans him_le
  exact div_le_div_of_nonneg_left (Real.exp_nonneg _) hsmall_pos hX_le

private lemma abs_ge_half_of_mem_right_tail
    {W a w : ℝ} (hW : 2 * |a| < W) (hw : w ∈ uIcc W (W + a)) :
    W / 2 ≤ |w| := by
  have hWpos : 0 < W := by linarith [abs_nonneg a]
  have hclose : |w - W| ≤ |a| := by
    simpa using abs_sub_left_of_mem_uIcc hw
  have htriangle : W ≤ |w| + |w - W| := by
    calc
      W = |W| := (abs_of_pos hWpos).symm
      _ = |w - (w - W)| := by ring_nf
      _ ≤ |w| + |w - W| := abs_sub _ _
  linarith

private lemma abs_ge_half_of_mem_left_tail
    {W a w : ℝ} (hW : 2 * |a| < W) (hw : w ∈ uIcc (-W) (-W + a)) :
    W / 2 ≤ |w| := by
  have hWpos : 0 < W := by linarith [abs_nonneg a]
  have hclose : |w - (-W)| ≤ |a| := by
    simpa using abs_sub_left_of_mem_uIcc hw
  have htriangle : W ≤ |w| + |w - (-W)| := by
    calc
      W = |-W| := by rw [abs_neg, abs_of_pos hWpos]
      _ = |w - (w - (-W))| := by ring_nf
      _ ≤ |w| + |w - (-W)| := abs_sub _ _
  linarith

private lemma translated_intervalIntegral_sub_eq_tails
    {c u W a : ℝ} (hc : 0 < c) :
    (∫ w : ℝ in (-W + a)..(W + a), firstOrderPerronKernel c u w) -
        (∫ w : ℝ in (-W)..W, firstOrderPerronKernel c u w) =
      (∫ w : ℝ in W..(W + a), firstOrderPerronKernel c u w) -
        (∫ w : ℝ in (-W)..(-W + a), firstOrderPerronKernel c u w) := by
  have hcont : Continuous (firstOrderPerronKernel c u) :=
    continuous_firstOrderPerronKernel (u := u) hc
  have hsym : IntervalIntegrable (firstOrderPerronKernel c u) volume (-W) W :=
    hcont.intervalIntegrable _ _
  have hright : IntervalIntegrable (firstOrderPerronKernel c u) volume W (W + a) :=
    hcont.intervalIntegrable _ _
  have hleft : IntervalIntegrable (firstOrderPerronKernel c u) volume (-W) (-W + a) :=
    hcont.intervalIntegrable _ _
  have htranslated :
      IntervalIntegrable (firstOrderPerronKernel c u) volume (-W + a) (W + a) :=
    hcont.intervalIntegrable _ _
  have houter₁ :
      (∫ w : ℝ in (-W)..W, firstOrderPerronKernel c u w) +
          (∫ w : ℝ in W..(W + a), firstOrderPerronKernel c u w) =
        ∫ w : ℝ in (-W)..(W + a), firstOrderPerronKernel c u w :=
    intervalIntegral.integral_add_adjacent_intervals hsym hright
  have houter₂ :
      (∫ w : ℝ in (-W)..(-W + a), firstOrderPerronKernel c u w) +
          (∫ w : ℝ in (-W + a)..(W + a), firstOrderPerronKernel c u w) =
        ∫ w : ℝ in (-W)..(W + a), firstOrderPerronKernel c u w :=
    intervalIntegral.integral_add_adjacent_intervals hleft htranslated
  have hbalance :
      (∫ w : ℝ in (-W)..(-W + a), firstOrderPerronKernel c u w) +
          (∫ w : ℝ in (-W + a)..(W + a), firstOrderPerronKernel c u w) =
        (∫ w : ℝ in (-W)..W, firstOrderPerronKernel c u w) +
          (∫ w : ℝ in W..(W + a), firstOrderPerronKernel c u w) :=
    houter₂.trans houter₁.symm
  calc
    (∫ w : ℝ in (-W + a)..(W + a), firstOrderPerronKernel c u w) -
        (∫ w : ℝ in (-W)..W, firstOrderPerronKernel c u w) =
      ((∫ w : ℝ in (-W)..(-W + a), firstOrderPerronKernel c u w) +
          (∫ w : ℝ in (-W + a)..(W + a), firstOrderPerronKernel c u w)) -
        ((∫ w : ℝ in (-W)..(-W + a), firstOrderPerronKernel c u w) +
          (∫ w : ℝ in (-W)..W, firstOrderPerronKernel c u w)) := by ring
    _ = ((∫ w : ℝ in (-W)..W, firstOrderPerronKernel c u w) +
          (∫ w : ℝ in W..(W + a), firstOrderPerronKernel c u w)) -
        ((∫ w : ℝ in (-W)..(-W + a), firstOrderPerronKernel c u w) +
          (∫ w : ℝ in (-W)..W, firstOrderPerronKernel c u w)) := by
      rw [hbalance]
    _ = (∫ w : ℝ in W..(W + a), firstOrderPerronKernel c u w) -
        (∫ w : ℝ in (-W)..(-W + a), firstOrderPerronKernel c u w) := by ring

private lemma norm_translated_intervalIntegral_sub_le
    {c u W a : ℝ} (hc : 0 < c) (hW : 2 * |a| < W) :
    ‖(∫ w : ℝ in (-W + a)..(W + a), firstOrderPerronKernel c u w) -
        (∫ w : ℝ in (-W)..W, firstOrderPerronKernel c u w)‖ ≤
      2 * (Real.exp (c * u) / (Real.pi * W) * |a|) := by
  have hWpos : 0 < W := by linarith [abs_nonneg a]
  have hhalf : 0 < W / 2 := by positivity
  have hright :
      ‖∫ w : ℝ in W..(W + a), firstOrderPerronKernel c u w‖ ≤
        Real.exp (c * u) / (Real.pi * W) * |a| := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := firstOrderPerronKernel c u)
      (C := Real.exp (c * u) / (Real.pi * W))
      (a := W) (b := W + a) (fun w hw => by
        have hkernel := norm_firstOrderPerronKernel_le
          (c := c) (u := u) hhalf
            (abs_ge_half_of_mem_right_tail hW (uIoc_subset_uIcc hw))
        convert hkernel using 1
        field_simp)
    simpa using hbound
  have hleft :
      ‖∫ w : ℝ in (-W)..(-W + a), firstOrderPerronKernel c u w‖ ≤
        Real.exp (c * u) / (Real.pi * W) * |a| := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := firstOrderPerronKernel c u)
      (C := Real.exp (c * u) / (Real.pi * W))
      (a := -W) (b := -W + a) (fun w hw => by
        have hkernel := norm_firstOrderPerronKernel_le
          (c := c) (u := u) hhalf
            (abs_ge_half_of_mem_left_tail hW (uIoc_subset_uIcc hw))
        convert hkernel using 1
        field_simp)
    simpa using hbound
  rw [translated_intervalIntegral_sub_eq_tails hc]
  calc
    ‖(∫ w : ℝ in W..(W + a), firstOrderPerronKernel c u w) -
        (∫ w : ℝ in (-W)..(-W + a), firstOrderPerronKernel c u w)‖ ≤
      ‖∫ w : ℝ in W..(W + a), firstOrderPerronKernel c u w‖ +
        ‖∫ w : ℝ in (-W)..(-W + a), firstOrderPerronKernel c u w‖ :=
      norm_sub_le _ _
    _ ≤ Real.exp (c * u) / (Real.pi * W) * |a| +
        Real.exp (c * u) / (Real.pi * W) * |a| := add_le_add hright hleft
    _ = 2 * (Real.exp (c * u) / (Real.pi * W) * |a|) := by ring

/-- Translating the symmetric truncation window by a fixed real amount does
not alter the ordinary Perron limit.  The assertion is proved at the level of
finite interval integrals, before taking the conditionally convergent limit. -/
theorem tendsto_translated_truncated_firstOrderPerronKernel_atTop
    (c : ℝ) (hc : 0 < c) (u a : ℝ) :
    Tendsto
      (fun W : ℝ => ∫ w : ℝ in (-W + a)..(W + a),
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I))
      atTop (nhds (perronHalfStep u)) := by
  let shifted : ℝ → ℂ := fun W =>
    ∫ w : ℝ in (-W + a)..(W + a), firstOrderPerronKernel c u w
  let symmetric : ℝ → ℂ := fun W =>
    ∫ w : ℝ in (-W)..W, firstOrderPerronKernel c u w
  change Tendsto shifted atTop (nhds (perronHalfStep u))
  have hdiff : Tendsto (fun W => shifted W - symmetric W) atTop (nhds 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    let C : ℝ := 2 * (Real.exp (c * u) / Real.pi * |a|)
    have hCdiv : Tendsto (fun W : ℝ => C / W) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    apply squeeze_zero' (Eventually.of_forall fun W => norm_nonneg _) _ hCdiv
    filter_upwards [eventually_gt_atTop (2 * |a|)] with W hW
    have hbound := norm_translated_intervalIntegral_sub_le
      (c := c) (u := u) hc hW
    simpa [shifted, symmetric, C, div_eq_mul_inv, mul_assoc, mul_comm,
      mul_left_comm] using hbound
  have hsym : Tendsto symmetric atTop (nhds (perronHalfStep u)) := by
    simpa [symmetric, firstOrderPerronKernel] using
      tendsto_truncated_firstOrderPerronKernel_atTop c hc u
  simpa only [sub_add_cancel, zero_add] using hdiff.add hsym

end PrimeNumberTheorem
