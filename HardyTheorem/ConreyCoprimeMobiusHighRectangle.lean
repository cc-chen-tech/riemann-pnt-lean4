import HardyTheorem.ConreyCoprimeMobiusRectangle
import HardyTheorem.ConreyReciprocalZetaStrip
import HardyTheorem.SelbergS12StripBounded

open Complex Set Metric Filter
open scoped BigOperators Interval Topology

namespace HardyTheorem

/-! Compact low-height thickening and the actual high zero-free strip are
combined before shifting the Perron contour. No analytic or nonvanishing
surrogate is supplied by the caller. This does not estimate the path errors. -/

private theorem exists_conrey_poleUnit_low_strip (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ ∀ σ t : ℝ,
      |t| ≤ T → 1 - δ ≤ σ →
        ZeroFreeRegion.riemannZetaPoleUnitAtOne ((σ : ℂ) + I * t) ≠ 0 := by
  let good : Set ℂ := {s | 0 < s.re ∧ ZeroFreeRegion.riemannZetaPoleUnitAtOne s ≠ 0}
  have hopen : IsOpen good := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have ha := ZeroFreeRegion.analyticOnNhd_riemannZetaPoleUnitAtOne_re_gt
      (θ := 0) le_rfl s hs.1
    exact Filter.inter_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs.1)
      (ha.continuousAt.eventually_ne hs.2)
  let segment : Set ℂ := (fun t : ℝ => (1 : ℂ) + I * t) '' Icc (-T) T
  have hcompact : IsCompact segment := isCompact_Icc.image (by fun_prop)
  have hsubset : segment ⊆ good := by
    rintro s ⟨t, _, rfl⟩
    refine ⟨by simp, riemannZetaPoleUnitAtOne_ne_zero_of_one_le_re ?_⟩
    simp
  obtain ⟨ε, hε, hthick⟩ := hcompact.exists_thickening_subset_open hopen hsubset
  let δ := min (ε / 2) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  refine ⟨δ, hδ, min_le_right _ _, ?_⟩
  intro σ t ht hσ
  by_cases hright : 1 ≤ σ
  · exact riemannZetaPoleUnitAtOne_ne_zero_of_one_le_re (by simpa using hright)
  · have hdist : dist ((σ : ℂ) + I * t) ((1 : ℂ) + I * t) < ε := by
      rw [dist_eq_norm, show (σ : ℂ) + I * t - (1 + I * t) = ((σ - 1 : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      have := min_le_left (ε / 2) (1 / 4 : ℝ)
      change δ ≤ ε / 2 at this
      linarith
    exact (hthick (mem_thickening_iff.mpr
      ⟨1 + I * t, ⟨t, abs_le.mp ht, rfl⟩, hdist⟩)).2

/-- Uniform actual analyticity on arbitrarily high rectangles crossing the
one-line. The width constant is chosen before both height and modulus. -/
theorem exists_conrey_coprime_mobius_analytic_rectangles :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 4 ∧ ∀ (K : ℝ) (m : ℕ) (z : ℂ),
      2 ≤ K → -(κ / (1 + Real.log (K + 2))) ≤ z.re → z.re ≤ 1 → |z.im| ≤ K →
      ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + z) ≠ 0 ∧
        AnalyticAt ℂ (conreyCoprimeMobiusRegularized m) z := by
  obtain ⟨c, T, hc, hc1, hT, hhigh⟩ := exists_conrey_reciprocal_zeta_quarterPower_strip
  obtain ⟨δ, hδ, hδ4, hlow⟩ := exists_conrey_poleUnit_low_strip T
  let κ := min c δ
  have hκ : 0 < κ := lt_min hc hδ
  have hκδ : κ ≤ δ := min_le_right _ _
  have hκc : κ ≤ c := min_le_left _ _
  refine ⟨κ, hκ, hκδ.trans hδ4, ?_⟩
  intro K m z hK hz hz1 ht
  have hlog : 0 < Real.log (K + 2) := Real.log_pos (by linarith)
  have hden : 0 < 1 + Real.log (K + 2) := by linarith
  have hsmall : κ / (1 + Real.log (K + 2)) ≤ δ :=
    (div_le_self hκ.le (by linarith)).trans hκδ
  have hzre : -1 < z.re := by linarith
  have hsre : 0 < (1 + z).re := by simpa only [add_re, one_re] using
    (show 0 < 1 + z.re by linarith)
  have heq : (((1 + z.re : ℝ) : ℂ) + I * z.im) = 1 + z := by
    apply Complex.ext <;> simp
  have hunit : ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + z) ≠ 0 := by
    by_cases hthi : T ≤ |z.im|
    · have ht2 : 2 ≤ |z.im| := hT.trans hthi
      have hlogt : 0 < Real.log |z.im| := Real.log_pos (by linarith)
      have hlogle : Real.log |z.im| ≤ 1 + Real.log (K + 2) := by
        have h := Real.log_le_log (by linarith : 0 < |z.im|) (by linarith : |z.im| ≤ K + 2)
        linarith
      have hwidth : κ / (1 + Real.log (K + 2)) ≤ c / Real.log |z.im| :=
        (div_le_div_of_nonneg_left hκ.le hlogt hlogle).trans
          (div_le_div_of_nonneg_right hκc hlogt.le)
      have hzn := (hhigh (1 + z.re) z.im hthi (by linarith) (by linarith)).1
      rw [heq] at hzn
      have hs1 : 1 + z ≠ 1 := by
        intro h
        have hi := congrArg Complex.im h
        simp only [add_im, one_im, zero_add] at hi
        rw [hi, abs_zero] at ht2
        norm_num at ht2
      rw [ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
        (Complex.ne_zero_of_re_pos hsre) hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) hzn
    · have h := hlow (1 + z.re) z.im (le_of_not_ge hthi) (by linarith)
      rwa [heq] at h
  refine ⟨hunit, ?_⟩
  have hQ := ZeroFreeRegion.analyticOnNhd_riemannZetaPoleUnitAtOne_re_gt
    (θ := 0) le_rfl (1 + z) hsre
  exact (analyticAt_id.mul ((hQ.comp (analyticAt_const.add analyticAt_id)).inv hunit)).mul
    (analyticAt_conreyCoprimeEulerInverse m hzre)

/-- Exact actual Euler-integrand residue on the full high rectangle.
Its analyticity is proved from the native zero-free region and compactness;
the assumptions only describe the geometric widths and shift. -/
theorem exists_conrey_coprime_mobius_high_rectangle_residue :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 4 ∧
      ∀ (K : ℝ) (m : ℕ) (α : ℂ) (X b u : ℝ), 2 ≤ K → 0 < X →
        ‖α‖ < b → ‖α‖ < u →
        b + ‖α‖ ≤ κ / (1 + Real.log (K + 3)) → u + ‖α‖ ≤ 1 →
        AnalyticOnNhd ℂ (fun w => conreyCoprimeMobiusRegularized m (α + w))
          ([[-b, u]] ×ℂ [[-K, K]]) ∧
        MathlibAux.boundaryRectIntegral (fun w : ℂ => (X : ℂ) ^ w *
          (riemannZeta (1 + α + w) *
            ∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + w))))⁻¹ *
          (1 / w ^ 2)) (-b) u (-K) K =
          (2 * Real.pi * I) *
            ((Real.log X : ℂ) * conreyCoprimeMobiusRegularized m α +
              deriv (conreyCoprimeMobiusRegularized m) α) := by
  obtain ⟨κ, hκ, hκ4, hband⟩ := exists_conrey_coprime_mobius_analytic_rectangles
  refine ⟨κ, hκ, hκ4, ?_⟩
  intro K m α X b u hK hX hαb hαu hwidth hupper
  have hb : 0 < b := (norm_nonneg α).trans_lt hαb
  have hu : 0 < u := (norm_nonneg α).trans_lt hαu
  have hα1 : ‖α‖ ≤ 1 := by linarith
  have hαre := abs_le.mp (Complex.abs_re_le_norm α)
  have hαim := abs_le.mp (Complex.abs_im_le_norm α)
  have hlog : 0 < Real.log (K + 3) := Real.log_pos (by linarith)
  have hsmall : κ / (1 + Real.log (K + 3)) ≤ 1 / 4 :=
    (div_le_self hκ.le (by linarith)).trans hκ4
  have hgeom : ∀ w ∈ ([[-b, u]] ×ℂ [[-K, K]]),
      -(κ / (1 + Real.log (K + 3))) ≤ (α + w).re ∧
        (α + w).re ≤ 1 ∧ |(α + w).im| ≤ K + 1 := by
    intro w hw
    rw [mem_reProdIm, uIcc_of_le (by linarith : -b ≤ u),
      uIcc_of_le (by linarith : -K ≤ K)] at hw
    simp only [add_re, add_im]
    refine ⟨by linarith [hw.1.1], by linarith [hw.1.2], ?_⟩
    exact abs_le.mpr ⟨by linarith [hw.2.1], by linarith [hw.2.2]⟩
  have hW : ∀ w ∈ ([[-b, u]] ×ℂ [[-K, K]]),
      AnalyticAt ℂ (conreyCoprimeMobiusRegularized m) (α + w) := by
    intro w hw
    have hg := hgeom w hw
    apply (hband (K + 1) m (α + w) (by linarith) ?_ hg.2.1 hg.2.2).2
    simpa only [show K + 1 + 2 = K + 3 by ring] using hg.1
  refine ⟨fun w hw => (hW w hw).comp (analyticAt_const.add analyticAt_id), ?_⟩
  apply conrey_coprime_mobius_rectangle_residue_of_analytic m α hX
    (by linarith) hu (by linarith) (by linarith)
    (by simp only [neg_re]; linarith [hαre.2])
    (by simp only [neg_re]; linarith [hαre.1])
    (by simp only [neg_im]; linarith [hαim.2])
    (by simp only [neg_im]; linarith [hαim.1]) hW
  intro w hw
  linarith [(hgeom w hw).1]

end HardyTheorem
