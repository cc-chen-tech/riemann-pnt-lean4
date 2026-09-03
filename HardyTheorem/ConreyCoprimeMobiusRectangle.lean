import HardyTheorem.ConreyCoprimeMobiusResidue
import MathlibAux.RectangleCauchyDerivative

open Complex Set Metric
open scoped BigOperators Interval

namespace HardyTheorem

/-! A common actual coprime Möbius contour calculation and its local-disk
corollary. The disk is constructed from zeta, not assumed. The high-rectangle
caller is in `ConreyCoprimeMobiusHighRectangle`; path norm bounds remain separate. -/

/-- The common contour calculation, with actual regularization fixed.
Local and high-rectangle callers must prove its analytic hypotheses. -/
theorem conrey_coprime_mobius_rectangle_residue_of_analytic
    (m : ℕ) (α : ℂ) {X a b c d : ℝ} (hX : 0 < X)
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d)
    (hαa : a < (-α).re) (hαb : (-α).re < b)
    (hαc : c < (-α).im) (hαd : (-α).im < d)
    (hW : ∀ w ∈ ([[a, b]] ×ℂ [[c, d]]),
      AnalyticAt ℂ (conreyCoprimeMobiusRegularized m) (α + w))
    (hre : ∀ w ∈ ([[a, b]] ×ℂ [[c, d]]), -1 < (α + w).re) :
      MathlibAux.boundaryRectIntegral (fun w : ℂ => (X : ℂ) ^ w *
        (riemannZeta (1 + α + w) *
          ∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + w))))⁻¹ *
        (1 / w ^ 2)) a b c d =
        (2 * Real.pi * I) *
          ((Real.log X : ℂ) * conreyCoprimeMobiusRegularized m α +
            deriv (conreyCoprimeMobiusRegularized m) α) := by
  have hzmem : (0 : ℂ) ∈ ([[a, b]] ×ℂ [[c, d]]) := by
    rw [mem_reProdIm, uIcc_of_le (ha.trans hb).le, uIcc_of_le (hc.trans hd).le]
    exact ⟨⟨ha.le, hb.le⟩, hc.le, hd.le⟩
  have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  let f : ℂ → ℂ := fun w => (X : ℂ) ^ w * conreyCoprimeMobiusRegularized m (α + w)
  have hf : AnalyticOnNhd ℂ f ([[a, b]] ×ℂ [[c, d]]) := by
    intro w hw
    exact ((differentiable_id.const_cpow (Or.inl hX0)).analyticAt w).mul
      ((hW w hw).comp
        (analyticAt_const.add analyticAt_id))
  have hboundary : MathlibAux.boundaryRectIntegral (fun w : ℂ => (X : ℂ) ^ w *
      (riemannZeta (1 + α + w) *
        ∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + w))))⁻¹ *
      (1 / w ^ 2)) a b c d =
      MathlibAux.boundaryRectIntegral (fun w => f w / w ^ 2) a b c d := by
    apply MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
    intro w hw hnot
    have hne : α + w ≠ 0 := by
      intro heq
      have hwα : w = -α := eq_neg_of_add_eq_zero_right heq
      subst w
      exact hnot ⟨hαa, hαb, hαc, hαd⟩
    have hne1 : 1 + (α + w) ≠ 0 := by
      apply Complex.ne_zero_of_re_pos
      have h := hre w hw
      simpa only [add_re, one_re] using (show 0 < 1 + (α + w).re by linarith)
    have heq := conreyCoprimeMobiusRegularized_eq_euler m hne hne1
    simp only [f, heq, ← add_assoc, div_eq_mul_inv, one_mul]
  have hderiv : deriv f 0 =
      (Real.log X : ℂ) * conreyCoprimeMobiusRegularized m α +
        deriv (conreyCoprimeMobiusRegularized m) α := by
    have hx : HasDerivAt (fun w : ℂ => (X : ℂ) ^ w) (Complex.log (X : ℂ)) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl hX0)
    have hw : HasDerivAt (fun w : ℂ => conreyCoprimeMobiusRegularized m (α + w))
        (deriv (conreyCoprimeMobiusRegularized m) α) 0 := by
      apply HasDerivAt.comp_const_add
      simpa using (hW 0 hzmem).differentiableAt.hasDerivAt
    simpa [f, ← Complex.ofReal_log hX.le] using (hx.fun_mul hw).deriv
  rw [hboundary, MathlibAux.boundaryRectIntegral_div_sq hf.differentiableOn ha hb hc hd,
    hderiv]

/-- A common local disk, chosen before the modulus; zero shift is allowed. -/
theorem exists_conrey_coprime_mobius_rectangle_residue :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ∀ (m : ℕ) (α : ℂ)
      (X a b c d : ℝ), 0 < X →
      a < 0 → 0 < b → c < 0 → 0 < d →
      a < (-α).re → (-α).re < b → c < (-α).im → (-α).im < d →
      (∀ w ∈ ([[a, b]] ×ℂ [[c, d]]), ‖α + w‖ ≤ r) →
      MathlibAux.boundaryRectIntegral (fun w : ℂ => (X : ℂ) ^ w *
        (riemannZeta (1 + α + w) *
          ∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + w))))⁻¹ *
        (1 / w ^ 2)) a b c d =
        (2 * Real.pi * I) *
          ((Real.log X : ℂ) * conreyCoprimeMobiusRegularized m α +
            deriv (conreyCoprimeMobiusRegularized m) α) := by
  obtain ⟨r, C, hr, hr4, hC, hlocal⟩ := exists_conrey_coprime_mobius_local_residue
  refine ⟨r, hr, hr4, ?_⟩
  intro m α X a b c d hX ha hb hc hd hαa hαb hαc hαd hshift
  apply conrey_coprime_mobius_rectangle_residue_of_analytic m α hX
    ha hb hc hd hαa hαb hαc hαd
  · intro w hw
    exact (hlocal m).1 (α + w) (by simpa using hshift w hw)
  · intro w hw
    have hlo := (abs_le.mp (Complex.abs_re_le_norm (α + w))).1
    have hn := hshift w hw
    linarith

end HardyTheorem
