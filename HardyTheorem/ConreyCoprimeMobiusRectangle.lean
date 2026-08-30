import HardyTheorem.ConreyCoprimeMobiusResidue
import MathlibAux.RectangleCauchyDerivative

open Complex Set Metric
open scoped BigOperators Interval

namespace HardyTheorem

/-! Actual coprime Möbius Perron residues on local rectangles. The common
disk is constructed from zeta, not assumed. The high contour and its error
bounds still require the global zero-free-strip assembly. -/

/-- One radius works for all moduli and every rectangle in the local
regularization disk whose interior contains both `0` and `-alpha`.
The latter condition keeps the raw Euler expression off its removable point
on the boundary. Zero shift is allowed. -/
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
  have hW : AnalyticOnNhd ℂ (conreyCoprimeMobiusRegularized m) (closedBall 0 r) :=
    (hlocal m).1
  have hzmem : (0 : ℂ) ∈ ([[a, b]] ×ℂ [[c, d]]) := by
    rw [mem_reProdIm, uIcc_of_le (ha.trans hb).le, uIcc_of_le (hc.trans hd).le]
    exact ⟨⟨ha.le, hb.le⟩, hc.le, hd.le⟩
  have hαr : ‖α‖ ≤ r := by simpa using hshift 0 hzmem
  have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  let f : ℂ → ℂ := fun w => (X : ℂ) ^ w * conreyCoprimeMobiusRegularized m (α + w)
  have hf : AnalyticOnNhd ℂ f ([[a, b]] ×ℂ [[c, d]]) := by
    intro w hw
    exact ((differentiable_id.const_cpow (Or.inl hX0)).analyticAt w).mul
      ((hW (α + w) (by simpa using hshift w hw)).comp
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
      have hlo := (abs_le.mp (Complex.abs_re_le_norm (α + w))).1
      have hn := hshift w hw
      simp only [add_re] at hlo
      simp only [add_re, one_re]
      linarith
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
      simpa using (hW α (by simpa using hαr)).differentiableAt.hasDerivAt
    simpa [f, ← Complex.ofReal_log hX.le] using (hx.fun_mul hw).deriv
  rw [hboundary, MathlibAux.boundaryRectIntegral_div_sq hf.differentiableOn ha hb hc hd,
    hderiv]

end HardyTheorem
