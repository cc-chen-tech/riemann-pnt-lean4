import PrimeNumberTheorem.LittlewoodTailLimit
import Mathlib.Analysis.SpecificLimits.Basic

/-!
The finite zero table supplies a zero-free vertical approach to the left
edge. Compactness supplies the logarithmic upper bound. Thus neither is
an extra hypothesis in the full left-boundary Littlewood inequality.
-/

open Complex Filter Set Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem.CarlsonZeroDensity

private theorem exists_positive_gap_below_finite_real_parts
    (K : Finset ℂ) {x0 critical : ℝ} (hc : x0 < critical) :
    ∃ d : ℝ, 0 < d ∧ d < critical - x0 ∧
      ∀ z ∈ K, x0 < z.re → d < z.re - x0 := by
  classical
  induction K using Finset.induction_on with
  | empty =>
      refine ⟨(critical - x0) / 2, by linarith, by linarith, ?_⟩
      simp
  | @insert z K hz ih =>
      obtain ⟨d, hd, hdc, hK⟩ := ih
      by_cases hxz : x0 < z.re
      · refine ⟨min d ((z.re - x0) / 2),
          lt_min hd (by linarith), (min_le_left _ _).trans_lt hdc, ?_⟩
        intro w hw hxw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact (min_le_right _ _).trans_lt (by linarith)
        · exact (min_le_left _ _).trans_lt (hK w hw hxw)
      · refine ⟨d, hd, hdc, ?_⟩
        intro w hw hxw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact (hxz hxw).elim
        · exact hK w hw hxw

/-- Littlewood's full multiplicity bound with left-edge zeros allowed.
The exact finite zero table and analyticity construct both the zero-free
approaching lines and the uniform logarithmic upper bound internally. -/
theorem littlewoodRectangle_mass_le_logNormEdges_of_finite_zero_table
    {f : ℂ → ℂ} {x0 x1 y0 y1 critical : ℝ}
    (hy : y0 < y1) (hc0 : x0 < critical) (hc1 : critical < x1)
    (K : Finset ℂ) (m : ℂ → ℕ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ), f z = 0 ↔ z ∈ K)
    (horder : ∀ z ∈ K, analyticOrderAt f z = m z)
    (hK : ∀ z ∈ K, x0 ≤ z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) :
    (2 * Real.pi) * (critical - x0) * zeroMultiplicityMassAtOrRight K m critical ≤
      (∫ t in y0..y1, Real.log ‖f ((x0 : ℂ) + I * t)‖) +
        littlewoodRectangleNonleftRemainder f x0 x1 y0 y1 := by
  obtain ⟨d, hd, hdc, hgap⟩ := exists_positive_gap_below_finite_real_parts K hc0
  let x : ℕ → ℝ := fun n => x0 + d / ((n : ℝ) + 1)
  have hxleft : ∀ n, x0 < x n := by
    intro n
    dsimp [x]
    exact lt_add_of_pos_right _ (div_pos hd (by positivity))
  have hxgap : ∀ n, x n - x0 ≤ d := by
    intro n
    dsimp [x]
    have hdiv := div_le_self hd.le
      (show (1 : ℝ) ≤ (n : ℝ) + 1 from le_add_of_nonneg_left (Nat.cast_nonneg n))
    linarith
  have hxcritical : ∀ n, x n < critical := by
    intro n
    linarith [hxgap n]
  have hxline : ∀ n y, y ∈ [[y0, y1]] →
      f ((x n : ℂ) + I * (y : ℂ)) ≠ 0 := by
    intro n y hy' hz
    have hxmem : x n ∈ [[x0, x1]] := by
      rw [uIcc_of_le (hc0.trans hc1).le]
      exact ⟨(hxleft n).le, ((hxcritical n).trans hc1).le⟩
    have hzmem : (x n : ℂ) + I * (y : ℂ) ∈
        ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ) := by
      simpa [mem_reProdIm] using And.intro hxmem hy'
    have hzK := (hzero _ hzmem).mp hz
    have hg := hgap _ hzK (by simpa using hxleft n)
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero] at hg
    linarith [hxgap n]
  have hxtend : Tendsto x atTop (𝓝 x0) := by
    have hdlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul d
    simpa [x, div_eq_mul_inv] using tendsto_const_nhds.add hdlim
  have hcompact : IsCompact ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ) :=
    isCompact_uIcc.reProdIm isCompact_uIcc
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image hf.continuousOn.norm
  have hlogle : ∀ sigma ∈ [[x0, x1]], ∀ y ∈ [[y0, y1]],
      Real.log ‖f ((sigma : ℂ) + I * (y : ℂ))‖ ≤ C := by
    intro sigma hs y hy'
    apply (Real.log_le_self (norm_nonneg _)).trans
    apply hC
    refine ⟨(sigma : ℂ) + I * (y : ℂ), ?_, rfl⟩
    simpa [mem_reProdIm] using And.intro hs hy'
  exact littlewoodRectangle_mass_le_logNormEdges_of_leftBoundaryZeros
    (hc0.trans hc1) hy hc1 K m hf hzero horder hK
    hxleft hxcritical hxline hxtend hlogle

end PrimeNumberTheorem.CarlsonZeroDensity
