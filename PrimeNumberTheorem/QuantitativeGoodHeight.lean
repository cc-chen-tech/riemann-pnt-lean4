import PrimeNumberTheorem.ExplicitFormulaAux
import ZeroFreeRegion.MeromorphicAux

open Complex Set

namespace PrimeNumberTheorem
namespace ExplicitFormulaAux

/-- Absolute ordinates of nontrivial zeros in the fixed-width window used to
select a quantitatively safe contour height. -/
noncomputable def localZeroHeights (A : ℝ) : Finset ℝ :=
  ((nontrivialZerosFinset (A + 2)).filter fun ρ : ℂ =>
      A - 1 / 4 ≤ |ρ.im| ∧ |ρ.im| ≤ A + 5 / 4).image fun ρ => |ρ.im|

lemma mem_localZeroHeights_of_nontrivialZero {A : ℝ} {ρ : ℂ}
    (hρ : RiemannHypothesis.IsNontrivialZero ρ)
    (hlow : A - 1 / 4 ≤ |ρ.im|) (hhigh : |ρ.im| ≤ A + 5 / 4) :
    |ρ.im| ∈ localZeroHeights A := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨ρ, ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨mem_nontrivialZerosFinset.mpr ⟨hρ, ?_⟩, hlow, hhigh⟩
  linarith

/-- Every unit interval contains a height separated from every nontrivial-zero
ordinate by an explicit pigeonhole distance.  Unlike `exists_goodHeight_Ioo`,
this theorem gives the quantitative input needed to bound principal parts of
`zeta'/zeta` on a horizontal contour. -/
theorem exists_goodHeight_Icc_quantitatively_separated (A : ℝ) :
    ∃ T ∈ Set.Icc A (A + 1),
      goodHeight T ∧
        ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ →
          1 / ((4 : ℝ) * (((localZeroHeights A).card : ℝ) + 1)) ≤
            |T - abs ρ.im| := by
  classical
  let H := localZeroHeights A
  rcases ZeroFreeRegion.exists_radius_separated_from_finset H
      (show A < A + 1 by linarith) with ⟨T, hT, hsep⟩
  have hdelta_pos :
      0 < 1 / ((4 : ℝ) * ((H.card : ℝ) + 1)) := by positivity
  have hdelta_quarter :
      1 / ((4 : ℝ) * ((H.card : ℝ) + 1)) ≤ 1 / 4 := by
    have hone : (1 : ℝ) ≤ (H.card : ℝ) + 1 := by
      have hcard : (0 : ℝ) ≤ (H.card : ℝ) := by positivity
      linarith
    have hden : (4 : ℝ) ≤ 4 * ((H.card : ℝ) + 1) := by nlinarith
    exact one_div_le_one_div_of_le (by norm_num) hden
  have hall : ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ →
      1 / ((4 : ℝ) * ((H.card : ℝ) + 1)) ≤ |T - abs ρ.im| := by
    intro ρ hρ
    by_cases hlow : A - 1 / 4 ≤ |ρ.im|
    · by_cases hhigh : |ρ.im| ≤ A + 5 / 4
      · have hmem : |ρ.im| ∈ H := by
          simpa [H] using mem_localZeroHeights_of_nontrivialZero hρ hlow hhigh
        simpa [H] using hsep |ρ.im| hmem
      · have hfar : 1 / 4 ≤ |T - abs ρ.im| := by
          have hheight : A + 5 / 4 < |ρ.im| := lt_of_not_ge hhigh
          rw [abs_of_nonpos]
          · linarith [hT.2]
          · linarith [hT.2]
        exact hdelta_quarter.trans hfar
    · have hfar : 1 / 4 ≤ |T - abs ρ.im| := by
        have hheight : |ρ.im| < A - 1 / 4 := lt_of_not_ge hlow
        rw [abs_of_nonneg]
        · linarith [hT.1]
        · linarith [hT.1]
      exact hdelta_quarter.trans hfar
  refine ⟨T, hT, ?_, ?_⟩
  · intro ρ hρ heq
    have h := hall ρ hρ
    rw [← heq, sub_self, abs_zero] at h
    exact (not_lt_of_ge h) hdelta_pos
  · simpa [H] using hall

end ExplicitFormulaAux
end PrimeNumberTheorem
