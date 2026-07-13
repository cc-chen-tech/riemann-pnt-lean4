import PrimeNumberTheorem.ExplicitFormulaAux
import ZeroFreeRegion.PhragmenLindelofZeta

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

/-- The number of distinct absolute ordinates in the fixed local window is
uniformly `O(log A)`.  Both signs of the ordinate are covered by fixed disks,
while functional-equation symmetry moves every zero to `Re ρ ≥ 1 / 2`. -/
theorem exists_card_localZeroHeights_le_log_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 4 ≤ A →
      ((localZeroHeights A).card : ℝ) ≤ B * (1 + Real.log (A + 6)) := by
  classical
  rcases ZeroFreeRegion.exists_finsum_divisor_riemannZeta_fixed_disk_log_bound with
    ⟨Bmass, hBmass, hmass⟩
  refine ⟨2 * Bmass, mul_nonneg (by norm_num) hBmass, ?_⟩
  intro A hA
  let t : ℝ := A + 1 / 2
  let cpos : ℂ := (2 : ℂ) + I * t
  let cneg : ℂ := (2 : ℂ) + I * ((-t : ℝ) : ℂ)
  have ht : 4 ≤ |t| := by
    rw [abs_of_nonneg (by dsimp [t]; linarith)]
    dsimp [t]
    linarith
  have hneg_t : 4 ≤ |-t| := by simpa using ht
  have havoid (s : ℝ) (hs : 4 ≤ |s|) :
      ∀ z : ℂ, z ∈ Metric.closedBall ((2 : ℂ) + I * s) (17 / 10 : ℝ) → z ≠ 1 := by
    intro z hz hzone
    subst z
    have hdist : ‖(1 : ℂ) - ((2 : ℂ) + I * s)‖ ≤ (17 / 10 : ℝ) := by
      simpa [Complex.dist_eq] using (Metric.mem_closedBall.mp hz)
    have him : |s| ≤ ‖(1 : ℂ) - ((2 : ℂ) + I * s)‖ := by
      simpa using Complex.abs_im_le_norm ((1 : ℂ) - ((2 : ℂ) + I * s))
    linarith
  rcases ZeroFreeRegion.exists_finset_riemannZeta_zeros_closedBall_card_le_divisor_mass
      (c := cpos) (r := (17 / 10 : ℝ)) (R := (17 / 10 : ℝ)) le_rfl
      (by simpa [cpos] using havoid t ht) with
    ⟨zerosPos, hzerosPos, hcardPos⟩
  rcases ZeroFreeRegion.exists_finset_riemannZeta_zeros_closedBall_card_le_divisor_mass
      (c := cneg) (r := (17 / 10 : ℝ)) (R := (17 / 10 : ℝ)) le_rfl
      (by simpa [cneg] using havoid (-t) hneg_t) with
    ⟨zerosNeg, hzerosNeg, hcardNeg⟩
  have hcardPos' : (zerosPos.card : ℝ) ≤
      ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall cpos (17 / 10 : ℝ)) u : ℝ) := by
    rw [ZeroFreeRegion.finsum_divisor_riemannZeta_closedBall_eq_finsum_mem_of_le
      (c := cpos) (b := (17 / 10 : ℝ)) (R := (17 / 10 : ℝ)) le_rfl]
    exact hcardPos
  have hcardNeg' : (zerosNeg.card : ℝ) ≤
      ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall cneg (17 / 10 : ℝ)) u : ℝ) := by
    rw [ZeroFreeRegion.finsum_divisor_riemannZeta_closedBall_eq_finsum_mem_of_le
      (c := cneg) (b := (17 / 10 : ℝ)) (R := (17 / 10 : ℝ)) le_rfl]
    exact hcardNeg
  have hright_mem (ρ : ℂ) (hρ : RiemannHypothesis.IsNontrivialZero ρ)
      (hlow : A - 1 / 4 ≤ |ρ.im|) (hhigh : |ρ.im| ≤ A + 5 / 4)
      (hre : (1 / 2 : ℝ) ≤ ρ.re) : ρ ∈ zerosPos ∪ zerosNeg := by
    have hre_high : ρ.re < 1 := hρ.2.2
    by_cases him : 0 ≤ ρ.im
    · apply Finset.mem_union.mpr
      left
      apply (hzerosPos ρ).mpr
      refine ⟨?_, hρ.1⟩
      rw [Metric.mem_closedBall, Complex.dist_eq]
      have hlow' : A - 1 / 4 ≤ ρ.im := by simpa [abs_of_nonneg him] using hlow
      have hhigh' : ρ.im ≤ A + 5 / 4 := by simpa [abs_of_nonneg him] using hhigh
      have hsquare : ‖ρ - cpos‖ ^ 2 ≤ (17 / 10 : ℝ) ^ 2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq_apply, cpos, t]
        nlinarith
      simpa [cpos] using
        (show ‖ρ - cpos‖ ≤ (17 / 10 : ℝ) by
          nlinarith [norm_nonneg (ρ - cpos)])
    · have him' : ρ.im < 0 := lt_of_not_ge him
      apply Finset.mem_union.mpr
      right
      apply (hzerosNeg ρ).mpr
      refine ⟨?_, hρ.1⟩
      rw [Metric.mem_closedBall, Complex.dist_eq]
      have hlow' : A - 1 / 4 ≤ -ρ.im := by simpa [abs_of_neg him'] using hlow
      have hhigh' : -ρ.im ≤ A + 5 / 4 := by simpa [abs_of_neg him'] using hhigh
      have hsquare : ‖ρ - cneg‖ ^ 2 ≤ (17 / 10 : ℝ) ^ 2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq_apply, cneg, t]
        nlinarith
      simpa [cneg] using
        (show ‖ρ - cneg‖ ≤ (17 / 10 : ℝ) by
          nlinarith [norm_nonneg (ρ - cneg)])
  have hsubset : localZeroHeights A ⊆
      (zerosPos ∪ zerosNeg).image fun ρ : ℂ => |ρ.im| := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨ρ, hρ, rfl⟩
    rcases Finset.mem_filter.mp hρ with ⟨hρtrunc, hlow, hhigh⟩
    have hρzero : RiemannHypothesis.IsNontrivialZero ρ :=
      (mem_nontrivialZerosFinset.mp hρtrunc).1
    by_cases hre : (1 / 2 : ℝ) ≤ ρ.re
    · exact Finset.mem_image.mpr ⟨ρ, hright_mem ρ hρzero hlow hhigh hre, rfl⟩
    · let ρ' : ℂ := 1 - ρ
      have hρ'zero : RiemannHypothesis.IsNontrivialZero ρ' := by
        simpa [ρ'] using nontrivial_zero_symmetric' hρzero
      have hre' : (1 / 2 : ℝ) ≤ ρ'.re := by
        dsimp [ρ']
        linarith
      have habs : |ρ'.im| = |ρ.im| := by simp [ρ', Complex.sub_im]
      apply Finset.mem_image.mpr
      refine ⟨ρ', hright_mem ρ' hρ'zero ?_ ?_ hre', habs⟩
      · rw [habs]
        exact hlow
      · rw [habs]
        exact hhigh
  have hcardImage : ((localZeroHeights A).card : ℝ) ≤
      (((zerosPos ∪ zerosNeg).image fun ρ : ℂ => |ρ.im|).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have himageCard :
      (((zerosPos ∪ zerosNeg).image fun ρ : ℂ => |ρ.im|).card : ℝ) ≤
        ((zerosPos ∪ zerosNeg).card : ℝ) := by
    exact_mod_cast Finset.card_image_le
  have hunionCard : ((zerosPos ∪ zerosNeg).card : ℝ) ≤
      (zerosPos.card : ℝ) + (zerosNeg.card : ℝ) := by
    exact_mod_cast Finset.card_union_le zerosPos zerosNeg
  have hmassPos := hmass t ht
  have hmassNeg := hmass (-t) hneg_t
  have hzerosPosBound : (zerosPos.card : ℝ) ≤
      Bmass * (1 + Real.log (|t| + 5)) := by
    exact hcardPos'.trans (by simpa [cpos] using hmassPos)
  have hzerosNegBound : (zerosNeg.card : ℝ) ≤
      Bmass * (1 + Real.log (|t| + 5)) := by
    exact hcardNeg'.trans (by simpa only [cneg, map_neg, abs_neg] using hmassNeg)
  have hlog : Real.log (|t| + 5) ≤ Real.log (A + 6) := by
    apply Real.log_le_log
    · positivity
    · rw [abs_of_nonneg (by dsimp [t]; linarith)]
      dsimp [t]
      linarith
  have hfactor : Bmass * (1 + Real.log (|t| + 5)) ≤
      Bmass * (1 + Real.log (A + 6)) := by
    apply mul_le_mul_of_nonneg_left _ hBmass
    linarith
  calc
    ((localZeroHeights A).card : ℝ) ≤
        (((zerosPos ∪ zerosNeg).image fun ρ : ℂ => |ρ.im|).card : ℝ) := hcardImage
    _ ≤ ((zerosPos ∪ zerosNeg).card : ℝ) := himageCard
    _ ≤ (zerosPos.card : ℝ) + (zerosNeg.card : ℝ) := hunionCard
    _ ≤ 2 * Bmass * (1 + Real.log (A + 6)) := by
      nlinarith [hzerosPosBound.trans hfactor, hzerosNegBound.trans hfactor]

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
