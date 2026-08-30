import HardyTheorem.ConreyEquation35Global

/-!
# Full mollified multiplicity budgets on the same height interval

Unlike the half-weighted counts, every critical-line root is charged by its
full analytic order. At nonnegative U the height range is exactly `(U,T]`;
for arbitrary U the underlying positive-height restriction also remains.
Identification
with eta is used only at positive-height roots, never at the possible pole 1.
-/

open Complex Set
open scoped BigOperators

namespace HardyTheorem

/-- Full analytic multiplicity of the actual product in the bounded right
half-rectangle, with the original lower height cutoff retained. -/
noncomputable def conreyMollifiedV1BoundedFullZeroCountBetween
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ) (A U T : ℝ) : ℕ :=
  ∑ z ∈ (conreyMollifiedV1BoundedZeros g g0 g1 L Y sigma0 P A T).filter
      (fun z => U < z.im),
    analyticOrderNatAt (conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) z

/-- Full analytic multiplicity of the actual product on the unbounded right
half-strip, restricted to the same lower height cutoff. -/
noncomputable def conreyMollifiedV1HalfStripFullZeroCountBetween
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ) (U T : ℝ) : ℕ :=
  ∑ z ∈ (conreyMollifiedV1HalfStripZeros g g0 g1 L Y sigma0 P T).filter
      (fun z => U < z.im),
    analyticOrderNatAt (conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) z

/-- Any actual eta-zero family in the same positive-height rectangle has
full multiplicity no greater than that of the normalized mollified product.
No zero-free condition is imposed on the product's boundary. -/
theorem conreyEta_zero_mass_le_mollified_bounded_full
    {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) (hU : 0 ≤ U)
    (K : Finset ℂ)
    (hK : ∀ z ∈ K, 1 / 2 ≤ z.re ∧ z.re ≤ A ∧ U < z.im ∧ z.im ≤ T ∧
      conreyDegreeOneEta g g0 g1 L z = 0) :
    (∑ z ∈ K, analyticOrderNatAt (conreyDegreeOneEta g g0 g1 L) z) ≤
      conreyMollifiedV1BoundedFullZeroCountBetween g g0 g1 L Y sigma0 P A U T := by
  classical
  have hgeom : ∀ z ∈ K, 0 < z.re ∧ z ≠ 1 := by
    intro z hz
    have hd := hK z hz
    refine ⟨by linarith [hd.1], ?_⟩
    intro heq
    have him := hd.2.2.1
    simp only [heq, Complex.one_im] at him
    linarith
  have hsub : K ⊆ (conreyMollifiedV1BoundedZeros
      g g0 g1 L Y sigma0 P A T).filter (fun z => U < z.im) := by
    intro z hz
    obtain ⟨hzlo, hzhi, hzU, hzT, hz0⟩ := hK z hz
    refine Finset.mem_filter.mpr ⟨?_, hzU⟩
    apply (mem_conreyMollifiedV1BoundedZeros hg hY hP1).mpr
    refine ⟨hzlo, hzhi, lt_of_le_of_lt hU hzU, hzT, ?_⟩
    apply conreyMollifiedDegreeOneV1_eq_zero_of_v1_eq_zero
    exact (conreyDegreeOneEta_eq_zero_iff_conreyDegreeOneV1_eq_zero_of_re_pos_of_ne_one
      (hgeom z hz).1 (hgeom z hz).2).mp hz0
  calc
    _ ≤ ∑ z ∈ K,
        analyticOrderNatAt (conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) z := by
      apply Finset.sum_le_sum
      intro z hz
      have horder : analyticOrderNatAt (conreyDegreeOneEta g g0 g1 L) z =
          analyticOrderNatAt (conreyDegreeOneV1 g g0 g1 L) z := by
        unfold analyticOrderNatAt
        rw [analyticOrderAt_conreyDegreeOneEta_eq_conreyDegreeOneV1_of_re_pos_of_ne_one
          (hgeom z hz).1 (hgeom z hz).2]
      rw [horder]
      exact analyticOrderNatAt_conreyDegreeOneV1_le_mollified_of_g_ne_zero
        hg (hgeom z hz).1 (hgeom z hz).2 hY hP1
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

/-- Enlarging the bounded rectangle to the actual half-strip can only
increase the full product multiplicity, at unchanged parameters and heights. -/
theorem conreyMollifiedV1BoundedFullZeroCountBetween_le_halfStrip
    {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) :
    conreyMollifiedV1BoundedFullZeroCountBetween g g0 g1 L Y sigma0 P A U T ≤
      conreyMollifiedV1HalfStripFullZeroCountBetween g g0 g1 L Y sigma0 P U T := by
  classical
  apply Finset.sum_le_sum_of_subset
  intro z hz
  obtain ⟨hzK, hzU⟩ := Finset.mem_filter.mp hz
  obtain ⟨hzlo, _hzhi, hzpos, hzT, hz0⟩ :=
    (mem_conreyMollifiedV1BoundedZeros hg hY hP1).mp hzK
  exact Finset.mem_filter.mpr
    ⟨(mem_conreyMollifiedV1HalfStripZeros hg hY hP1).mpr ⟨hzlo, hzpos, hzT, hz0⟩, hzU⟩

end HardyTheorem
