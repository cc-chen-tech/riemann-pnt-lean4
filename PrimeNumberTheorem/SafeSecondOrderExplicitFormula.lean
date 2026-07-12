import PrimeNumberTheorem.SecondOrderExplicitFormula
import PrimeNumberTheorem.ExplicitFormulaAux

open Complex Filter Topology Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- At every good positive height and for every fixed right edge `c > 1`, one
can choose a left edge in `(0, 1/2)` avoiding the real part of every enclosed
nontrivial zeta zero.  The resulting rectangle has all candidate poles in its
strict interior. -/
theorem exists_safe_leftBoundary_of_goodHeight
    {T c : ℝ} (hT : 0 < T) (hc : 1 < c)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧ a < c ∧
      ∀ p ∈ ([[a, c]] ×ℂ [[-T, T]] : Set ℂ),
        p = 1 ∨ riemannZeta p = 0 →
          a < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T := by
  let Z : Set ℂ :=
    {ρ : ℂ | RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| ≤ T}
  let X : Set ℝ := (fun ρ : ℂ => ρ.re) '' Z
  have hZ_finite : Z.Finite := by
    simpa [Z] using finite_nontrivial_zeros_bounded_height T
  have hX_finite : X.Finite := hZ_finite.image _
  have hIoo_infinite : (Set.Ioo (0 : ℝ) (1 / 2)).Infinite :=
    Set.Ioo_infinite (by norm_num)
  have hnot_subset : ¬ Set.Ioo (0 : ℝ) (1 / 2) ⊆ X := by
    intro hsubset
    exact hIoo_infinite (hX_finite.subset hsubset)
  rcases Set.not_subset.mp hnot_subset with ⟨a, ha, ha_not_bad⟩
  have hac : a < c := lt_trans ha.2 (by linarith)
  refine ⟨a, ha.1, ha.2, hac, ?_⟩
  intro p hpK hp
  have hpK' := hpK
  simp only [Complex.mem_reProdIm] at hpK'
  rw [uIcc_of_le hac.le] at hpK'
  rw [uIcc_of_le (by linarith : -T ≤ T)] at hpK'
  rcases hp with rfl | hpzero
  · simpa using (show a < 1 ∧ 1 < c ∧ -T < 0 ∧ 0 < T from
      ⟨by linarith [ha.2], hc, by linarith, hT⟩)
  · have hpre_lt_one : p.re < 1 := by
      by_contra hnot
      exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hnot)) hpzero
    have hpre_pos : 0 < p.re := lt_of_lt_of_le ha.1 hpK'.1.1
    have hp_nontrivial : RiemannHypothesis.IsNontrivialZero p :=
      ⟨hpzero, hpre_pos, hpre_lt_one⟩
    have habs_le : |p.im| ≤ T := abs_le.mpr hpK'.2
    have habs_lt : |p.im| < T :=
      lt_of_le_of_ne habs_le (hgood p hp_nontrivial)
    have him := abs_lt.mp habs_lt
    have hleft : a < p.re := by
      apply lt_of_le_of_ne hpK'.1.1
      intro heq
      apply ha_not_bad
      refine ⟨p, ?_, ?_⟩
      · exact ⟨hp_nontrivial, habs_le⟩
      · exact heq.symm
    exact ⟨hleft, hpre_lt_one.trans hc, him.1, him.2⟩

/-- Safe finite-height second-order explicit formulas exist above every
prescribed Perron height.  Both the horizontal height and the left edge are
chosen unconditionally, so the resulting theorem has no pole-free-boundary
hypothesis. -/
theorem exists_safe_norm_residue_sum_sub_contourRemainder_sub_smoothedPsi_le
    {x c A : ℝ} (hx : 0 < x) (hc : 1 < c) :
    ∃ (W a : ℝ) (poles : Finset ℂ) (residue : ℂ → ℂ),
      A < W ∧ 0 < W ∧ 0 < a ∧ a < 1 / 2 ∧ a < c ∧
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 2) ∧
      ‖((∑ p ∈ poles, residue p) - secondOrderContourRemainder x a c W) -
          (smoothedChebyshevPsi x : ℂ)‖ ≤
        ∑' n : ℕ,
          vonMangoldt n * (x / n) ^ c / (2 * Real.pi ^ 2 * W) := by
  let B : ℝ := max (2 * Real.pi * A) 1
  rcases ExplicitFormulaAux.exists_goodHeight_Ioo B with
    ⟨T, hBT, hTupper, hgood⟩
  have hTpos : 0 < T := by
    have hBone : 1 ≤ B := by dsimp [B]; exact le_max_right _ _
    linarith
  rcases exists_safe_leftBoundary_of_goodHeight hTpos hc hgood with
    ⟨a, ha0, hahalf, hac, hsafe⟩
  let W : ℝ := T / (2 * Real.pi)
  have hden : 0 < 2 * Real.pi := mul_pos zero_lt_two Real.pi_pos
  have hW : 0 < W := div_pos hTpos hden
  have hAW : A < W := by
    apply (lt_div_iff₀ hden).2
    have hBA : 2 * Real.pi * A ≤ B := by
      dsimp [B]
      exact le_max_left _ _
    exact lt_of_le_of_lt (by simpa [mul_comm] using hBA) hBT
  have hscale : 2 * Real.pi * W = T := by
    dsimp [W]
    field_simp [Real.pi_ne_zero]
  have hsafeW : ∀ p ∈
      ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W := by
    simpa [hscale] using hsafe
  rcases
      exists_norm_residue_sum_sub_contourRemainder_sub_smoothedPsi_le
        hx ha0 hac hc hW hsafeW with
    ⟨poles, residue, hpoles, hclass, hresidue, hformula⟩
  exact ⟨W, a, poles, residue, hAW, hW, ha0, hahalf, hac,
    hpoles, hclass, hresidue, hformula⟩

end ExplicitFormulaResidues
end PrimeNumberTheorem
