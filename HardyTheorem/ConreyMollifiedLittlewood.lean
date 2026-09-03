import HardyTheorem.ConreyMollifiedRectangleZeros
import HardyTheorem.ConreyMollifiedContourCount
import PrimeNumberTheorem.LittlewoodFiniteZeroTable

/-!
Littlewood's inequality for the actual mollified product, and its direct
use in the canonical simple-zero count. The shifted left edge may contain
zeros. All product zeros, finite orders, approaching zero-free lines and
logarithmic upper bounds are constructed, not assumed.

Nonvanishing on the other three product edges remains explicit. This is
not a mollified mean-square asymptotic or a positive-proportion theorem.
-/

open Complex Set
open scoped BigOperators Interval
open PrimeNumberTheorem.CarlsonZeroDensity

namespace HardyTheorem

/-- The actual bounded full product multiplicity is controlled by the
left log-norm integral and the complete non-left Littlewood remainder.
No nonvanishing condition is imposed on the shifted left edge. -/
theorem conreyMollified_boundedFullCount_le_logNorm_edges
    {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (hsigma0 : 0 < sigma0) (hsigmaHalf : sigma0 < 1 / 2)
    (hA : 1 / 2 < A) (hU : 0 < U) (hUT : U < T)
    (hedge : ∀ z ∈ (Icc sigma0 A ×ℂ Icc U T),
      z.im = U ∨ z.re = A ∨ z.im = T →
        conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P z ≠ 0) :
    (2 * Real.pi) * (1 / 2 - sigma0) *
        (conreyMollifiedV1BoundedFullZeroCountBetween g g0 g1 L Y sigma0 P A U T : ℝ) ≤
      (∫ t in U..T, Real.log
        ‖conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P ((sigma0 : ℂ) + I * t)‖) +
      littlewoodRectangleNonleftRemainder
        (conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) sigma0 A U T := by
  let F := conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P
  have hrect : ([[sigma0, A]] ×ℂ [[U, T]] : Set ℂ) = Icc sigma0 A ×ℂ Icc U T := by
    rw [uIcc_of_le (hsigmaHalf.trans hA).le, uIcc_of_le hUT.le]
  obtain ⟨K, hK, horder, hmassNat⟩ := exists_conreyMollified_rectangle_zero_finset
    hg hY hP1 hsigma0 hsigmaHalf.le hU
    (fun z hz hzu => hedge z hz (Or.inl hzu))
  have hKmem : ∀ z ∈ K, z ∈ (Icc sigma0 A ×ℂ Icc U T : Set ℂ) := by
    intro z hz
    obtain ⟨hlo, hhi, hU', hT', _⟩ := (hK z).mp hz
    exact ⟨⟨hlo, hhi⟩, hU', hT'⟩
  have hf : AnalyticOnNhd ℂ F ([[sigma0, A]] ×ℂ [[U, T]]) := by
    intro z hz
    rw [hrect] at hz
    have hz0 : 0 < z.re := hsigma0.trans_le hz.1.1
    have hz1 : z ≠ 1 := by
      intro heq
      have him := hz.2.1
      simp only [heq, Complex.one_im] at him
      linarith
    exact (analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one
      (g := g) (g0 := g0) (g1 := g1) (L := L) hz0 hz1).mul
      (analyticOnNhd_conreyMollifier Y sigma0 P z (by simp))
  have hzero : ∀ z ∈ ([[sigma0, A]] ×ℂ [[U, T]] : Set ℂ), F z = 0 ↔ z ∈ K := by
    intro z hz
    rw [hrect] at hz
    exact ⟨fun hfz => (hK z).mpr ⟨hz.1.1, hz.1.2, hz.2.1, hz.2.2, hfz⟩,
      fun hzK => ((hK z).mp hzK).2.2.2.2⟩
  have hKstrict : ∀ z ∈ K, sigma0 ≤ z.re ∧ z.re < A ∧ U < z.im ∧ z.im < T := by
    intro z hz
    obtain ⟨hzlo, hzhi, hzU, hzT, hz0⟩ := (hK z).mp hz
    refine ⟨hzlo, ?_, ?_, ?_⟩
    · apply lt_of_le_of_ne hzhi
      intro heq
      exact hedge z (hKmem z hz) (Or.inr (Or.inl heq)) hz0
    · apply lt_of_le_of_ne hzU
      intro heq
      exact hedge z (hKmem z hz) (Or.inl heq.symm) hz0
    · apply lt_of_le_of_ne hzT
      intro heq
      exact hedge z (hKmem z hz) (Or.inr (Or.inr heq)) hz0
  have hmass : zeroMultiplicityMassAtOrRight K (analyticOrderNatAt F) (1 / 2) =
      (conreyMollifiedV1BoundedFullZeroCountBetween g g0 g1 L Y sigma0 P A U T : ℝ) := by
    unfold zeroMultiplicityMassAtOrRight
    exact_mod_cast hmassNat
  have h := littlewoodRectangle_mass_le_logNormEdges_of_finite_zero_table
    hUT hsigmaHalf hA K (analyticOrderNatAt F) hf hzero horder hKstrict
  rw [hmass] at h
  exact h

/-- The canonical actual simple-zero count after inserting the actual
product's Littlewood inequality. All parameters and heights stay fixed. -/
theorem conrey_simpleZeroCount_lower_bound_of_mollified_littlewood
    {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (hsigma0 : 0 < sigma0) (hsigmaHalf : sigma0 < 1 / 2)
    (hA : 1 / 2 < A) (hU : 0 < U) (hUT : U < T)
    (hedge : ∀ z ∈ (Icc sigma0 A ×ℂ Icc U T),
      z.im = U ∨ z.re = A ∨ z.im = T →
        conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P z ≠ 0) :
    conreyEtaThreeEdgeArgument g g0 g1 L A U T / Real.pi -
      ((∫ t in U..T, Real.log
        ‖conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P ((sigma0 : ℂ) + I * t)‖) +
        littlewoodRectangleNonleftRemainder
          (conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) sigma0 A U T) /
          (Real.pi * (1 / 2 - sigma0)) - 1 ≤ positiveCriticalLineSimpleZeroCount T := by
  have heta : ∀ z ∈ (Icc (1 / 2 : ℝ) A ×ℂ Icc U T),
      z.im = U ∨ z.re = A ∨ z.im = T → conreyDegreeOneEta g g0 g1 L z ≠ 0 := by
    intro z hz he hz0
    have hzre : 0 < z.re := by linarith [hz.1.1]
    have hz1 : z ≠ 1 := by
      intro heq
      have him := hz.2.1
      simp only [heq, Complex.one_im] at him
      linarith
    apply hedge z ⟨⟨hsigmaHalf.le.trans hz.1.1, hz.1.2⟩, hz.2⟩ he
    exact conreyMollifiedDegreeOneV1_eq_zero_of_v1_eq_zero
      ((conreyDegreeOneEta_eq_zero_iff_conreyDegreeOneV1_eq_zero_of_re_pos_of_ne_one
        hzre hz1).mp hz0)
  have hcount := conrey_simpleZeroCount_lower_bound_of_three_edges_mollified_bounded
    (sigma0 := sigma0) hg hY hP1 hA hU.le hUT heta
  have hmass := conreyMollified_boundedFullCount_le_logNorm_edges
    hg hY hP1 hsigma0 hsigmaHalf hA hU hUT hedge
  have hden : 0 < Real.pi * (1 / 2 - sigma0) :=
    mul_pos Real.pi_pos (sub_pos.mpr hsigmaHalf)
  have htwo : 2 * (conreyMollifiedV1BoundedFullZeroCountBetween
      g g0 g1 L Y sigma0 P A U T : ℝ) ≤
      ((∫ t in U..T, Real.log
        ‖conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P ((sigma0 : ℂ) + I * t)‖) +
        littlewoodRectangleNonleftRemainder
          (conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) sigma0 A U T) /
          (Real.pi * (1 / 2 - sigma0)) := by
    apply (le_div_iff₀ hden).mpr
    calc
      _ = (2 * Real.pi) * (1 / 2 - sigma0) *
          (conreyMollifiedV1BoundedFullZeroCountBetween g g0 g1 L Y sigma0 P A U T : ℝ) := by
        ring
      _ ≤ _ := hmass
  linarith only [hcount, htwo]

end HardyTheorem
