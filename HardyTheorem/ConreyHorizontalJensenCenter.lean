import HardyTheorem.ConreyExplicitRightVerticalLow

/-!
# Uniform lower bound at the moving Jensen centers

The low and high estimates on Conrey's explicit right vertical are joined
here into the concrete lower bound used at every moving Jensen center.
-/

open Complex

namespace HardyTheorem

/-- The actual explicit product is uniformly bounded away from zero along the
whole moving right edge.  This is the center-value input for Jensen's formula. -/
theorem one_sixth_le_norm_conreyExplicitRightVerticalProduct
    {Y : ℕ} {sigma0 L t : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : 40000 ≤ L) (ht : 1 ≤ t) (htop : t ≤ Real.exp L) :
    (1 / 6 : ℝ) ≤
      ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖ := by
  by_cases hlow : t ≤ 2 * Real.log L
  · have hbounds :=
      conreyExplicitRightVerticalProduct_low_norm_bounds
        hY hsigma0 hL ht hlow
    linarith [hbounds.1]
  · have hhigh : 2 * Real.log L ≤ t := le_of_not_ge hlow
    have hLpos : 0 < L := by linarith
    have he2lt : Real.exp 2 < 9 := by
      have he := Real.exp_one_lt_three
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [he2]
      nlinarith [Real.exp_pos 1]
    have hLexp2 : Real.exp 2 ≤ L := he2lt.le.trans (by linarith)
    let P : ℂ := conreyExplicitRightVerticalProduct Y sigma0 L t
    let A : ℂ := conreyExplicitDegreeOneHeightMain L t
    have hmain : (1 / 3 : ℝ) ≤ ‖A‖ := by
      rw [show A = conreyExplicitDegreeOneHeightMain L t by rfl,
        norm_conreyExplicitDegreeOneHeightMain_eq_re hLexp2 ht]
      exact one_third_le_conreyExplicitDegreeOneHeightMain_re hLexp2 ht
    have herr : ‖P - A‖ ≤ 79 / L := by
      simpa only [P, A] using
        norm_conreyExplicitRightVerticalProduct_sub_heightMain_le
          hY hsigma0 (by linarith : 600 ≤ L) hhigh htop
    have hnormLoss : ‖A‖ - ‖P‖ ≤ ‖P - A‖ := by
      calc
        ‖A‖ - ‖P‖ ≤ |‖P‖ - ‖A‖| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        _ ≤ ‖P - A‖ := abs_norm_sub_norm_le P A
    have herrorSmall : (79 / L : ℝ) ≤ 1 / 6 := by
      apply (div_le_iff₀ hLpos).2
      nlinarith
    linarith

end HardyTheorem
