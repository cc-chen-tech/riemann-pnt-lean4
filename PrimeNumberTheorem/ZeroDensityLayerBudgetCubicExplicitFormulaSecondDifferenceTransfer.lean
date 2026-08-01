import PrimeNumberTheorem.ZeroDensityLayerBudgetSecondRieszPsiSandwich

open Real

namespace PrimeNumberTheorem

/-- Three complex pointwise approximations lose at most the weighted sum of
their errors after taking a real second forward difference. -/
theorem abs_real_secondDifference_sub_le
    {A0 A1 A2 : ℂ} {P0 P1 P2 E0 E1 E2 : ℝ}
    (h0 : ‖A0 - (P0 : ℂ)‖ ≤ E0)
    (h1 : ‖A1 - (P1 : ℂ)‖ ≤ E1)
    (h2 : ‖A2 - (P2 : ℂ)‖ ≤ E2) :
    |(A2.re - 2 * A1.re + A0.re) - (P2 - 2 * P1 + P0)| ≤
      E2 + 2 * E1 + E0 := by
  have hre0 : |A0.re - P0| ≤ E0 := by
    calc
      |A0.re - P0| = |(A0 - (P0 : ℂ)).re| := by simp
      _ ≤ ‖A0 - (P0 : ℂ)‖ := Complex.abs_re_le_norm _
      _ ≤ E0 := h0
  have hre1 : |A1.re - P1| ≤ E1 := by
    calc
      |A1.re - P1| = |(A1 - (P1 : ℂ)).re| := by simp
      _ ≤ ‖A1 - (P1 : ℂ)‖ := Complex.abs_re_le_norm _
      _ ≤ E1 := h1
  have hre2 : |A2.re - P2| ≤ E2 := by
    calc
      |A2.re - P2| = |(A2 - (P2 : ℂ)).re| := by simp
      _ ≤ ‖A2 - (P2 : ℂ)‖ := Complex.abs_re_le_norm _
      _ ≤ E2 := h2
  rw [show
    (A2.re - 2 * A1.re + A0.re) - (P2 - 2 * P1 + P0) =
      (A2.re - P2) - 2 * (A1.re - P1) + (A0.re - P0) by ring]
  calc
    |(A2.re - P2) - 2 * (A1.re - P1) + (A0.re - P0)| ≤
        |A2.re - P2| + |2 * (A1.re - P1)| + |A0.re - P0| := by
      simpa [sub_eq_add_neg, abs_neg, add_assoc] using
        (abs_add_three (A2.re - P2) (-2 * (A1.re - P1)) (A0.re - P0))
    _ = |A2.re - P2| + 2 * |A1.re - P1| + |A0.re - P0| := by
      rw [abs_mul]
      norm_num
    _ ≤ E2 + 2 * E1 + E0 := by linarith

/-- Pointwise complex approximations to the actual second Riesz Chebyshev
mean at three logarithmically spaced points give explicit one-sided bounds for
the unsmoothed Chebyshev function at the two endpoints. -/
theorem chebyshevPsi_bounds_of_three_secondRiesz_complex_approximations
    {x h E0 E1 E2 : ℝ} {A0 A1 A2 : ℂ}
    (hx : 0 < x) (hh : 0 < h)
    (h0 : ‖A0 - (secondRieszChebyshevPsi x : ℂ)‖ ≤ E0)
    (h1 : ‖A1 - (secondRieszChebyshevPsi (x * Real.exp h) : ℂ)‖ ≤ E1)
    (h2 : ‖A2 - (secondRieszChebyshevPsi (x * Real.exp (2 * h)) : ℂ)‖ ≤ E2) :
    chebyshevPsi x ≤
        ((A2.re - 2 * A1.re + A0.re) + (E2 + 2 * E1 + E0)) / h ^ 2 ∧
      ((A2.re - 2 * A1.re + A0.re) - (E2 + 2 * E1 + E0)) / h ^ 2 ≤
        chebyshevPsi (x * Real.exp (2 * h)) := by
  have herror :
      |(A2.re - 2 * A1.re + A0.re) -
        (secondRieszChebyshevPsi (x * Real.exp (2 * h)) -
          2 * secondRieszChebyshevPsi (x * Real.exp h) +
          secondRieszChebyshevPsi x)| ≤ E2 + 2 * E1 + E0 := by
    exact abs_real_secondDifference_sub_le h0 h1 h2
  have hlower :
      (A2.re - 2 * A1.re + A0.re) - (E2 + 2 * E1 + E0) ≤
        secondRieszChebyshevPsi (x * Real.exp (2 * h)) -
          2 * secondRieszChebyshevPsi (x * Real.exp h) +
          secondRieszChebyshevPsi x := by
    have := (abs_le.mp herror).2
    linarith
  have hupper :
      secondRieszChebyshevPsi (x * Real.exp (2 * h)) -
          2 * secondRieszChebyshevPsi (x * Real.exp h) +
          secondRieszChebyshevPsi x ≤
        (A2.re - 2 * A1.re + A0.re) + (E2 + 2 * E1 + E0) := by
    have := (abs_le.mp herror).1
    linarith
  have hsandwich := chebyshevPsi_le_secondRieszSecondDifference_div_sq_le hx hh
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  dsimp only at hsandwich ⊢
  constructor
  · apply (le_div_iff₀ hh2).2
    exact ((le_div_iff₀ hh2).1 hsandwich.1).trans hupper
  · apply (div_le_iff₀ hh2).2
    exact hlower.trans ((div_le_iff₀ hh2).1 hsandwich.2)

end PrimeNumberTheorem
