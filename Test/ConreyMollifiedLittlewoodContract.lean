import HardyTheorem.ConreyMollifiedLittlewood

/-!
The actual V1*B count must be controlled without an input zero table,
approach sequence, log bound, or zero-free shifted left edge. The second
contract checks its use in the canonical actual simple-zero lower bound.
-/

open Complex Set
open scoped BigOperators Interval
open HardyTheorem PrimeNumberTheorem.CarlsonZeroDensity

example {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
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
  exact conreyMollified_boundedFullCount_le_logNorm_edges
    hg hY hP1 hsigma0 hsigmaHalf hA hU hUT hedge

example {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
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
  exact conrey_simpleZeroCount_lower_bound_of_mollified_littlewood
    hg hY hP1 hsigma0 hsigmaHalf hA hU hUT hedge

#print axioms conreyMollified_boundedFullCount_le_logNorm_edges
#print axioms conrey_simpleZeroCount_lower_bound_of_mollified_littlewood
