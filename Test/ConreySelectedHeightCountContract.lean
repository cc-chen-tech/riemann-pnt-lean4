import HardyTheorem.ConreySelectedHeightCount

/-!
The selected-height result must actually construct both heights and the
three zero-free product edges, absorb all auxiliary constants into one
threshold, preserve the fixed L in every factor, and count at exp L.
-/

open Complex Set
open scoped Interval
open HardyTheorem PrimeNumberTheorem.CarlsonZeroDensity

example (Y : ℕ) (R L U T : ℝ) :
    conreyEquation37BoundaryRemainder Y R L U T =
      littlewoodRectangleNonleftRemainder
        (conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
          (1 / 2 - R / L) conreyExplicitP)
        (1 / 2 - R / L) (2 * Real.log L) U T := by
  exact conreyEquation37BoundaryRemainder_eq_littlewood Y R L U T

example :
    ∃ L0 : ℝ, 40000 ≤ L0 ∧
      ∀ {Y : ℕ} {R L : ℝ}, 2 ≤ Y → (Y : ℝ) ≤ Real.exp L →
        0 < R → R ≤ 6 / 5 → L0 ≤ L →
        ∃ U T : ℝ,
          U ∈ Icc (2 * Real.log L + 1) (2 * Real.log L + 2) ∧
          T ∈ Icc (Real.exp L - 1) (Real.exp L) ∧ U < T ∧
          (∀ z ∈ (Icc (1 / 2 - R / L) (2 * Real.log L) ×ℂ Icc U T),
            z.im = U ∨ z.re = 2 * Real.log L ∨ z.im = T →
              conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
                (1 / 2 - R / L) conreyExplicitP z ≠ 0) ∧
          conreyEtaThreeEdgeArgument (49 / 100) 0 (51 / 50) L
              (2 * Real.log L) U T / Real.pi -
            ((∫ t in U..T, Real.log
              ‖conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
                (1 / 2 - R / L) conreyExplicitP
                (((1 / 2 - R / L : ℝ) : ℂ) + I * t)‖) +
              (507 * Real.exp L / L + 2200000000000 * L ^ 7 +
                (2 * Real.log L - (1 / 2 - R / L)) * Real.pi)) /
              (Real.pi * (R / L)) - 1 ≤
                positiveCriticalLineSimpleZeroCount (Real.exp L) := by
  exact exists_conrey_selected_heights_simpleZeroCount_lower_bound

#print axioms conreyEquation37BoundaryRemainder_eq_littlewood
#print axioms exists_conrey_selected_heights_simpleZeroCount_lower_bound
