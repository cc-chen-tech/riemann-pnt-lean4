import HardyTheorem.ConreyLocalSimpleZeroWitness

/-!
UNCOMPILED / UNVERIFIED DRAFT. 尚未编译、未验证。
Written before the implementation; no red/green run is authorized yet.
This contract would reject a global count in place of local witnesses,
loss of simplicity or open-interval location, or a supplied moment bound.
-/

open Complex Set
open scoped Interval
open PrimeNumberTheorem.CarlsonZeroDensity

namespace HardyTheorem

example {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (hsigma0 : 0 < sigma0) (hsigmaHalf : sigma0 < 1 / 2)
    (hA : 1 / 2 < A) (hU : 0 < U) (hUT : U < T)
    (hedge : ∀ z ∈ (Icc sigma0 A ×ℂ Icc U T),
      z.im = U ∨ z.re = A ∨ z.im = T →
        conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P z ≠ 0) :
    let F := conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P
    ∃ S : Finset ℝ,
      (∀ t ∈ S, t ∈ Ioo U T ∧ riemannZeta (conreyCriticalPoint t) = 0 ∧
        analyticOrderNatAt riemannZeta (conreyCriticalPoint t) = 1) ∧
      0 < (∫ t in U..T, ‖F ((sigma0 : ℂ) + I * t)‖ ^ 2) ∧
      conreyEtaThreeEdgeArgument g g0 g1 L A U T / Real.pi -
        ((T - U) * Real.log
          ((∫ t in U..T, ‖F ((sigma0 : ℂ) + I * t)‖ ^ 2) / (T - U)) +
          2 * littlewoodRectangleNonleftRemainder F sigma0 A U T) /
            (2 * Real.pi * (1 / 2 - sigma0)) - 1 ≤ (S.card : ℝ) := by
  exact exists_conrey_local_simpleZero_finset_lower_bound_meanSquare
    hg hY hP1 hsigma0 hsigmaHalf hA hU hUT hedge

#print axioms exists_conrey_local_simpleZero_finset_lower_bound_meanSquare

end HardyTheorem
