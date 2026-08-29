import HardyTheorem.ConreyEquation41Global

open Complex Filter
open HardyTheorem

-- The actual finite critical-line eta-zero ordinates are exactly the positive
-- ordinates up to T where eta vanishes; auxiliary mollifier parameters do not
-- enter the resulting membership predicate.
example {g g0 g1 L T t : ℝ} (hg : g ≠ 0) :
    t ∈ conreyEtaCriticalZeroOrdinates g g0 g1 L T ↔
      0 < t ∧ t ≤ T ∧
        conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) = 0 := by
  exact mem_conreyEtaCriticalZeroOrdinates hg

#print axioms mem_conreyEtaCriticalZeroOrdinates

-- The actual ordinates admit a canonical strictly increasing enumeration.
example (g g0 g1 L T : ℝ) :
    (conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T).length =
      (conreyEtaCriticalZeroOrdinates g g0 g1 L T).card := by
  exact length_conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T

example {g g0 g1 L T t : ℝ} :
    t ∈ conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T ↔
      t ∈ conreyEtaCriticalZeroOrdinates g g0 g1 L T := by
  exact mem_conreyEtaCriticalZeroOrdinatesSorted

example (g g0 g1 L T : ℝ) :
    (conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T).Pairwise (· < ·) := by
  exact pairwise_lt_conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T

-- Every listed zero has a finite positive analytic order, so it contributes a
-- positive finite bridge multiplicity rather than an abstract weight.
example {g g0 g1 L T t : ℝ} (hg : g ≠ 0)
    (ht : t ∈ conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T) :
    analyticOrderAt (conreyDegreeOneEta g g0 g1 L)
      (conreyCriticalPoint t) ≠ ⊤ := by
  exact conreyEtaCriticalZeroOrder_ne_top hg ht

example {g g0 g1 L T t : ℝ} (hg : g ≠ 0)
    (ht : t ∈ conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T) :
    0 < analyticOrderNatAt (conreyDegreeOneEta g g0 g1 L)
      (conreyCriticalPoint t) := by
  exact conreyEtaCriticalZeroOrderNat_pos hg ht

#print axioms conreyEtaCriticalZeroOrderNat_pos

-- Mutations caught: the exponent is the actual analytic order `m`, the
-- vertical displacement is `I * (t - tau)`, and the regular factor stays
-- nonzero on a real neighborhood of the zero ordinate.
example {g g0 g1 L tau : ℝ} {m : ℕ}
    (horder :
      analyticOrderAt (conreyDegreeOneEta g g0 g1 L)
        (conreyCriticalPoint tau) = m) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h (conreyCriticalPoint tau) ∧
      h (conreyCriticalPoint tau) ≠ 0 ∧
      (∀ᶠ t in nhds tau, h (conreyCriticalPoint t) ≠ 0) ∧
      (∀ᶠ t in nhds tau,
        conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) =
          (I * ((t - tau : ℝ) : ℂ)) ^ m *
            h (conreyCriticalPoint t)) := by
  exact exists_conreyDegreeOneEta_vertical_order_factor horder

#print axioms exists_conreyDegreeOneEta_vertical_order_factor

-- The same regular factor has one continuous logarithm across a symmetric
-- interval containing the zero ordinate; no principal-branch assumption is
-- exposed in the contract.
example {g g0 g1 L tau : ℝ} {m : ℕ}
    (horder :
      analyticOrderAt (conreyDegreeOneEta g g0 g1 L)
        (conreyCriticalPoint tau) = m) :
    ∃ h : ℂ → ℂ, ∃ delta : ℝ, ∃ ell : ℝ → ℂ,
      0 < delta ∧
      AnalyticAt ℂ h (conreyCriticalPoint tau) ∧
      h (conreyCriticalPoint tau) ≠ 0 ∧
      ContinuousOn ell (Set.Ioo (tau - delta) (tau + delta)) ∧
      (∀ t ∈ Set.Ioo (tau - delta) (tau + delta),
        Complex.exp (ell t) = h (conreyCriticalPoint t)) ∧
      (∀ᶠ t in nhds tau,
        conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) =
          (I * ((t - tau : ℝ) : ℂ)) ^ m *
            h (conreyCriticalPoint t)) := by
  exact exists_conreyDegreeOneEta_regularFactor_continuousLog horder

#print axioms exists_conreyDegreeOneEta_regularFactor_continuousLog

-- The local left/right logarithms exponentiate to the actual eta restriction,
-- and their symmetric limiting argument gap is exactly the zero multiplicity
-- times pi.
example {g g0 g1 L tau : ℝ} {m : ℕ}
    (horder :
      analyticOrderAt (conreyDegreeOneEta g g0 g1 L)
        (conreyCriticalPoint tau) = m) :
    ∃ delta : ℝ, ∃ ell : ℝ → ℂ,
      0 < delta ∧
      ContinuousOn ell (Set.Ioo (tau - delta) (tau + delta)) ∧
      (∀ t ∈ Set.Ioo (tau - delta) tau,
        Complex.exp
            (MathlibAux.verticalPowerLeftLog m (tau - t) + ell t) =
          conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t)) ∧
      (∀ t ∈ Set.Ioo tau (tau + delta),
        Complex.exp
            (MathlibAux.verticalPowerRightLog m (t - tau) + ell t) =
          conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t)) ∧
      Tendsto
        (fun r =>
          (MathlibAux.verticalPowerRightLog m r + ell (tau + r)).im -
            (MathlibAux.verticalPowerLeftLog m r + ell (tau - r)).im)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((m : ℝ) * Real.pi)) := by
  exact exists_conreyDegreeOneEta_local_argument_bridge horder

#print axioms exists_conreyDegreeOneEta_local_argument_bridge
