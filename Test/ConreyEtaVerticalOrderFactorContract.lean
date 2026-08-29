import HardyTheorem.ConreyDegreeOneEta

open Complex Filter
open HardyTheorem

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
