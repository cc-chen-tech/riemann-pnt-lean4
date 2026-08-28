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
