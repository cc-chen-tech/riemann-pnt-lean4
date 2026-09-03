import HardyTheorem.ConreyReciprocalZetaStrip

namespace HardyTheorem

-- The literal strip crosses to the LEFT of Re(s)=1. Replacing it by
-- a right-half-plane hypothesis, dropping nonvanishing, or assuming
-- the norm estimate itself cannot satisfy this unconditional contract.
example : ∃ c T : ℝ, 0 < c ∧ c ≤ 1 ∧ 2 ≤ T ∧
    ∀ σ t : ℝ, T ≤ |t| → 1 - c / Real.log |t| ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0 ∧
        ‖(riemannZeta ((σ : ℂ) + Complex.I * t))⁻¹‖ ≤
          (1 + Real.log |t| / c) * Real.exp (Real.log |t| / 4) :=
  exists_conrey_reciprocal_zeta_quarterPower_strip

#print axioms exists_conrey_reciprocal_zeta_quarterPower_strip

end HardyTheorem
