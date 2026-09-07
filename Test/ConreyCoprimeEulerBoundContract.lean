import HardyTheorem.ConreyCoprimeEulerBound

open Complex
open scoped BigOperators

example : 1 ≤ ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ)) := by
  exact HardyTheorem.one_le_conreyEulerCorrectionConstant

-- The modulus-dependent product must remain: no uniform bound in m alone.
example (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ16 : δ ≤ 1 / 16)
    {z : ℂ} (hz : -2 * δ ≤ z.re) :
    ‖(∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + z))))⁻¹‖ ≤
      (∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) *
        ∏ p ∈ m.primeFactors, (1 + (p : ℝ) ^ (-(1 - 2 * δ))) := by
  exact HardyTheorem.norm_conreyCoprimeEulerInverse_le m hδ hδ16 hz

#print axioms HardyTheorem.one_le_conreyEulerCorrectionConstant
#print axioms HardyTheorem.norm_conreyCoprimeEulerInverse_le
