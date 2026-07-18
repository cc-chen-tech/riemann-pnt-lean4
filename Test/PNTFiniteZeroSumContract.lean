import PrimeNumberTheorem.PNTFiniteZeroSum

namespace PrimeNumberTheorem
namespace ExplicitFormulaAux

example :
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧ ∀ x T : ℝ, 1 < x → 4 ≤ T →
      ‖finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
        C * x ^ (1 - b / Real.log (T + 6)) *
          (1 + Real.log (T + 6)) ^ 2 :=
  exists_norm_finiteNontrivialZeroSumWithMultiplicity_le_zeroFree_mul_log_sq

example :
    (fun m : ℕ => chebyshevPsi0 (m : ℝ) - (m : ℝ))
      =o[Filter.atTop] (fun m : ℕ => (m : ℝ)) :=
  chebyshevPsi0_sub_id_nat_isLittleO

end ExplicitFormulaAux
end PrimeNumberTheorem
