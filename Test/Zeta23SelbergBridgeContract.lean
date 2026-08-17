import HardyTheorem.Zeta23SelbergBridge

namespace HardyTheorem
namespace Zeta23SelbergBridge

/-- Contract: the two externally closed targets are now inhabited by
concrete proof terms built from the Zeta23 bridge. -/

example : selberg_odd_zero_proportion_target :=
  selberg_odd_zero_proportion_target_of_zeta23

example : selberg_zero_proportion_target :=
  selberg_zero_proportion_target_of_zeta23

example : KnownResults.conrey_40_percent_zeros_on_critical_line_target :=
  conrey_40_percent_zeros_on_critical_line_target_of_zeta23

/-- The multiplicity and counting alignments used by the bridge. -/

example (ρ : ℂ) : Zeta23.zeroMult ρ = analyticOrderNatAt riemannZeta ρ :=
  zeroMult_eq_analyticOrderNatAt ρ

example {ρ : ℂ} {T : ℝ} :
    ρ ∈ Zeta23.zerosIn 0 T ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ T :=
  mem_zeta23_zerosIn_zero

example (T : ℝ) :
    Zeta23.Ncount 0 T =
      PrimeNumberTheorem.RiemannVonMangoldt.riemannZeroCount T :=
  ncount_zero_eq_riemannZeroCount T

example (T : ℝ) :
    Zeta23.N0simple 0 T ≤ criticalLineOddZeroCount T :=
  n0simple_zero_le_criticalLineOddZeroCount T

end Zeta23SelbergBridge
end HardyTheorem
