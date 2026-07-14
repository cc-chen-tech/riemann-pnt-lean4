import PrimeNumberTheorem.LeftHorizontalEdge

open Complex MeasureTheory
open scoped Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

example {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a T : ℝ}, a ≤ -ε → 1 ≤ |T| →
      IntervalIntegrable
          (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + T * I))
          MeasureTheory.volume a (-ε) ∧
        ‖∫ σ : ℝ in a..(-ε),
            explicitFormulaIntegrand x ((σ : ℂ) + T * I)‖ ≤
          C * (1 + Real.log (1 + |T|)) / |T| :=
  exists_norm_integral_farLeft_explicit_le_log_div hx hε

end ExplicitFormulaResidues
end PrimeNumberTheorem
