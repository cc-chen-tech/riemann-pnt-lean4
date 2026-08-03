import MathlibAux.CollectedCoefficientEnergy

open Complex
open scoped BigOperators

namespace MathlibAux

/-!
# Contract for collected coefficient energy
-/

#check sum_normSq_collectedCoefficient_le_fiber_budget

example {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) :
    (∑ omega ∈ collectedFrequencySupport s freq,
        Complex.normSq (collectedCoefficient s coeff freq omega)) ≤
      ∑ omega ∈ collectedFrequencySupport s freq,
        ((s.filter (fun i => freq i = omega)).card : ℝ) *
          ∑ i ∈ s.filter (fun i => freq i = omega),
            Complex.normSq (coeff i) :=
  sum_normSq_collectedCoefficient_le_fiber_budget s coeff freq

end MathlibAux
