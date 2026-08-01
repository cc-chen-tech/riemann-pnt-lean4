import MathlibAux.CollectedExponentialPolynomial
import MathlibAux.FiberwiseNormSq

/-!
# Energy bounds for coefficients collected by frequency

Finite Cauchy--Schwarz bounds the square energy of coefficients after equal
frequencies have been combined.  This generic result keeps the exact
frequency-fiber multiplicities visible for later arithmetic estimates.
-/

open Complex
open scoped BigOperators

namespace MathlibAux

/-- Collecting coefficients by a finite frequency map costs the exact
fiberwise Cauchy--Schwarz multiplicity budget. -/
theorem sum_normSq_collectedCoefficient_le_fiber_budget
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) :
    (∑ omega ∈ collectedFrequencySupport s freq,
        Complex.normSq (collectedCoefficient s coeff freq omega)) ≤
      ∑ omega ∈ collectedFrequencySupport s freq,
        ((s.filter (fun i => freq i = omega)).card : ℝ) *
          ∑ i ∈ s.filter (fun i => freq i = omega),
            Complex.normSq (coeff i) := by
  exact sum_normSq_fiber_le_sum_card_mul_normSq
    s (collectedFrequencySupport s freq) freq coeff
    (by
      intro i hi
      exact Finset.mem_image_of_mem freq hi)

end MathlibAux
