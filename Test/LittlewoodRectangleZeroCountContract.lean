import PrimeNumberTheorem.LittlewoodRectangleZeroCount

set_option autoImplicit false

open Complex Set
open scoped BigOperators
open PrimeNumberTheorem.CarlsonZeroDensity

example {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ} (hx : x0 ≤ x1) (hy : y0 ≤ y1)
    (poles : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hf : AnalyticOnNhd ℂ f (Icc x0 x1 ×ℂ Icc y0 y1))
    (hzero : ∀ z ∈ (Icc x0 x1 ×ℂ Icc y0 y1 : Set ℂ), f z = 0 ↔ z ∈ poles)
    (horder : ∀ z ∈ poles, analyticOrderAt f z = multiplicity z)
    (hinterior : ∀ z ∈ poles, x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) :
    (2 * Real.pi) * ∑ z ∈ poles, (z.re - x0) * (multiplicity z : ℝ) =
      rectangleLittlewoodLogNormForm f x0 x1 y0 y1 :=
  two_pi_mul_zeroMultiplicityWeightedRealSum_eq_logNormForm hx hy
    poles multiplicity hf hzero horder hinterior

#print axioms two_pi_mul_zeroMultiplicityWeightedRealSum_eq_logNormForm
