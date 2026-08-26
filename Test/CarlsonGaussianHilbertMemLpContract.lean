import PrimeNumberTheorem.CarlsonGaussianHilbertMemLp

open Complex MeasureTheory
open scoped ENNReal MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable (fun t : ℝ =>
      (1 + |t|) ^ n * Real.exp (-b * t ^ 2)) :=
  integrable_one_add_abs_pow_mul_exp_neg_mul_sq hb n

example {Delta w x C c : ℝ} (hDelta : 0 < Delta)
    (hc : c < 1 / Delta ^ 2) (H : ℂ → ℂ)
    (hHcont : Continuous fun t : ℝ => H ((x : ℂ) + I * (t : ℂ)))
    (hHbound : ∀ t : ℝ,
      ‖H ((x : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
        C * Real.exp (c * (t - w) ^ 2)) :
    MemLp (carlsonGaussianHilbertSection Delta w H (x : ℂ)) 2 volume :=
  memLp_carlsonGaussianHilbertSection_of_exp_sq_bound
    hDelta hc H hHcont hHbound

example {Delta w x C : ℝ} (hDelta : 0 < Delta) (n : ℕ)
    (H : ℂ → ℂ)
    (hHcont : Continuous fun t : ℝ => H ((x : ℂ) + I * (t : ℂ)))
    (hHbound : ∀ t : ℝ,
      ‖H ((x : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
        C * (1 + |t - w|) ^ n) :
    MemLp (carlsonGaussianHilbertSection Delta w H (x : ℂ)) 2 volume :=
  memLp_carlsonGaussianHilbertSection_of_polynomial_sq_bound
    hDelta n H hHcont hHbound

#print axioms integrable_one_add_abs_pow_mul_exp_neg_mul_sq
#print axioms memLp_carlsonGaussianHilbertSection_of_exp_sq_bound
#print axioms memLp_carlsonGaussianHilbertSection_of_polynomial_sq_bound

end CarlsonZeroDensity
end PrimeNumberTheorem
