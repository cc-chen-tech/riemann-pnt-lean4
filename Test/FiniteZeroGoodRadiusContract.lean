import PrimeNumberTheorem.FiniteZeroGoodRadius

open Complex

namespace PrimeNumberTheorem

example
    {f : ℂ → ℂ} (zeros : Finset ℂ) (c : ℂ)
    {a q b : ℝ} (ha : 0 < a) (haq : a < q) (hqb : q < b)
    (hcover : ∀ z ∈ Metric.closedBall c b, f z = 0 → z ∈ zeros) :
    ∃ r : ℝ,
      0 < r ∧ r ∈ Set.Icc a q ∧
      (∀ z ∈ Metric.sphere c r, ∀ ρ ∈ zeros,
        (q - a) / (4 * (((zeros.image (dist c)).card : ℝ) + 1)) ≤ dist z ρ) ∧
      (∀ z ∈ Metric.sphere c r, z ∈ Metric.closedBall c b) ∧
      ∀ z ∈ Metric.sphere c r, f z ≠ 0 :=
  exists_good_radius_avoiding_covered_finset_zeros zeros c ha haq hqb hcover

#print axioms exists_good_radius_avoiding_covered_finset_zeros

end PrimeNumberTheorem
