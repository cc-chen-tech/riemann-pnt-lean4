import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCarlsonMovingTail

namespace PrimeNumberTheorem

open Filter Topology
open scoped BigOperators

example (mass : ℕ → ℝ) (N : ℕ) :
    summableNatTail mass N =
      (∑' n : ℕ, mass n) - ∑ n ∈ Finset.range N, mass n := rfl

example {mass : ℕ → ℝ} (hmass : Summable mass) :
    Tendsto (summableNatTail mass) atTop (nhds 0) :=
  PrimeNumberTheorem.Summable.tendsto_summableNatTail_zero hmass

example (x sigma tau : ℝ) (S : Finset ℂ) (N : ℕ) :
    actualCubicDyadicStripSquareCapacityExcludingTail x sigma tau S N =
      summableNatTail
        (fun n =>
          actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S) N := rfl

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {x tau : ℝ} (hx : 1 ≤ x) (S : Finset ℂ) :
    Tendsto
      (actualCubicDyadicStripSquareCapacityExcludingTail x sigma tau S)
      atTop (nhds 0) :=
  certificate.tendsto_actualCubicDyadicStripSquareCapacityExcludingTail_zero
    hx S

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {x tau : ℝ} (hx : 1 ≤ x) (S : Finset ℂ)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto
      (fun m =>
        actualCubicDyadicStripSquareCapacityExcludingTail
          x sigma tau S (N m))
      atTop (nhds 0) :=
  certificate.tendsto_actualCubicDyadicStripSquareCapacityExcludingTail_comp_zero
    hx S hN

end PrimeNumberTheorem
