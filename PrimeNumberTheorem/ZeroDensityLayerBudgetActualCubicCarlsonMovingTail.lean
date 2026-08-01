import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCarlsonCertificateSummability

/-!
# Moving tails of actual cubic Carlson block capacities

Summability is converted into a tail tending to zero, first for an arbitrary
natural-indexed real sequence and then for the actual deleted-set cubic zeta
capacity.  A final composition theorem accepts any moving dyadic cut tending
to infinity.
-/

namespace PrimeNumberTheorem

open Filter Topology
open scoped BigOperators

/-- Tail of a natural-indexed series, represented as the total sum minus its
finite prefix. -/
noncomputable def summableNatTail (mass : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑' n : ℕ, mass n) - ∑ n ∈ Finset.range N, mass n

/-- Every summable natural-indexed real series has vanishing tails. -/
theorem Summable.tendsto_summableNatTail_zero
    {mass : ℕ → ℝ} (hmass : Summable mass) :
    Tendsto (summableNatTail mass) atTop (nhds 0) := by
  have hpartial := hmass.tendsto_sum_tsum_nat
  have hconst : Tendsto (fun _ : ℕ => ∑' n : ℕ, mass n) atTop
      (nhds (∑' n : ℕ, mass n)) := tendsto_const_nhds
  simpa [summableNatTail] using (hconst.sub hpartial)

/-- The actual cubic coefficient-square tail after deleting a finite set. -/
noncomputable def actualCubicDyadicStripSquareCapacityExcludingTail
    (x sigma tau : ℝ) (S : Finset ℂ) (N : ℕ) : ℝ :=
  summableNatTail
    (fun n => actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S) N

/-- A Carlson certificate makes the genuine deleted-set actual cubic capacity
tail tend to zero. -/
theorem CarlsonEventualMajorant.tendsto_actualCubicDyadicStripSquareCapacityExcludingTail_zero
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {x tau : ℝ} (hx : 1 ≤ x) (S : Finset ℂ) :
    Tendsto
      (actualCubicDyadicStripSquareCapacityExcludingTail x sigma tau S)
      atTop (nhds 0) := by
  exact Summable.tendsto_summableNatTail_zero
    (certificate.summable_actualCubicDyadicStripSquareCapacityExcluding
      (tau := tau) hx S)

/-- Any moving dyadic cut tending to infinity inherits the vanishing actual
cubic capacity tail. -/
theorem CarlsonEventualMajorant.tendsto_actualCubicDyadicStripSquareCapacityExcludingTail_comp_zero
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {x tau : ℝ} (hx : 1 ≤ x) (S : Finset ℂ)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto
      (fun m =>
        actualCubicDyadicStripSquareCapacityExcludingTail
          x sigma tau S (N m))
      atTop (nhds 0) := by
  exact
    (certificate.tendsto_actualCubicDyadicStripSquareCapacityExcludingTail_zero
      hx S).comp hN

end PrimeNumberTheorem
