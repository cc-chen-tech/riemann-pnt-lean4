import HardyTheorem.ConreyComponentSimpleZeros

open Complex Set Filter Topology
open scoped BigOperators
open HardyTheorem

-- No phase limits are assumed: actual zero-free eta intervals produce the
-- logarithms, limits and distinct actual zeta simple-zero witness points.
example {ι : Type*} [Fintype ι] {g g0 g1 L : ℝ} {a b : ι → ℝ} {M : ℕ}
    (hg : g ≠ 0) (hab : ∀ i, a i < b i)
    (hne : ∀ i, ∀ t ∈ Ioo (a i) (b i),
      conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0)
    (hdisjoint : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hcomponents : Fintype.card ι ≤ M + 1) :
    ∃ ell : ι → ℝ → ℂ, ∃ A B : ι → ℝ, ∃ S : Finset ℝ,
      (∀ i, ContinuousOn (ell i) (Ioo (a i) (b i))) ∧
      (∀ i, ∀ t ∈ Ioo (a i) (b i), Complex.exp (ell i t) =
        conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t)) ∧
      (∀ i, Tendsto (fun t => (ell i t).im)
        (nhdsWithin (a i) (Ioi (a i))) (nhds (A i))) ∧
      (∀ i, Tendsto (fun t => (ell i t).im)
        (nhdsWithin (b i) (Iio (b i))) (nhds (B i))) ∧
      (∑ i, (B i - A i)) / Real.pi - M - 1 ≤ S.card ∧
      ∀ t ∈ S, (∃ i, t ∈ Ioo (a i) (b i)) ∧
        riemannZeta (conreyCriticalPoint t) = 0 ∧
        analyticOrderNatAt riemannZeta (conreyCriticalPoint t) = 1 := by
  exact exists_conreyDegreeOneEta_simpleZero_finset_of_components
    hg hab hne hdisjoint hcomponents

#print axioms exists_conreyDegreeOneEta_simpleZero_finset_of_components
