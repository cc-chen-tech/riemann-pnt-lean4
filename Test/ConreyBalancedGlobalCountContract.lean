import HardyTheorem.ConreyBalancedGlobalCount

open Complex Set Filter Topology
open scoped BigOperators
open HardyTheorem

-- No supplied phase data, zero list, partition or component-count bound:
-- everything is constructed for actual eta on the whole interval (U,T).
example {g g0 g1 L U T : ℝ} (hg : g ≠ 0) (hU : 0 ≤ U) (hUT : U < T) :
    ∃ K : Finset ℝ,
      (∀ t, t ∈ K ↔ U < t ∧ t < T ∧
        conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) = 0) ∧
      ∃ b : ↥(insert U K) → ℝ, ∃ ell : ↥(insert U K) → ℝ → ℂ,
      ∃ A B : ↥(insert U K) → ℝ, ∃ S : Finset ℝ,
        (∀ i : ↥(insert U K), U ≤ (i : ℝ) ∧ (i : ℝ) < b i ∧ b i ≤ T) ∧
        (∀ i, b i ∈ insert T K) ∧
        Pairwise (fun (i j : ↥(insert U K)) =>
          Disjoint (Ioo (i : ℝ) (b i)) (Ioo (j : ℝ) (b j))) ∧
        (∀ t ∈ Ioo U T,
          conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0 ↔
          ∃ i : ↥(insert U K), t ∈ Ioo (i : ℝ) (b i)) ∧
        (∀ i : ↥(insert U K), ContinuousOn (ell i) (Ioo (i : ℝ) (b i))) ∧
        (∀ i : ↥(insert U K), ∀ t ∈ Ioo (i : ℝ) (b i), Complex.exp (ell i t) =
          conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t)) ∧
        (∀ i : ↥(insert U K), Tendsto (fun t => (ell i t).im)
          (nhdsWithin (i : ℝ) (Ioi (i : ℝ))) (nhds (A i))) ∧
        (∀ i, Tendsto (fun t => (ell i t).im)
          (nhdsWithin (b i) (Iio (b i))) (nhds (B i))) ∧
        (∑ i, (B i - A i)) / Real.pi -
          conreyEtaCriticalZeroMultiplicityMassBetween g g0 g1 L U T - 1 ≤ S.card ∧
        ∀ t ∈ S, t ∈ Ioo U T ∧ riemannZeta (conreyCriticalPoint t) = 0 ∧
          analyticOrderNatAt riemannZeta (conreyCriticalPoint t) = 1 := by
  exact exists_conreyDegreeOneEta_balanced_global_simpleZero_count hg hU hUT

#print axioms exists_conreyDegreeOneEta_balanced_global_simpleZero_count
