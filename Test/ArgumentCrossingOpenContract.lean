import MathlibAux.ArgumentCrossingOpen

open Complex Set Filter Topology
open MathlibAux
open scoped BigOperators

-- Mutation caught: a limiting endpoint level is not an interior crossing.
example {g ell : ℝ → ℂ} {a b alpha beta : ℝ} (hab : a < b)
    (hell : ContinuousOn ell (Ioo a b))
    (hexp : ∀ t ∈ Ioo a b, Complex.exp (ell t) = g t)
    (hleft : Tendsto (fun t => (ell t).im) (nhdsWithin a (Ioi a)) (nhds alpha))
    (hright : Tendsto (fun t => (ell t).im) (nhdsWithin b (Iio b)) (nhds beta))
    {k : ℤ} (hk : argumentCrossingLevel k ∈ Ioo alpha beta) :
    ∃ t ∈ Ioo a b, (ell t).im = argumentCrossingLevel k ∧
      (g t).re = 0 ∧ g t ≠ 0 := by
  exact exists_argumentCrossing_of_oneSided_limits hab hell hexp hleft hright hk

-- Mutation caught: the strict-endpoint lattice count loses at most one,
-- including aligned endpoints and decreasing or empty phase intervals.
example (alpha beta : ℝ) :
    (beta - alpha) / Real.pi - 1 ≤
      (argumentCrossingInteriorIndices alpha beta).card := by
  exact argumentCrossingInteriorIndices_card_lower_bound

-- Mutation caught: per-component losses are paid by the zero mass only for
-- the sum of component variations; no zero jumps are included in this sum.
example {ι : Type*} [Fintype ι] (A B : ι → ℝ) (n : ι → ℕ) (M : ℕ)
    (hlocal : ∀ i, (B i - A i) / Real.pi - 1 ≤ n i)
    (hcomponents : Fintype.card ι ≤ M + 1) :
    (∑ i, (B i - A i)) / Real.pi - M - 1 ≤ ∑ i, (n i : ℝ) := by
  exact argumentCrossing_component_budget hlocal hcomponents

#print axioms exists_argumentCrossing_of_oneSided_limits
#print axioms argumentCrossingInteriorIndices_card_lower_bound
#print axioms argumentCrossing_component_budget

-- Distinct attained phase levels must give distinct actual interior points.
example {g ell : ℝ → ℂ} {a b alpha beta : ℝ} (hab : a < b)
    (hell : ContinuousOn ell (Ioo a b))
    (hexp : ∀ t ∈ Ioo a b, Complex.exp (ell t) = g t)
    (hleft : Tendsto (fun t => (ell t).im) (nhdsWithin a (Ioi a)) (nhds alpha))
    (hright : Tendsto (fun t => (ell t).im) (nhdsWithin b (Iio b)) (nhds beta)) :
    ∃ S : Finset ℝ, (beta - alpha) / Real.pi - 1 ≤ S.card ∧
      ∀ t ∈ S, t ∈ Ioo a b ∧ (g t).re = 0 ∧ g t ≠ 0 := by
  exact exists_finset_argumentCrossings_of_oneSided_limits hab hell hexp hleft hright

#print axioms exists_finset_argumentCrossings_of_oneSided_limits

-- The union counts actual real points, not component-tagged duplicates.
example {ι : Type*} [Fintype ι] {g : ℝ → ℂ} {ell : ι → ℝ → ℂ}
    {a b A B : ι → ℝ} {M : ℕ}
    (hab : ∀ i, a i < b i)
    (hell : ∀ i, ContinuousOn (ell i) (Ioo (a i) (b i)))
    (hexp : ∀ i, ∀ t ∈ Ioo (a i) (b i), Complex.exp (ell i t) = g t)
    (hleft : ∀ i, Tendsto (fun t => (ell i t).im)
      (nhdsWithin (a i) (Ioi (a i))) (nhds (A i)))
    (hright : ∀ i, Tendsto (fun t => (ell i t).im)
      (nhdsWithin (b i) (Iio (b i))) (nhds (B i)))
    (hdisjoint : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hcomponents : Fintype.card ι ≤ M + 1) :
    ∃ S : Finset ℝ,
      (∑ i, (B i - A i)) / Real.pi - M - 1 ≤ S.card ∧
      ∀ t ∈ S, (∃ i, t ∈ Ioo (a i) (b i)) ∧ (g t).re = 0 ∧ g t ≠ 0 := by
  exact exists_finset_argumentCrossings_of_disjoint_components
    hab hell hexp hleft hright hdisjoint hcomponents

#print axioms exists_finset_argumentCrossings_of_disjoint_components
