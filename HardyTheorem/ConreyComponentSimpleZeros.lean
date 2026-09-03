import HardyTheorem.ConreyArgumentEndpoints
import MathlibAux.ArgumentCrossingOpen

/-!
# Actual zeta simple-zero witnesses from eta component phases

The hypotheses only supply finitely many disjoint zero-free eta intervals
and a component-count budget. All logarithms and finite phase limits are
constructed, and the resulting witness set consists of actual simple zeros
of zeta. Identifying the balanced phase sum by a contour formula is separate.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace HardyTheorem

/-- Actual zero-free eta components supply finite, distinct zeta simple-zero
witnesses. No endpoint phase-limit assumption is left to the caller. -/
theorem exists_conreyDegreeOneEta_simpleZero_finset_of_components
    {ι : Type*} [Fintype ι] {g g0 g1 L : ℝ} {a b : ι → ℝ} {M : ℕ}
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
  classical
  have hlocal := fun i => exists_conreyDegreeOneEta_continuousLog_with_argument_limits
    hg (hab i) (hne i)
  choose ell A B hell hexp hleft hright using hlocal
  obtain ⟨S, hcard, hS⟩ := MathlibAux.exists_finset_argumentCrossings_of_disjoint_components
    hab hell hexp hleft hright hdisjoint hcomponents
  refine ⟨ell, A, B, S, hell, hexp, hleft, hright, hcard, ?_⟩
  intro t ht
  obtain ⟨hi, hre, hnonzero⟩ := hS t ht
  exact ⟨hi, conreyDegreeOneEta_simple_zero_of_re_eq_zero_of_ne_zero hg hre hnonzero⟩

end HardyTheorem
