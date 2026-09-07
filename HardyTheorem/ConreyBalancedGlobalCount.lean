import HardyTheorem.ConreyComponentSimpleZeros
import MathlibAux.FiniteZeroComponents

/-!
# Actual global balanced-argument count

All open eta components on `(U,T)` are constructed from the actual finite
zero set. Their count is paid for by the actual `(U,T]` multiplicity mass.
The output includes logarithms, finite phase limits, and real zeta simple
zeros. A contour identification of the balanced sum is not assumed or proved.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace HardyTheorem

/-- The complete finite counting layer for actual eta: construct the exact
interior zero set, every complementary component, all phase endpoints and
simple-zero witnesses, charging the actual eta-zero multiplicity mass once.
Endpoint zeros are allowed here; corner corrections for a contour theorem
are a separate question. -/
theorem exists_conreyDegreeOneEta_balanced_global_simpleZero_count
    {g g0 g1 L U T : ℝ} (hg : g ≠ 0) (hU : 0 ≤ U) (hUT : U < T) :
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
  classical
  let Z := conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T
  let K := Z.filter (fun t => t < T)
  have hKmem : ∀ t, t ∈ K ↔ U < t ∧ t < T ∧
      conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) = 0 := by
    intro t
    simp only [K, Z, Finset.mem_filter,
      mem_conreyEtaCriticalZeroOrdinatesBetween hg hU]
    constructor
    · rintro ⟨⟨hUt, _, hz⟩, htT⟩
      exact ⟨hUt, htT, hz⟩
    · rintro ⟨hUt, htT, hz⟩
      exact ⟨⟨hUt, htT.le, hz⟩, htT⟩
  have hKinside : ∀ t ∈ K, t ∈ Ioo U T :=
    fun t ht => ⟨((hKmem t).mp ht).1, ((hKmem t).mp ht).2.1⟩
  obtain ⟨b, hgeom, hbmem, hgap, hdisjoint, hcover⟩ :=
    MathlibAux.exists_finite_zero_complement_components hUT hKinside
  have hsubinterval : ∀ i : ↥(insert U K), Ioo (i : ℝ) (b i) ⊆ Ioo U T :=
    fun i => Ioo_subset_Ioo (hgeom i).1 (hgeom i).2.2
  have hne : ∀ i : ↥(insert U K), ∀ t ∈ Ioo (i : ℝ) (b i),
      conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0 := by
    intro i t ht hz
    have htUT := hsubinterval i ht
    exact hgap i t ht ((hKmem t).mpr ⟨htUT.1, htUT.2, hz⟩)
  have hmassZ : Z.card ≤ conreyEtaCriticalZeroMultiplicityMassBetween g g0 g1 L U T := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro t ht
    exact conreyEtaCriticalZeroOrderNat_pos_of_mem_sortedBetween hg
      (mem_conreyEtaCriticalZeroOrdinatesSortedBetween.mpr ht)
  have hmassK : K.card ≤ conreyEtaCriticalZeroMultiplicityMassBetween g g0 g1 L U T :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans hmassZ
  have hUout : U ∉ K := fun h => (lt_irrefl U) (hKinside U h).1
  have hcomponents : Fintype.card ↥(insert U K) ≤
      conreyEtaCriticalZeroMultiplicityMassBetween g g0 g1 L U T + 1 := by
    rw [Fintype.card_coe, Finset.card_insert_of_notMem hUout]
    exact Nat.add_le_add_right hmassK 1
  obtain ⟨ell, A, B, S, hell, hexp, hA, hB, hcard, hS⟩ :=
    exists_conreyDegreeOneEta_simpleZero_finset_of_components hg
      (fun i => (hgeom i).2.1) hne hdisjoint hcomponents
  refine ⟨K, hKmem, b, ell, A, B, S, hgeom, hbmem, hdisjoint, ?_,
    hell, hexp, hA, hB, hcard, ?_⟩
  · intro t ht
    rw [← hcover t ht]
    constructor
    · intro hz htK
      exact hz ((hKmem t).mp htK).2.2
    · intro htK hz
      exact htK ((hKmem t).mpr ⟨ht.1, ht.2, hz⟩)
  · intro t ht
    obtain ⟨⟨i, hi⟩, hz, horder⟩ := hS t ht
    exact ⟨hsubinterval i hi, hz, horder⟩

end HardyTheorem
