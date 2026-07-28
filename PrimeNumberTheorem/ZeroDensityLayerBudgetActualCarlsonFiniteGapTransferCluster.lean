import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryMassFiniteGapCapture
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualFullTailExcludingClusterConjugation

/-!
# Finite Carlson transfer clusters

Starting from a finite cluster that captures enough Carlson boundary mass, we
adjoin the fixed finite set of real-ordinate nontrivial zeros.  This preserves
conjugation invariance, can only decrease boundary mass, and makes the
real-ordinate complement empty.  Under a global upper bound `Re rho <= beta`,
the resulting finite cluster satisfies every structural zero condition used by
the balanced Carlson PNT transfer.
-/

namespace PrimeNumberTheorem

noncomputable section

/-- Enlarge a visible cluster by all fixed real-ordinate nontrivial zeros. -/
def actualCarlsonAdjoinRealOrdinateZeros (S : Finset ℂ) : Finset ℂ :=
  S ∪ realOrdinateNontrivialZerosFinset 0

theorem conj_eq_self_of_mem_realOrdinateNontrivialZerosFinset
    {rho : ℂ}
    (hrho : rho ∈ realOrdinateNontrivialZerosFinset 0) :
    (starRingEnd ℂ) rho = rho := by
  exact
    Complex.conj_eq_iff_im.mpr
      (mem_realOrdinateNontrivialZerosFinset.mp hrho).2

/-- Adjoining all real-ordinate zeros preserves conjugation stability. -/
theorem actualCarlsonAdjoinRealOrdinateZeros_conjugationStable
    (S : Finset ℂ)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) :
    ∀ rho : ℂ,
      rho ∈ actualCarlsonAdjoinRealOrdinateZeros S ↔
        (starRingEnd ℂ) rho ∈
          actualCarlsonAdjoinRealOrdinateZeros S := by
  classical
  intro rho
  constructor
  · intro hrho
    rcases Finset.mem_union.mp hrho with hrhoS | hrhoReal
    · exact Finset.mem_union_left _ ((hS rho).mp hrhoS)
    · have hfixed :=
        conj_eq_self_of_mem_realOrdinateNontrivialZerosFinset hrhoReal
      rw [hfixed]
      exact Finset.mem_union_right _ hrhoReal
  · intro hrho
    rcases Finset.mem_union.mp hrho with hrhoS | hrhoReal
    · exact Finset.mem_union_left _ ((hS rho).mpr hrhoS)
    · have hfixed :=
        conj_eq_self_of_mem_realOrdinateNontrivialZerosFinset hrhoReal
      have hrhoEq : rho = (starRingEnd ℂ) rho := by
        simpa using hfixed
      rw [hrhoEq]
      exact Finset.mem_union_right _ hrhoReal

/-- After adjoining all fixed real-ordinate zeros, their outside-cluster
residual is empty. -/
theorem realOrdinateNontrivialZerosOutsideClusterFinset_adjoin_eq_empty
    (S : Finset ℂ) :
    realOrdinateNontrivialZerosOutsideClusterFinset 0
        (actualCarlsonAdjoinRealOrdinateZeros S) = ∅ := by
  classical
  unfold realOrdinateNontrivialZerosOutsideClusterFinset
  unfold actualCarlsonAdjoinRealOrdinateZeros
  ext rho
  constructor
  · intro hrho
    rcases Finset.mem_sdiff.mp hrho with ⟨hrhoReal, hrhoNot⟩
    exfalso
    exact hrhoNot (Finset.mem_union_right S hrhoReal)
  · intro hrho
    simpa using hrho

/-- Adjoining the real-ordinate finite residual can only decrease the outside
Carlson boundary mass. -/
theorem actualCarlsonOutsideClusterBoundaryMass_adjoinRealOrdinate_le
    {sigma beta : ℝ} (S : Finset ℂ)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta
        (actualCarlsonAdjoinRealOrdinateZeros S) ≤
      actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S := by
  apply actualCarlsonOutsideClusterBoundaryMass_antitone hhalf hone
  intro rho hrho
  exact Finset.mem_union_left _ hrho

/-- For every strict coefficient gap `q < c`, a global bound
`Re rho <= beta` yields a finite cluster satisfying all structural assumptions
of the balanced Carlson boundary transfer. -/
theorem exists_actualCarlsonFiniteGapTransferCluster
    {sigma beta c q : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hqC : q < c)
    (hre :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta) :
    ∃ S : Finset ℂ,
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      (∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta) ∧
      (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < c - q := by
  obtain ⟨S, hS, hgap⟩ :=
    exists_conjugationStable_actualCarlsonOutsideClusterBoundaryMass_two_mul_lt_gap
      (beta := beta) hhalf hone hqC
  let T := actualCarlsonAdjoinRealOrdinateZeros S
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · exact actualCarlsonAdjoinRealOrdinateZeros_conjugationStable S hS
  · intro index _
    exact hre index
  · intro rho hrho
    have hempty :
        realOrdinateNontrivialZerosOutsideClusterFinset 0 T = ∅ :=
      realOrdinateNontrivialZerosOutsideClusterFinset_adjoin_eq_empty S
    rw [hempty] at hrho
    simp at hrho
  · have hmass :=
      actualCarlsonOutsideClusterBoundaryMass_adjoinRealOrdinate_le
        (beta := beta) S hhalf hone
    exact (mul_le_mul_of_nonneg_left hmass zero_le_two).trans_lt hgap

end

end PrimeNumberTheorem
