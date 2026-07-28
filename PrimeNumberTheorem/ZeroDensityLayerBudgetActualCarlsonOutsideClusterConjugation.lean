import PrimeNumberTheorem.ZeroDensityLayerBudgetPositiveZeroConjugation
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonDynamicTruncatedDecay

/-!
# Conjugation transfer outside a finite cluster

The existing positive/negative zero decomposition is reused by assigning zero
to every member of a conjugation-stable main cluster.  This yields the factor
two transfer from the positive outside-cluster sum to the full nonreal
outside-cluster sum while retaining the real-ordinate residual explicitly.
-/

namespace PrimeNumberTheorem

open scoped BigOperators Topology
open Filter Complex

noncomputable section

def pntRelativeZeroContributionOutsideCluster
    (x : ℝ) (S : Finset ℂ) (rho : ℂ) : ℂ :=
  if rho ∈ S then 0 else pntRelativeZeroContribution x rho

theorem sum_pntRelativeZeroContributionOutsideCluster
    (A S : Finset ℂ) (x : ℝ) :
    (∑ rho ∈ A,
      pntRelativeZeroContributionOutsideCluster x S rho) =
      ∑ rho ∈ A \ S, pntRelativeZeroContribution x rho := by
  rw [show A \ S = A.filter (fun rho => rho ∉ S) by
    ext rho
    simp]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hmem : rho ∈ S <;>
    simp [pntRelativeZeroContributionOutsideCluster, hmem]

theorem pntRelativeZeroContributionOutsideCluster_conj
    {x : ℝ} (hx : 0 < x) {S : Finset ℂ}
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    {rho : ℂ} (hrho : rho ∈ nontrivialZerosFinset x) :
    pntRelativeZeroContributionOutsideCluster x S ((starRingEnd ℂ) rho) =
      (starRingEnd ℂ)
        (pntRelativeZeroContributionOutsideCluster x S rho) := by
  have hz : RiemannHypothesis.IsNontrivialZero rho :=
    (mem_nontrivialZerosFinset.mp hrho).1
  by_cases hmem : rho ∈ S
  · have hconj : (starRingEnd ℂ) rho ∈ S := (hS rho).mp hmem
    simp [pntRelativeZeroContributionOutsideCluster, hmem, hconj]
  · have hconj : (starRingEnd ℂ) rho ∉ S := by
      intro hc
      exact hmem ((hS rho).mpr hc)
    simp only [pntRelativeZeroContributionOutsideCluster,
      hmem, hconj, if_false]
    exact pntRelativeZeroContribution_conj hx hz

/-- Full outside-cluster zero sum versus the positive outside-cluster sum.
The real-ordinate residual is retained. -/
theorem norm_fullOutsideClusterZeroSum_le_two_mul_positive_add_real
    {T x : ℝ} (hx : 0 < x) (S : Finset ℂ)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) :
    ‖∑ rho ∈ nontrivialZerosOutsideClusterFinset T S,
        pntRelativeZeroContribution x rho‖ ≤
      2 *
          ‖∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
            pntRelativeZeroContribution x rho‖ +
        ‖∑ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset T S,
          pntRelativeZeroContribution x rho‖ := by
  let term := pntRelativeZeroContributionOutsideCluster x S
  have hterm :
      ∀ rho ∈ nontrivialZerosFinset T,
        term ((starRingEnd ℂ) rho) = (starRingEnd ℂ) (term rho) := by
    intro rho hrho
    have hz : RiemannHypothesis.IsNontrivialZero rho :=
      (mem_nontrivialZerosFinset.mp hrho).1
    by_cases hmem : rho ∈ S
    · have hconj : (starRingEnd ℂ) rho ∈ S := (hS rho).mp hmem
      simp [term, pntRelativeZeroContributionOutsideCluster,
        hmem, hconj]
    · have hconj : (starRingEnd ℂ) rho ∉ S := by
        intro hc
        exact hmem ((hS rho).mpr hc)
      simp only [term, pntRelativeZeroContributionOutsideCluster,
        hmem, hconj, if_false]
      exact pntRelativeZeroContribution_conj hx hz
  have hnegative :=
    sum_negative_eq_conj_sum_positive T term hterm
  have hdecomp :=
    finiteZeroSum_eq_positive_add_negative_add_real T term
  have hsum :
      (∑ rho ∈ nontrivialZerosOutsideClusterFinset T S,
          pntRelativeZeroContribution x rho) =
        (∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
          pntRelativeZeroContribution x rho) +
          (starRingEnd ℂ)
            (∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
              pntRelativeZeroContribution x rho) +
          ∑ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset T S,
            pntRelativeZeroContribution x rho := by
    calc
      (∑ rho ∈ nontrivialZerosOutsideClusterFinset T S,
          pntRelativeZeroContribution x rho) =
          ∑ rho ∈ nontrivialZerosFinset T, term rho := by
            symm
            exact sum_pntRelativeZeroContributionOutsideCluster
              (nontrivialZerosFinset T) S x
      _ = (∑ rho ∈ positiveNontrivialZerosFinset T, term rho) +
            (∑ rho ∈ negativeNontrivialZerosFinset T, term rho) +
            ∑ rho ∈ realOrdinateNontrivialZerosFinset T, term rho :=
          hdecomp
      _ = (∑ rho ∈ positiveNontrivialZerosFinset T, term rho) +
            (starRingEnd ℂ)
              (∑ rho ∈ positiveNontrivialZerosFinset T, term rho) +
            ∑ rho ∈ realOrdinateNontrivialZerosFinset T, term rho := by
          rw [hnegative]
      _ = (∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
            pntRelativeZeroContribution x rho) +
            (starRingEnd ℂ)
              (∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
                pntRelativeZeroContribution x rho) +
            ∑ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset T S,
              pntRelativeZeroContribution x rho := by
          rw [sum_pntRelativeZeroContributionOutsideCluster,
            sum_pntRelativeZeroContributionOutsideCluster]
          rfl
  rw [hsum]
  calc
    ‖(∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
          pntRelativeZeroContribution x rho) +
        (starRingEnd ℂ)
          (∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
            pntRelativeZeroContribution x rho) +
        ∑ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset T S,
          pntRelativeZeroContribution x rho‖ ≤
        ‖(∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
            pntRelativeZeroContribution x rho) +
          (starRingEnd ℂ)
            (∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
              pntRelativeZeroContribution x rho)‖ +
        ‖∑ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset T S,
          pntRelativeZeroContribution x rho‖ :=
      norm_add_le _ _
    _ ≤
        (‖∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
            pntRelativeZeroContribution x rho‖ +
          ‖(starRingEnd ℂ)
            (∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
              pntRelativeZeroContribution x rho)‖) +
        ‖∑ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset T S,
          pntRelativeZeroContribution x rho‖ :=
      add_le_add (norm_add_le _ _) (le_refl _)
    _ = 2 *
          ‖∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
            pntRelativeZeroContribution x rho‖ +
        ‖∑ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset T S,
          pntRelativeZeroContribution x rho‖ := by
      have hnormConj :
          ‖(starRingEnd ℂ)
              (∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
                pntRelativeZeroContribution x rho)‖ =
            ‖∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
              pntRelativeZeroContribution x rho‖ := by
        change
          ‖star
              (∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
                pntRelativeZeroContribution x rho)‖ =
            ‖∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
              pntRelativeZeroContribution x rho‖
        exact norm_star _
      rw [hnormConj]
      ring

end

end PrimeNumberTheorem
