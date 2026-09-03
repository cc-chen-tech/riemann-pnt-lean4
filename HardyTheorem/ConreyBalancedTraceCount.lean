import HardyTheorem.ConreyBalancedGlobalCount
import MathlibAux.ContinuousLogDerivative
import MathlibAux.FiniteZeroComponentIntegral

/-!
# Actual eta simple-zero counting from a regularized real trace

This identifies the balanced component sum with a whole-interval integral.
The continuous trace and its agreement with the actual logarithmic derivative
away from eta zeros are explicit hypotheses. Its contour construction and the
half-weight argument principle are not assumed to have been completed.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators Interval

namespace HardyTheorem

/-- A continuous extension of the actual eta logarithmic-derivative real trace
gives a finite set of genuine zeta simple zeros with the balanced integral lower
bound. No phase, partition, or component-count hypothesis is supplied. -/
theorem exists_conreyDegreeOneEta_simpleZero_finset_of_regularized_trace
    {g g0 g1 L U T : ℝ} {q : ℝ → ℝ}
    (hg : g ≠ 0) (hU : 0 ≤ U) (hUT : U < T)
    (hq : ContinuousOn q (Icc U T))
    (htrace : ∀ t ∈ Ioo U T,
      conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0 →
      q t = (logDeriv (conreyDegreeOneEta g g0 g1 L) (conreyCriticalPoint t)).re) :
    ∃ S : Finset ℝ,
      (∫ t in U..T, q t) / Real.pi -
        conreyEtaCriticalZeroMultiplicityMassBetween g g0 g1 L U T - 1 ≤ S.card ∧
      ∀ t ∈ S, t ∈ Ioo U T ∧ riemannZeta (conreyCriticalPoint t) = 0 ∧
        analyticOrderNatAt riemannZeta (conreyCriticalPoint t) = 1 := by
  classical
  obtain ⟨K, hK, b, ell, A, B, S, hgeom, _hbmem, hdisjoint, hcover,
    hell, hexp, hA, hB, hcard, hS⟩ :=
    exists_conreyDegreeOneEta_balanced_global_simpleZero_count hg hU hUT
  have hsub : ∀ i : ↥(insert U K), Ioo (i : ℝ) (b i) ⊆ Ioo U T :=
    fun i => Ioo_subset_Ioo (hgeom i).1 (hgeom i).2.2
  have hcoverK : ∀ t ∈ Ioo U T, t ∉ K ↔ ∃ i : ↥(insert U K), t ∈ Ioo (i : ℝ) (b i) := by
    intro t ht
    rw [← hcover t ht]
    constructor
    · intro htK hz
      exact htK ((hK t).mpr ⟨ht.1, ht.2, hz⟩)
    · intro hz htK
      exact hz ((hK t).mp htK).2.2
  have hpoint : ∀ t : ℝ, (((1 / 2 : ℝ) : ℂ) + I * t) = conreyCriticalPoint t := by
    intro t
    simp [conreyCriticalPoint]
  have hinc : ∀ i : ↥(insert U K), B i - A i = ∫ t in (i : ℝ)..b i, q t := by
    intro i
    apply MathlibAux.continuousLog_phase_increment_eq_integral
      (f := conreyDegreeOneEta g g0 g1 L) (sigma := 1 / 2)
      (hgeom i).2.1 (hell i) _ _
      (hq.mono (Icc_subset_Icc (hgeom i).1 (hgeom i).2.2)) _ (hA i) (hB i)
    · intro t _ht
      exact (analyticAt_conreyDegreeOneEta g g0 g1 L _).differentiableAt
    · intro t ht
      simpa only [hpoint] using hexp i t ht
    · intro t ht
      have hne := (hcover t (hsub i ht)).mpr ⟨i, ht⟩
      simpa only [hpoint] using htrace t (hsub i ht) hne
  have hsum : (∑ i, (B i - A i)) = ∫ t in U..T, q t := by
    calc
      (∑ i, (B i - A i)) = ∑ i : ↥(insert U K), ∫ t in (i : ℝ)..b i, q t :=
        Finset.sum_congr rfl (fun i _hi => hinc i)
      _ = ∫ t in U..T, q t :=
        MathlibAux.sum_intervalIntegral_eq_of_finite_complement hUT hgeom hdisjoint hcoverK hq
  refine ⟨S, ?_, hS⟩
  rwa [hsum] at hcard

end HardyTheorem
