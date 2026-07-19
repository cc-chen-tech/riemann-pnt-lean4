import PrimeNumberTheorem.NontrivialZeroMultiplicity

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt

noncomputable def positiveNontrivialZerosFinset (T : ℝ) : Finset ℂ :=
  (nontrivialZerosFinset T).filter fun rho : ℂ => 0 < rho.im

lemma mem_positiveNontrivialZerosFinset {rho : ℂ} {T : ℝ} :
    rho ∈ positiveNontrivialZerosFinset T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧ 0 < rho.im ∧ rho.im ≤ T := by
  simp only [positiveNontrivialZerosFinset, Finset.mem_filter,
    mem_nontrivialZerosFinset]
  constructor
  · rintro ⟨⟨hzero, hheight⟩, him⟩
    exact ⟨hzero, him, by simpa [abs_of_pos him] using hheight⟩
  · rintro ⟨hzero, him, hheight⟩
    exact ⟨⟨hzero, by simpa [abs_of_pos him] using hheight⟩, him⟩

lemma positiveNontrivialZerosFinset_subset {U T : ℝ} (hUT : U ≤ T) :
    positiveNontrivialZerosFinset U ⊆ positiveNontrivialZerosFinset T := by
  intro rho hrho
  rcases mem_positiveNontrivialZerosFinset.mp hrho with
    ⟨hzero, him, hheight⟩
  exact mem_positiveNontrivialZerosFinset.mpr
    ⟨hzero, him, hheight.trans hUT⟩

noncomputable def positiveNontrivialZerosBetween (U T : ℝ) : Finset ℂ :=
  positiveNontrivialZerosFinset T \ positiveNontrivialZerosFinset U

lemma mem_positiveNontrivialZerosBetween {rho : ℂ} {U T : ℝ} (hU : 0 ≤ U) :
    rho ∈ positiveNontrivialZerosBetween U T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧ U < rho.im ∧ rho.im ≤ T := by
  constructor
  · intro hrho
    rcases Finset.mem_sdiff.mp hrho with ⟨hrhoT, hrhoU⟩
    rcases mem_positiveNontrivialZerosFinset.mp hrhoT with
      ⟨hzero, him, hheightT⟩
    have hheightU : U < rho.im := by
      by_contra hnot
      exact hrhoU (mem_positiveNontrivialZerosFinset.mpr
        ⟨hzero, him, le_of_not_gt hnot⟩)
    exact ⟨hzero, hheightU, hheightT⟩
  · rintro ⟨hzero, hheightU, hheightT⟩
    have him : 0 < rho.im := lt_of_le_of_lt hU hheightU
    apply Finset.mem_sdiff.mpr
    exact ⟨mem_positiveNontrivialZerosFinset.mpr
      ⟨hzero, him, hheightT⟩, by
        intro hrhoU
        exact (not_le_of_gt hheightU)
          (mem_positiveNontrivialZerosFinset.mp hrhoU).2.2⟩

noncomputable def riemannZeroCount (T : ℝ) : ℕ :=
  ∑ rho ∈ positiveNontrivialZerosFinset T,
    analyticOrderNatAt riemannZeta rho

lemma riemannZeroCount_nonneg (T : ℝ) : 0 ≤ riemannZeroCount T :=
  Nat.zero_le _

theorem riemannZeroCount_add_between {U T : ℝ} (hUT : U ≤ T) :
    riemannZeroCount U +
        ∑ rho ∈ positiveNontrivialZerosBetween U T,
          analyticOrderNatAt riemannZeta rho =
      riemannZeroCount T := by
  classical
  have hsubset := positiveNontrivialZerosFinset_subset hUT
  unfold riemannZeroCount positiveNontrivialZerosBetween
  rw [add_comm]
  exact Finset.sum_sdiff hsubset

theorem riemannZeroCount_mono {U T : ℝ} (hUT : U ≤ T) :
    riemannZeroCount U ≤ riemannZeroCount T := by
  have hsplit := riemannZeroCount_add_between hUT
  omega

theorem riemannZeroCount_sub_eq_between {U T : ℝ} (hUT : U ≤ T) :
    riemannZeroCount T - riemannZeroCount U =
      ∑ rho ∈ positiveNontrivialZerosBetween U T,
        analyticOrderNatAt riemannZeta rho := by
  have hsplit := riemannZeroCount_add_between hUT
  omega

end RiemannVonMangoldt
end PrimeNumberTheorem
