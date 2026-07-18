import PrimeNumberTheorem.GlobalZeroCount

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ZeroDensity

/-- Nontrivial zeta zeros above the real threshold `sigma`, with positive
ordinate at most `T`.  The finset stores distinct zeros; multiplicity is
applied by `zeroDensityCount`. -/
noncomputable def zeroDensityZerosFinset (sigma T : ℝ) : Finset ℂ :=
  (nontrivialZerosFinset T).filter fun rho : ℂ =>
    0 < rho.im ∧ sigma < rho.re

lemma mem_zeroDensityZerosFinset {rho : ℂ} {sigma T : ℝ} :
    rho ∈ zeroDensityZerosFinset sigma T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧
        0 < rho.im ∧ rho.im ≤ T ∧ sigma < rho.re := by
  simp only [zeroDensityZerosFinset, Finset.mem_filter,
    mem_nontrivialZerosFinset]
  constructor
  · rintro ⟨⟨hzero, hheight⟩, him, hre⟩
    exact ⟨hzero, him, by simpa [abs_of_pos him] using hheight, hre⟩
  · rintro ⟨hzero, him, hheight, hre⟩
    exact ⟨⟨hzero, by simpa [abs_of_pos him] using hheight⟩, him, hre⟩

/-- Number of nontrivial zeta zeros with `0 < Im rho ≤ T` and
`sigma < Re rho`, counted with analytic multiplicity. -/
noncomputable def zeroDensityCount (sigma T : ℝ) : ℕ :=
  ∑ rho ∈ zeroDensityZerosFinset sigma T,
    analyticOrderNatAt riemannZeta rho

private lemma zeroDensityZerosFinset_subset_height
    {sigma T U : ℝ} (hTU : T ≤ U) :
    zeroDensityZerosFinset sigma T ⊆ zeroDensityZerosFinset sigma U := by
  intro rho hrho
  rcases mem_zeroDensityZerosFinset.mp hrho with
    ⟨hzero, him, hheight, hre⟩
  exact mem_zeroDensityZerosFinset.mpr
    ⟨hzero, him, hheight.trans hTU, hre⟩

theorem zeroDensityCount_mono_height
    {sigma T U : ℝ} (hTU : T ≤ U) :
    zeroDensityCount sigma T ≤ zeroDensityCount sigma U := by
  unfold zeroDensityCount
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (zeroDensityZerosFinset_subset_height hTU)
    (fun _ _ _ => Nat.zero_le _)

private lemma zeroDensityZerosFinset_subset_re
    {sigma tau T : ℝ} (hst : sigma ≤ tau) :
    zeroDensityZerosFinset tau T ⊆ zeroDensityZerosFinset sigma T := by
  intro rho hrho
  rcases mem_zeroDensityZerosFinset.mp hrho with
    ⟨hzero, him, hheight, hre⟩
  exact mem_zeroDensityZerosFinset.mpr
    ⟨hzero, him, hheight, lt_of_le_of_lt hst hre⟩

theorem zeroDensityCount_antitone_re
    {sigma tau T : ℝ} (hst : sigma ≤ tau) :
    zeroDensityCount tau T ≤ zeroDensityCount sigma T := by
  unfold zeroDensityCount
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (zeroDensityZerosFinset_subset_re hst)
    (fun _ _ _ => Nat.zero_le _)

theorem zeroDensityCount_le_globalZeroMultiplicity (sigma T : ℝ) :
    (zeroDensityCount sigma T : ℝ) ≤
      ExplicitFormulaAux.globalZeroMultiplicity T := by
  calc
    (zeroDensityCount sigma T : ℝ) =
        ∑ rho ∈ zeroDensityZerosFinset sigma T,
          (analyticOrderNatAt riemannZeta rho : ℝ) := by
            simp [zeroDensityCount]
    _ ≤ ∑ rho ∈ nontrivialZerosFinset T,
          (analyticOrderNatAt riemannZeta rho : ℝ) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _)
              (fun _ _ _ => Nat.cast_nonneg _)
    _ = ExplicitFormulaAux.globalZeroMultiplicity T := rfl

theorem zeroDensityCount_eq_zero_of_nonpos_height
    {sigma T : ℝ} (hT : T ≤ 0) :
    zeroDensityCount sigma T = 0 := by
  have hempty : zeroDensityZerosFinset sigma T = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    rcases hnonempty with ⟨rho, hrho⟩
    rcases mem_zeroDensityZerosFinset.mp hrho with
      ⟨_hzero, him, hheight, _hre⟩
    linarith
  simp [zeroDensityCount, hempty]

end ZeroDensity
end PrimeNumberTheorem
