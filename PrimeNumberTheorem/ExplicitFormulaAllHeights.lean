import PrimeNumberTheorem.CofinalExplicitFormula
import PrimeNumberTheorem.QuantitativeGoodHeight

open Complex Filter Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- If two truncation heights differ by at most three, the change in the
multiplicity-aware explicit-formula approximation is controlled by two of the
fixed-width local zero windows. -/
theorem norm_explicitFormulaApproxWithMultiplicity_sub_le_two_localWindows
    {x T U : ℝ} (hTU : T ≤ U) (hUT : U ≤ T + 3) :
    ‖explicitFormulaApproxWithMultiplicity x T -
        explicitFormulaApproxWithMultiplicity x U‖ ≤
      ExplicitFormulaAux.localZeroContributionNorm x (T + 1 / 4) +
        ExplicitFormulaAux.localZeroContributionNorm x (T + 7 / 4) := by
  classical
  let D := nontrivialZerosFinset U \ nontrivialZerosFinset T
  let Dlow := D.filter fun ρ : ℂ => |ρ.im| ≤ T + 3 / 2
  let Dhigh := D.filter fun ρ : ℂ => ¬|ρ.im| ≤ T + 3 / 2
  let Wlow :=
    (nontrivialZerosFinset ((T + 1 / 4) + 2)).filter fun ρ : ℂ =>
      (T + 1 / 4) - 1 / 4 ≤ |ρ.im| ∧
        |ρ.im| ≤ (T + 1 / 4) + 5 / 4
  let Whigh :=
    (nontrivialZerosFinset ((T + 7 / 4) + 2)).filter fun ρ : ℂ =>
      (T + 7 / 4) - 1 / 4 ≤ |ρ.im| ∧
        |ρ.im| ≤ (T + 7 / 4) + 5 / 4
  let f : ℂ → ℝ := fun ρ =>
    ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖
  have hdata (ρ : ℂ) (hρ : ρ ∈ D) :
      RiemannHypothesis.IsNontrivialZero ρ ∧ T < |ρ.im| ∧ |ρ.im| ≤ U := by
    rcases Finset.mem_sdiff.mp hρ with ⟨hρU, hρT⟩
    rcases mem_nontrivialZerosFinset.mp hρU with ⟨hzero, himU⟩
    have himT : T < |ρ.im| := by
      apply lt_of_not_ge
      intro him
      exact hρT (mem_nontrivialZerosFinset.mpr ⟨hzero, him⟩)
    exact ⟨hzero, himT, himU⟩
  have hDlow_subset : Dlow ⊆ Wlow := by
    intro ρ hρ
    rcases Finset.mem_filter.mp hρ with ⟨hρD, hρupper⟩
    rcases hdata ρ hρD with ⟨hzero, hρlower, _hρU⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_nontrivialZerosFinset.mpr ⟨hzero, ?_⟩, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
  have hDhigh_subset : Dhigh ⊆ Whigh := by
    intro ρ hρ
    rcases Finset.mem_filter.mp hρ with ⟨hρD, hρlower_not⟩
    rcases hdata ρ hρD with ⟨hzero, _hρlower, hρU⟩
    have hρlower : T + 3 / 2 < |ρ.im| := lt_of_not_ge hρlower_not
    apply Finset.mem_filter.mpr
    refine ⟨mem_nontrivialZerosFinset.mpr ⟨hzero, ?_⟩, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
  have hlow_sum : (∑ ρ ∈ Dlow, f ρ) ≤ ∑ ρ ∈ Wlow, f ρ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hDlow_subset
    intro ρ _hρW _hρD
    exact norm_nonneg _
  have hhigh_sum : (∑ ρ ∈ Dhigh, f ρ) ≤ ∑ ρ ∈ Whigh, f ρ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hDhigh_subset
    intro ρ _hρW _hρD
    exact norm_nonneg _
  have hsplit : (∑ ρ ∈ D, f ρ) =
      (∑ ρ ∈ Dlow, f ρ) + ∑ ρ ∈ Dhigh, f ρ := by
    symm
    exact Finset.sum_filter_add_sum_filter_not D
      (fun ρ : ℂ => |ρ.im| ≤ T + 3 / 2) f
  calc
    ‖explicitFormulaApproxWithMultiplicity x T -
        explicitFormulaApproxWithMultiplicity x U‖ ≤ ∑ ρ ∈ D, f ρ := by
      simpa [D, f] using
        norm_explicitFormulaApproxWithMultiplicity_sub_le_new_zeros_sum_norm
          (x := x) hTU
    _ = (∑ ρ ∈ Dlow, f ρ) + ∑ ρ ∈ Dhigh, f ρ := hsplit
    _ ≤ (∑ ρ ∈ Wlow, f ρ) + ∑ ρ ∈ Whigh, f ρ :=
      add_le_add hlow_sum hhigh_sum
    _ = ExplicitFormulaAux.localZeroContributionNorm x (T + 1 / 4) +
        ExplicitFormulaAux.localZeroContributionNorm x (T + 7 / 4) := by
      simp only [ExplicitFormulaAux.localZeroContributionNorm]
      rfl

/-- The multiplicity-aware von Mangoldt explicit formula, with symmetric
truncation by every real height.  The proof promotes the cofinal good-height
limit using the two-window bounded-gap estimate above. -/
theorem explicit_formula_von_mangoldt_proved
    {x : ℝ} (hx : 2 ≤ x) :
    explicit_formula_von_mangoldt x hx := by
  have hx1 : 1 < x := one_lt_two.trans_le hx
  rcases exists_cofinal_explicitFormulaApproxWithMultiplicity_tendsto hx1 with
    ⟨T, _hTmono, hTtop, hTspec, hTlimit⟩
  change Tendsto (fun t : ℝ => explicitFormulaApproxWithMultiplicity x t)
    atTop (𝓝 (chebyshevPsi0 x : ℂ))
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases (Metric.tendsto_atTop.mp hTlimit) (ε / 2) (by positivity) with
    ⟨Nseq, hNseq⟩
  have hlocal := ExplicitFormulaAux.tendsto_localZeroContributionNorm_atTop hx1
  rcases (Metric.tendsto_atTop.mp hlocal) (ε / 4) (by positivity) with
    ⟨Alocal, hAlocal⟩
  obtain ⟨Nlocal, hNlocal⟩ := exists_nat_ge Alocal
  let N : ℕ := max Nseq Nlocal
  refine ⟨2 * (N : ℝ) + 7, ?_⟩
  intro t ht
  let n : ℕ := Nat.floor ((t - 5) / 2)
  have hy : 0 ≤ (t - 5) / 2 := by
    have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    linarith
  have hn_floor : (n : ℝ) ≤ (t - 5) / 2 := by
    exact_mod_cast Nat.floor_le hy
  have hfloor_succ : (t - 5) / 2 < (n : ℝ) + 1 := by
    exact Nat.lt_floor_add_one _
  have hnN : N ≤ n := by
    apply Nat.le_floor
    dsimp [N]
    exact_mod_cast (show (N : ℝ) ≤ (t - 5) / 2 by linarith)
  have hnseq : Nseq ≤ n := (le_max_left _ _).trans hnN
  have hnlocal : Nlocal ≤ n := (le_max_right _ _).trans hnN
  have hTn_lower : 2 * (n : ℝ) + 4 ≤ T n := (hTspec n).1.1
  have hTn_upper : T n ≤ 2 * (n : ℝ) + 5 := (hTspec n).1.2
  have hTn_t : T n ≤ t := by linarith
  have ht_Tn : t ≤ T n + 3 := by linarith
  have hAlocal_Tn : Alocal ≤ T n := by
    have hcast : Alocal ≤ (Nlocal : ℝ) := hNlocal
    have hnlocal_real : (Nlocal : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlocal
    linarith
  have hlow_local :
      ExplicitFormulaAux.localZeroContributionNorm x (T n + 1 / 4) < ε / 4 := by
    have hdist := hAlocal (T n + 1 / 4) (by linarith)
    have hnonneg :
        0 ≤ ExplicitFormulaAux.localZeroContributionNorm x (T n + 1 / 4) := by
      unfold ExplicitFormulaAux.localZeroContributionNorm
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    change |ExplicitFormulaAux.localZeroContributionNorm x (T n + 1 / 4) - 0| <
      ε / 4 at hdist
    rwa [sub_zero, abs_of_nonneg hnonneg] at hdist
  have hhigh_local :
      ExplicitFormulaAux.localZeroContributionNorm x (T n + 7 / 4) < ε / 4 := by
    have hdist := hAlocal (T n + 7 / 4) (by linarith)
    have hnonneg :
        0 ≤ ExplicitFormulaAux.localZeroContributionNorm x (T n + 7 / 4) := by
      unfold ExplicitFormulaAux.localZeroContributionNorm
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    change |ExplicitFormulaAux.localZeroContributionNorm x (T n + 7 / 4) - 0| <
      ε / 4 at hdist
    rwa [sub_zero, abs_of_nonneg hnonneg] at hdist
  have hselected := hNseq n hnseq
  have hincrement :=
    norm_explicitFormulaApproxWithMultiplicity_sub_le_two_localWindows
      (x := x) hTn_t ht_Tn
  have hincrement' :
      dist (explicitFormulaApproxWithMultiplicity x t)
          (explicitFormulaApproxWithMultiplicity x (T n)) < ε / 2 := by
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt hincrement (by linarith)
  calc
    dist (explicitFormulaApproxWithMultiplicity x t) (chebyshevPsi0 x : ℂ) ≤
        dist (explicitFormulaApproxWithMultiplicity x t)
            (explicitFormulaApproxWithMultiplicity x (T n)) +
          dist (explicitFormulaApproxWithMultiplicity x (T n))
            (chebyshevPsi0 x : ℂ) := dist_triangle _ _ _
    _ < ε := by linarith

end ExplicitFormulaResidues
end PrimeNumberTheorem
