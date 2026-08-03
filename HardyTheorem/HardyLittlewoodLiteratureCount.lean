import HardyTheorem.HardyLittlewoodOddTheorem
import HardyTheorem.PositiveCriticalLineOddCount
import PrimeNumberTheorem.RiemannVonMangoldt.CriticalLinePartition

open Complex

namespace HardyTheorem

/-!
# Literature-normalized Hardy--Littlewood zero counts

The classical counting functions use positive ordinates `0 < γ ≤ T`.
The original Hardy--Littlewood development in this repository used
`0 ≤ γ ≤ T`; this file removes the possible central point without assuming
the separate numerical fact `ζ(1 / 2) ≠ 0`.
-/

lemma positiveCriticalLineOddZerosFinset_subset_positiveCriticalLineZerosFinset
    (T : ℝ) :
    positiveCriticalLineOddZerosFinset T ⊆
      PrimeNumberTheorem.RiemannVonMangoldt.positiveCriticalLineZerosFinset T := by
  intro ρ hρ
  have hodd := (mem_positiveCriticalLineOddZerosFinset.mp hρ).1
  have him := (mem_positiveCriticalLineOddZerosFinset.mp hρ).2
  have hcritical := (Finset.mem_filter.mp hodd).1
  have hm := mem_criticalLineZerosFinset.mp hcritical
  exact
    PrimeNumberTheorem.RiemannVonMangoldt.mem_positiveCriticalLineZerosFinset.mpr
      ⟨hm.1, him, hm.2.2.2, hm.2.1⟩

/-- The positive odd-order count is bounded by the standard positive-ordinate
critical-line count with analytic multiplicity. -/
lemma positiveCriticalLineOddZeroCount_le_positiveCriticalLineZeroMultiplicityCount
    (T : ℝ) :
    positiveCriticalLineOddZeroCount T ≤
      PrimeNumberTheorem.RiemannVonMangoldt.positiveCriticalLineZeroMultiplicityCount T := by
  classical
  have hcard :
      (positiveCriticalLineOddZerosFinset T).card ≤
        (PrimeNumberTheorem.RiemannVonMangoldt.positiveCriticalLineZerosFinset T).card :=
    Finset.card_le_card
      (positiveCriticalLineOddZerosFinset_subset_positiveCriticalLineZerosFinset T)
  apply hcard.trans
  unfold PrimeNumberTheorem.RiemannVonMangoldt.positiveCriticalLineZeroMultiplicityCount
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro ρ hρ
  have hm :=
    PrimeNumberTheorem.RiemannVonMangoldt.mem_positiveCriticalLineZerosFinset.mp hρ
  exact ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
    (by
      intro hρ1
      have hre := congrArg Complex.re hρ1
      norm_num at hre
      nlinarith [hm.2.2.2])
    hm.1.1

private lemma criticalLineOddZerosFinset_subset_positive_union_center
    (T : ℝ) :
    criticalLineOddZerosFinset T ⊆
      positiveCriticalLineOddZerosFinset T ∪ {(1 / 2 : ℂ)} := by
  intro ρ hρ
  by_cases him : 0 < ρ.im
  · exact Finset.mem_union.mpr <| Or.inl <|
      mem_positiveCriticalLineOddZerosFinset.mpr ⟨hρ, him⟩
  · apply Finset.mem_union.mpr
    right
    rw [Finset.mem_singleton]
    have hcritical := (Finset.mem_filter.mp hρ).1
    have hm := mem_criticalLineZerosFinset.mp hcritical
    have him0 : ρ.im = 0 := by linarith [hm.2.2.1]
    apply Complex.ext
    · simpa using hm.2.1
    · simpa using him0

/-- Passing from `0 ≤ γ ≤ T` to the literature convention `0 < γ ≤ T`
removes at most the single central point `1 / 2`. -/
lemma criticalLineOddZeroCount_le_positiveCriticalLineOddZeroCount_add_one
    (T : ℝ) :
    criticalLineOddZeroCount T ≤ positiveCriticalLineOddZeroCount T + 1 := by
  classical
  unfold criticalLineOddZeroCount positiveCriticalLineOddZeroCount
  calc
    (criticalLineOddZerosFinset T).card ≤
        (positiveCriticalLineOddZerosFinset T ∪ {(1 / 2 : ℂ)}).card :=
      Finset.card_le_card
        (criticalLineOddZerosFinset_subset_positive_union_center T)
    _ ≤ (positiveCriticalLineOddZerosFinset T).card +
        ({(1 / 2 : ℂ)} : Finset ℂ).card :=
      Finset.card_union_le _ _
    _ = (positiveCriticalLineOddZerosFinset T).card + 1 := by simp

/-- Literature-normalized Hardy--Littlewood target: linearly many
positive-ordinate critical-line zeros of odd analytic multiplicity, each
counted once. -/
def hardy_littlewood_positive_odd_lower_bound_target : Prop :=
  ∃ C > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
    (positiveCriticalLineOddZeroCount T : ℝ) ≥ C * T

/-- The repository's nonnegative-ordinate odd-count theorem implies the
literature-normalized positive-ordinate version. -/
theorem hardy_littlewood_positive_odd_lower_bound_target_of_nonnegative
    (h : hardy_littlewood_odd_lower_bound_target) :
    hardy_littlewood_positive_odd_lower_bound_target := by
  rcases h with ⟨C, hC, T0, hT⟩
  let C' : ℝ := C / 2
  let T1 : ℝ := max T0 (2 / C)
  refine ⟨C', div_pos hC (by norm_num), T1, ?_⟩
  intro T hT1
  have hT0 : T0 ≤ T := (le_max_left _ _).trans hT1
  have hTlarge : 2 / C ≤ T := (le_max_right _ _).trans hT1
  have hCT : 2 ≤ C * T := by
    rw [div_le_iff₀ hC] at hTlarge
    nlinarith
  have hLower := hT T hT0
  have hCountNat :=
    criticalLineOddZeroCount_le_positiveCriticalLineOddZeroCount_add_one T
  have hCountReal :
      (criticalLineOddZeroCount T : ℝ) ≤
        (positiveCriticalLineOddZeroCount T : ℝ) + 1 := by
    exact_mod_cast hCountNat
  dsimp only [C']
  nlinarith

/-- Unconditional literature-normalized Hardy--Littlewood theorem for
positive ordinates and odd analytic multiplicity. -/
theorem hardy_littlewood_positive_odd_lower_bound_target_proved :
    hardy_littlewood_positive_odd_lower_bound_target :=
  hardy_littlewood_positive_odd_lower_bound_target_of_nonnegative
    hardy_littlewood_odd_lower_bound_target_proved

/-- Literature-normalized `N₀(T)` target, with every positive-ordinate
critical-line zero counted by its analytic multiplicity. -/
def hardy_littlewood_positive_multiplicity_lower_bound_target : Prop :=
  ∃ C > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
    (PrimeNumberTheorem.RiemannVonMangoldt.positiveCriticalLineZeroMultiplicityCount T : ℝ) ≥
      C * T

lemma hardy_littlewood_positive_multiplicity_lower_bound_target_of_odd
    (h : hardy_littlewood_positive_odd_lower_bound_target) :
    hardy_littlewood_positive_multiplicity_lower_bound_target := by
  rcases h with ⟨C, hC, T0, hT⟩
  refine ⟨C, hC, T0, fun T hT0 => ?_⟩
  exact (hT T hT0).trans
    (by
      exact_mod_cast
        positiveCriticalLineOddZeroCount_le_positiveCriticalLineZeroMultiplicityCount T)

/-- Unconditional Hardy--Littlewood lower bound for the literature-standard
positive-ordinate, multiplicity-weighted critical-line zero count. -/
theorem hardy_littlewood_positive_multiplicity_lower_bound_target_proved :
    hardy_littlewood_positive_multiplicity_lower_bound_target :=
  hardy_littlewood_positive_multiplicity_lower_bound_target_of_odd
    hardy_littlewood_positive_odd_lower_bound_target_proved

end HardyTheorem
