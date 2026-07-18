import HardyTheorem
import PrimeNumberTheorem.NontrivialZeroMultiplicity

open Complex Filter Topology

namespace HardyTheorem

/-!
# Critical-line zero counts with analytic multiplicity

The original `zeroCountOnCriticalLine` counts distinct ordinates.  The
Hardy--Littlewood, Selberg, and Conrey counting statements are most naturally
formulated using the analytic multiplicity of each zeta zero.  This file
provides that count without changing the existing distinct-count API.
-/

/-- The distinct nontrivial zeta zeros on the critical line with imaginary
part in `[0, T]`. -/
noncomputable def criticalLineZerosFinset (T : ℝ) : Finset ℂ :=
  (PrimeNumberTheorem.nontrivialZerosFinset T).filter
    fun ρ => ρ.re = 1 / 2 ∧ 0 ≤ ρ.im

lemma mem_criticalLineZerosFinset {T : ℝ} {ρ : ℂ} :
    ρ ∈ criticalLineZerosFinset T ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧
        ρ.re = 1 / 2 ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T := by
  classical
  simp only [criticalLineZerosFinset, Finset.mem_filter,
    PrimeNumberTheorem.mem_nontrivialZerosFinset]
  constructor
  · rintro ⟨⟨hzero, habs⟩, hre, him0⟩
    exact ⟨hzero, hre, him0, (le_abs_self ρ.im).trans habs⟩
  · rintro ⟨hzero, hre, him0, himT⟩
    exact ⟨⟨hzero, by simpa [abs_of_nonneg him0] using himT⟩, hre, him0⟩

/-- The number of critical-line zeta zeros with imaginary part in `[0, T]`,
counted with analytic multiplicity. -/
noncomputable def criticalLineZeroMultiplicityCount (T : ℝ) : ℕ :=
  ∑ ρ ∈ criticalLineZerosFinset T, analyticOrderNatAt riemannZeta ρ

/-- The number of distinct critical-line zeros represented by
`criticalLineZerosFinset`. -/
noncomputable def criticalLineDistinctZeroCount (T : ℝ) : ℕ :=
  (criticalLineZerosFinset T).card

/-- Critical-line zeros of odd analytic multiplicity, each counted once. -/
noncomputable def criticalLineOddZerosFinset (T : ℝ) : Finset ℂ :=
  (criticalLineZerosFinset T).filter
    fun ρ => Odd (analyticOrderNatAt riemannZeta ρ)

/-- The number of critical-line zeros of odd analytic multiplicity, each
counted once.  These are exactly the zeros detected by sign changes of the
real Hardy function. -/
noncomputable def criticalLineOddZeroCount (T : ℝ) : ℕ :=
  (criticalLineOddZerosFinset T).card

lemma criticalLineZerosFinset_subset {T U : ℝ} (hTU : T ≤ U) :
    criticalLineZerosFinset T ⊆ criticalLineZerosFinset U := by
  intro ρ hρ
  rw [mem_criticalLineZerosFinset] at hρ ⊢
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans hTU⟩

lemma criticalLineZeroMultiplicityCount_mono {T U : ℝ} (hTU : T ≤ U) :
    criticalLineZeroMultiplicityCount T ≤
      criticalLineZeroMultiplicityCount U := by
  classical
  exact Finset.sum_le_sum_of_subset
    (criticalLineZerosFinset_subset hTU)

lemma criticalLineDistinctZeroCount_mono {T U : ℝ} (hTU : T ≤ U) :
    criticalLineDistinctZeroCount T ≤ criticalLineDistinctZeroCount U := by
  classical
  exact Finset.card_le_card (criticalLineZerosFinset_subset hTU)

lemma criticalLineOddZerosFinset_subset {T U : ℝ} (hTU : T ≤ U) :
    criticalLineOddZerosFinset T ⊆ criticalLineOddZerosFinset U := by
  intro ρ hρ
  simp only [criticalLineOddZerosFinset, Finset.mem_filter] at hρ ⊢
  exact ⟨criticalLineZerosFinset_subset hTU hρ.1, hρ.2⟩

lemma criticalLineOddZeroCount_mono {T U : ℝ} (hTU : T ≤ U) :
    criticalLineOddZeroCount T ≤ criticalLineOddZeroCount U := by
  classical
  exact Finset.card_le_card (criticalLineOddZerosFinset_subset hTU)

lemma analyticOrderNatAt_riemannZeta_pos_of_mem_criticalLineZerosFinset
    {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ criticalLineZerosFinset T) :
    0 < analyticOrderNatAt riemannZeta ρ := by
  have hmem := (mem_criticalLineZerosFinset.mp hρ).1
  have hρ1 : ρ ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hmem.2.2]
  exact ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero hρ1 hmem.1

/-- The multiplicity count dominates the number of distinct critical-line
zeros represented by `criticalLineZerosFinset`. -/
lemma card_criticalLineZerosFinset_le_criticalLineZeroMultiplicityCount
    (T : ℝ) :
    (criticalLineZerosFinset T).card ≤
      criticalLineZeroMultiplicityCount T := by
  classical
  rw [criticalLineZeroMultiplicityCount, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun ρ hρ =>
    analyticOrderNatAt_riemannZeta_pos_of_mem_criticalLineZerosFinset hρ

/-- The existing real-ordinate count and the complex-zero finset have the
same cardinality. -/
lemma zeroCountOnCriticalLine_eq_criticalLineDistinctZeroCount (T : ℝ) :
    zeroCountOnCriticalLine T = criticalLineDistinctZeroCount T := by
  classical
  let S : Set (Set.Icc (0 : ℝ) T) :=
    {t : Set.Icc (0 : ℝ) T |
      riemannZeta (0.5 + I * (t : ℝ)) = 0}
  let Z : Set ℂ := criticalLineZerosFinset T
  have hcard : S.ncard = Z.ncard := by
    apply Set.ncard_congr (s := S) (t := Z)
      (fun t _ => (0.5 : ℂ) + I * (t : ℝ))
    · intro t ht
      change (0.5 : ℂ) + I * (t : ℝ) ∈ criticalLineZerosFinset T
      rw [mem_criticalLineZerosFinset]
      change riemannZeta (0.5 + I * (t : ℝ)) = 0 at ht
      refine ⟨⟨ht, ?_, ?_⟩, ?_, ?_, ?_⟩
      · norm_num
      · norm_num
      · norm_num
      · norm_num
        exact t.property.1
      · norm_num
        exact t.property.2
    · intro a b _ha _hb hab
      apply Subtype.ext
      have him := congrArg Complex.im hab
      simpa using him
    · intro ρ hρ
      change ρ ∈ criticalLineZerosFinset T at hρ
      have hm := mem_criticalLineZerosFinset.mp hρ
      let t : Set.Icc (0 : ℝ) T := ⟨ρ.im, hm.2.2.1, hm.2.2.2⟩
      have heq : (0.5 : ℂ) + I * (t : ℝ) = ρ := by
        apply Complex.ext
        · norm_num [t, hm.2.1]
        · norm_num [t]
      refine ⟨t, ?_, heq⟩
      change riemannZeta (0.5 + I * (t : ℝ)) = 0
      rw [heq]
      exact hm.1.1
  simpa [zeroCountOnCriticalLine, criticalLineDistinctZeroCount, S, Z]
    using hcard

lemma criticalLineOddZeroCount_le_criticalLineDistinctZeroCount (T : ℝ) :
    criticalLineOddZeroCount T ≤ criticalLineDistinctZeroCount T := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma criticalLineDistinctZeroCount_le_criticalLineZeroMultiplicityCount
    (T : ℝ) :
    criticalLineDistinctZeroCount T ≤
      criticalLineZeroMultiplicityCount T :=
  card_criticalLineZerosFinset_le_criticalLineZeroMultiplicityCount T

lemma zeroCountOnCriticalLine_le_criticalLineZeroMultiplicityCount (T : ℝ) :
    zeroCountOnCriticalLine T ≤ criticalLineZeroMultiplicityCount T := by
  rw [zeroCountOnCriticalLine_eq_criticalLineDistinctZeroCount]
  exact criticalLineDistinctZeroCount_le_criticalLineZeroMultiplicityCount T

lemma criticalLineOddZeroCount_le_criticalLineZeroMultiplicityCount (T : ℝ) :
    criticalLineOddZeroCount T ≤
      criticalLineZeroMultiplicityCount T :=
  (criticalLineOddZeroCount_le_criticalLineDistinctZeroCount T).trans
    (criticalLineDistinctZeroCount_le_criticalLineZeroMultiplicityCount T)

/-- A linear lower bound for critical-line zeta zeros counted with analytic
multiplicity.  This follows from the stronger odd-multiplicity count supplied
by the Hardy--Littlewood sign-change method. -/
def hardy_littlewood_multiplicity_lower_bound_target : Prop :=
  ∃ C > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
    (criticalLineZeroMultiplicityCount T : ℝ) ≥ C * T

/-- Literature-aligned Hardy--Littlewood target: linearly many critical-line
zeros of odd analytic multiplicity, each counted once. -/
def hardy_littlewood_odd_lower_bound_target : Prop :=
  ∃ C > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
    (criticalLineOddZeroCount T : ℝ) ≥ C * T

lemma hardy_littlewood_multiplicity_lower_bound_target_of_odd
    (h : hardy_littlewood_odd_lower_bound_target) :
    hardy_littlewood_multiplicity_lower_bound_target := by
  rcases h with ⟨C, hC, T0, hT⟩
  refine ⟨C, hC, T0, fun T hT0 => ?_⟩
  exact (hT T hT0).trans
    (by exact_mod_cast criticalLineOddZeroCount_le_criticalLineZeroMultiplicityCount T)

/-- The sign-change form of Hardy--Littlewood implies the repository's
legacy distinct-ordinate linear lower-bound target. -/
lemma hardy_littlewood_lower_bound_target_of_odd
    (h : hardy_littlewood_odd_lower_bound_target) :
    hardy_littlewood_lower_bound_target := by
  rcases h with ⟨C, hC, T0, hT⟩
  refine ⟨C, hC, T0, fun T hT0 => ?_⟩
  rw [zeroCountOnCriticalLine_eq_criticalLineDistinctZeroCount]
  exact (hT T hT0).trans
    (by exact_mod_cast criticalLineOddZeroCount_le_criticalLineDistinctZeroCount T)

lemma hardy_theorem_target_of_hardy_littlewood_odd_lower_bound
    (h : hardy_littlewood_odd_lower_bound_target) :
    hardy_theorem_target :=
  hardy_theorem_target_of_hardy_littlewood_lower_bound
    (hardy_littlewood_lower_bound_target_of_odd h)

/-- Literature-aligned Selberg target: a positive-proportion-scale lower
bound for odd-order critical-line zeros counted once. -/
def selberg_odd_zero_proportion_target : Prop :=
  ∃ c > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
    (criticalLineOddZeroCount T : ℝ) ≥
      c * (T / (2 * Real.pi) * Real.log T)

lemma selberg_zero_proportion_target_of_odd
    (h : selberg_odd_zero_proportion_target) :
    selberg_zero_proportion_target := by
  rcases h with ⟨c, hc, T0, hT⟩
  refine ⟨c, hc, T0, fun T hT0 => ?_⟩
  rw [zeroCountOnCriticalLine_eq_criticalLineDistinctZeroCount]
  exact (hT T hT0).trans
    (by exact_mod_cast criticalLineOddZeroCount_le_criticalLineDistinctZeroCount T)

end HardyTheorem
