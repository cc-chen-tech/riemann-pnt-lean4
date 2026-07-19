import HardyTheorem.HardyOddMultiplicity
import HardyTheorem.CriticalLineMultiplicity

open Complex Filter Set Topology

namespace HardyTheorem

/-!
# Packing short-interval sign changes into odd critical-line zeros

This file isolates the finite combinatorial step used by bounded
Hardy--Littlewood arguments.  The generic theorem separates continuity and
local sign change from the two function-specific facts: detecting a zeta zero
and detecting odd analytic multiplicity.
-/

/-- `f` takes negative values arbitrarily close to the left of `t` and
positive values arbitrarily close to the right of `t`. -/
def HasNegToPosLocalSignChangeAt (f : ℝ → ℝ) (t : ℝ) : Prop :=
  (∀ ε > 0, ∃ x ∈ Set.Ioo (t - ε) t, f x < 0) ∧
    ∀ ε > 0, ∃ x ∈ Set.Ioo t (t + ε), 0 < f x

namespace HasNegToPosLocalSignChangeAt

/-- A local sign change of a continuous real function occurs at a zero. -/
theorem eq_zero {f : ℝ → ℝ} {t : ℝ} (hf : Continuous f)
    (hchange : HasNegToPosLocalSignChangeAt f t) :
    f t = 0 := by
  apply le_antisymm
  · by_contra hnot
    have hpos : 0 < f t := lt_of_not_ge hnot
    have hnear : ∀ᶠ x : ℝ in nhds t, 0 < f x :=
      continuousAt_const.eventually_lt hf.continuousAt hpos
    rw [Metric.eventually_nhds_iff] at hnear
    obtain ⟨ε, hε, hbound⟩ := hnear
    obtain ⟨x, hx, hxneg⟩ := hchange.1 ε hε
    have hdist : dist x t < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    exact (not_lt_of_ge (hbound hdist).le) hxneg
  · by_contra hnot
    have hneg : f t < 0 := lt_of_not_ge hnot
    have hnear : ∀ᶠ x : ℝ in nhds t, f x < 0 :=
      hf.continuousAt.eventually_lt continuousAt_const hneg
    rw [Metric.eventually_nhds_iff] at hnear
    obtain ⟨ε, hε, hbound⟩ := hnear
    obtain ⟨x, hx, hxpos⟩ := hchange.2 ε hε
    have hdist : dist x t < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    exact (not_lt_of_ge hxpos.le) (hbound hdist)

end HasNegToPosLocalSignChangeAt

/-- Pairwise-disjoint intervals carrying bounded local sign changes inject
into the bounded odd critical-line zero count, once the real function is
known to detect zeta zeros and odd analytic order. -/
theorem card_le_criticalLineOddZeroCount_of_pairwiseDisjoint_signChanges
    (f : ℝ → ℝ) (G : Finset ℕ) (J : ℕ → Set ℝ) (T : ℝ)
    (hf : Continuous f)
    (hdisj : (G : Set ℕ).PairwiseDisjoint J)
    (hzero : ∀ t, f t = 0 →
      riemannZeta ((1 / 2 : ℂ) + I * t) = 0)
    (hodd : ∀ t, HasNegToPosLocalSignChangeAt f t →
      Odd (analyticOrderNatAt riemannZeta ((1 / 2 : ℂ) + I * t)))
    (hsign : ∀ i ∈ G, ∃ t ∈ J i, t ∈ Set.Icc (0 : ℝ) T ∧
      HasNegToPosLocalSignChangeAt f t) :
    G.card ≤ criticalLineOddZeroCount T := by
  apply card_le_criticalLineOddZeroCount_of_pairwiseDisjoint_hits
    G J T hdisj
  intro i hi
  obtain ⟨t, htJ, ht, hchange⟩ := hsign i hi
  refine ⟨t, htJ, ?_⟩
  simp only [criticalLineOddZerosFinset, Finset.mem_filter]
  refine ⟨?_, hodd t hchange⟩
  rw [mem_criticalLineZerosFinset]
  refine ⟨⟨hzero t (hchange.eq_zero hf), ?_, ?_⟩, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · simpa using ht.1
  · simpa using ht.2

/-- The generic packing theorem specialized to Hardy's `Z` function. -/
theorem card_le_criticalLineOddZeroCount_of_pairwiseDisjoint_hardyZ_signChanges
    (G : Finset ℕ) (J : ℕ → Set ℝ) (T : ℝ)
    (hdisj : (G : Set ℕ).PairwiseDisjoint J)
    (hsign : ∀ i ∈ G, ∃ t ∈ J i, t ∈ Set.Icc (0 : ℝ) T ∧
      HasNegToPosLocalSignChangeAt hardyZ t) :
    G.card ≤ criticalLineOddZeroCount T := by
  apply card_le_criticalLineOddZeroCount_of_pairwiseDisjoint_signChanges
    hardyZ G J T hardyZ_continuous hdisj
  · intro t ht
    convert hardyZ_zero_implies_zeta_zero t ht using 1
    norm_num
  · intro t hchange
    exact odd_analyticOrderNatAt_riemannZeta_of_hardyZ_local_sign_change
      hchange.1 hchange.2
  · exact hsign

end HardyTheorem
