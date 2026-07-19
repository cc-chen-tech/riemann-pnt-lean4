import Mathlib

open MeasureTheory Set

namespace MathlibAux

noncomputable section

private def packingCore (a H : ℝ) (i : ℕ) : Set ℝ :=
  Set.Ioo (a + 3 * H * i) (a + 3 * H * i + H)

private lemma packingCore_subset_Icc {a b H : ℝ} {N i : ℕ}
    (hH : 0 < H) (hN : (N : ℝ) * (3 * H) ≤ b - a) (hi : i < N) :
    packingCore a H i ⊆ Set.Icc a b := by
  intro x hx
  have hiN : (i : ℝ) + 1 ≤ N := by
    exact_mod_cast (Nat.succ_le_iff.mpr hi)
  have hscale : ((i : ℝ) + 1) * (3 * H) ≤ (N : ℝ) * (3 * H) :=
    mul_le_mul_of_nonneg_right hiN (by positivity)
  have hblock : a + 3 * H * (i : ℝ) + 3 * H ≤ b := by
    calc
      a + 3 * H * (i : ℝ) + 3 * H =
          a + ((i : ℝ) + 1) * (3 * H) := by ring
      _ ≤ a + (N : ℝ) * (3 * H) := by
        simpa only [add_comm] using add_le_add_left hscale a
      _ ≤ b := by linarith
  constructor
  · have hprod : 0 ≤ 3 * H * (i : ℝ) := by positivity
    have : a ≤ a + 3 * H * (i : ℝ) := by linarith
    exact this.trans hx.1.le
  · rcases hx with ⟨_, hxUpper⟩
    nlinarith

private lemma packingCore_start_le_sub {a b H : ℝ} {N i : ℕ}
    (hH : 0 < H) (hN : (N : ℝ) * (3 * H) ≤ b - a) (hi : i < N)
    {x : ℝ} (hx : x ∈ packingCore a H i) :
    x ≤ b - H := by
  have hiN : (i : ℝ) + 1 ≤ N := by
    exact_mod_cast (Nat.succ_le_iff.mpr hi)
  have hscale : ((i : ℝ) + 1) * (3 * H) ≤ (N : ℝ) * (3 * H) :=
    mul_le_mul_of_nonneg_right hiN (by positivity)
  have hblock : a + 3 * H * (i : ℝ) + 3 * H ≤ b := by
    calc
      a + 3 * H * (i : ℝ) + 3 * H =
          a + ((i : ℝ) + 1) * (3 * H) := by ring
      _ ≤ a + (N : ℝ) * (3 * H) := by
        simpa only [add_comm] using add_le_add_left hscale a
      _ ≤ b := by linarith
  rcases hx with ⟨_, hxUpper⟩
  nlinarith

private lemma packingCore_pairwiseDisjoint (a : ℝ) {H : ℝ} (hH : 0 < H) :
    Set.PairwiseDisjoint Set.univ (packingCore a H) := by
  intro i _ j _ hij
  change Disjoint (packingCore a H i) (packingCore a H j)
  rw [Set.disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hij' : (i : ℝ) + 1 ≤ j := by
      exact_mod_cast (Nat.succ_le_iff.mpr hijlt)
    have hscale : ((i : ℝ) + 1) * (3 * H) ≤ (j : ℝ) * (3 * H) :=
      mul_le_mul_of_nonneg_right hij' (by positivity)
    dsimp only [packingCore] at hxi hxj
    have hsep : a + 3 * H * (i : ℝ) + H ≤ a + 3 * H * (j : ℝ) := by
      nlinarith
    exact (not_lt_of_ge (hsep.trans hxj.1.le)) hxi.2
  · have hji' : (j : ℝ) + 1 ≤ i := by
      exact_mod_cast (Nat.succ_le_iff.mpr hjilt)
    have hscale : ((j : ℝ) + 1) * (3 * H) ≤ (i : ℝ) * (3 * H) :=
      mul_le_mul_of_nonneg_right hji' (by positivity)
    dsimp only [packingCore] at hxi hxj
    have hsep : a + 3 * H * (j : ℝ) + H ≤ a + 3 * H * (i : ℝ) := by
      nlinarith
    exact (not_lt_of_ge (hsep.trans hxi.1.le)) hxj.2

private lemma windows_pairwiseDisjoint_of_mem_packingCore
    (a : ℝ) {H : ℝ} (hH : 0 < H) (G : Finset ℕ) (start : ℕ → ℝ)
    (hstart : ∀ i ∈ G, start i ∈ packingCore a H i) :
    (G : Set ℕ).PairwiseDisjoint
      (fun i ↦ Set.Ioo (start i) (start i + H)) := by
  intro i hi j hj hij
  change Disjoint (Set.Ioo (start i) (start i + H))
    (Set.Ioo (start j) (start j + H))
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hsi := hstart i hi
  have hsj := hstart j hj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hij' : (i : ℝ) + 1 ≤ j := by
      exact_mod_cast (Nat.succ_le_iff.mpr hijlt)
    have hscale : ((i : ℝ) + 1) * (3 * H) ≤ (j : ℝ) * (3 * H) :=
      mul_le_mul_of_nonneg_right hij' (by positivity)
    dsimp only [packingCore] at hsi hsj
    have hsep : start i + H ≤ start j := by
      nlinarith [hsi.2, hsj.1]
    exact (not_lt_of_ge (hsep.trans hxj.1.le)) hxi.2
  · have hji' : (j : ℝ) + 1 ≤ i := by
      exact_mod_cast (Nat.succ_le_iff.mpr hjilt)
    have hscale : ((j : ℝ) + 1) * (3 * H) ≤ (i : ℝ) * (3 * H) :=
      mul_le_mul_of_nonneg_right hji' (by positivity)
    dsimp only [packingCore] at hsi hsj
    have hsep : start j + H ≤ start i := by
      nlinarith [hsj.2, hsi.1]
    exact (not_lt_of_ge (hsep.trans hxi.1.le)) hxj.2

/-- If the complement of `good` occupies at most `E` units of a bounded
interval, then the interval contains many good starts for pairwise-disjoint
windows of length `H`.

The proof uses open cores of length `H` in every third `H`-block.  Empty
cores are disjoint subsets of the bad set, so at most `E / H` cores can be
empty.  A good start chosen in each remaining core produces disjoint open
windows, with two unused `H`-blocks separating consecutive cores. -/
theorem exists_many_pairwiseDisjoint_windows_of_measure_compl_le
    (good : Set ℝ) (a b H E : ℝ)
    (hH : 0 < H) (hab : a ≤ b)
    (hbad : volume.real (Set.Icc a b \ good) ≤ E) :
    ∃ (G : Finset ℕ) (start : ℕ → ℝ),
      ((Nat.floor ((b - a) / (3 * H)) : ℝ) - E / H ≤
          (G.card : ℝ)) ∧
        (∀ i ∈ G, start i ∈ good ∩ Set.Icc a (b - H)) ∧
        (G : Set ℕ).PairwiseDisjoint
          (fun i ↦ Set.Ioo (start i) (start i + H)) := by
  classical
  let N := Nat.floor ((b - a) / (3 * H))
  let core : ℕ → Set ℝ := packingCore a H
  let candidates := Finset.range N
  let emptyCores := candidates.filter fun i ↦ core i ⊆ Set.Icc a b \ good
  let G := candidates \ emptyCores
  have hE : 0 ≤ E := measureReal_nonneg.trans hbad
  have hratio_nonneg : 0 ≤ (b - a) / (3 * H) :=
    div_nonneg (sub_nonneg.mpr hab) (mul_nonneg (by norm_num) hH.le)
  have hN : (N : ℝ) * (3 * H) ≤ b - a := by
    have hfloor : (N : ℝ) ≤ (b - a) / (3 * H) := by
      simpa only [N] using Nat.floor_le hratio_nonneg
    exact (le_div_iff₀ (by positivity : 0 < 3 * H)).1 hfloor
  have hcore_subset (i : ℕ) (hi : i ∈ candidates) :
      core i ⊆ Set.Icc a b := by
    apply packingCore_subset_Icc hH hN
    simpa only [candidates, Finset.mem_range] using hi
  have hempty_subset : emptyCores ⊆ candidates := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have hcore_disjoint : (emptyCores : Set ℕ).PairwiseDisjoint core := by
    intro i _ j _ hij
    exact packingCore_pairwiseDisjoint a hH (Set.mem_univ i) (Set.mem_univ j) hij
  have hunion_subset :
      (⋃ i ∈ emptyCores, core i) ⊆ Set.Icc a b \ good := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    obtain ⟨hiEmpty, hxCore⟩ := hi
    exact (Finset.mem_filter.mp hiEmpty).2 hxCore
  have hcore_measure (i : ℕ) : volume.real (core i) = H := by
    simp [core, packingCore, Measure.real, Real.volume_Ioo, hH.le]
  have hempty_measure :
      volume.real (⋃ i ∈ emptyCores, core i) = (emptyCores.card : ℝ) * H := by
    rw [measureReal_biUnion_finset hcore_disjoint
      (fun _ _ ↦ measurableSet_Ioo)
      (fun i _ ↦ by simp [core, packingCore, Real.volume_Ioo])]
    simp [hcore_measure]
  have hbad_ne_top : volume (Set.Icc a b \ good) ≠ ⊤ := by
    apply measure_ne_top_of_subset diff_subset
    exact (measure_Icc_lt_top : volume (Set.Icc a b) < ⊤).ne
  have hempty_mul_le : (emptyCores.card : ℝ) * H ≤ E := by
    rw [← hempty_measure]
    exact (measureReal_mono hunion_subset hbad_ne_top).trans hbad
  have hempty_card_le : (emptyCores.card : ℝ) ≤ E / H :=
    (le_div_iff₀ hH).2 hempty_mul_le
  have hG_card :
      (G.card : ℝ) = (N : ℝ) - (emptyCores.card : ℝ) := by
    simpa only [G, candidates, Finset.card_range] using
      (Finset.cast_card_sdiff (R := ℝ) hempty_subset)
  have hchoice : ∀ i ∈ G,
      ∃ x : ℝ, x ∈ core i ∧ x ∈ good ∩ Set.Icc a (b - H) := by
    intro i hiG
    have hiCand : i ∈ candidates := (Finset.mem_sdiff.mp hiG).1
    have hiNotEmpty : i ∉ emptyCores := (Finset.mem_sdiff.mp hiG).2
    have hnotSubset : ¬ core i ⊆ Set.Icc a b \ good := by
      intro hsubset
      exact hiNotEmpty (Finset.mem_filter.mpr ⟨hiCand, hsubset⟩)
    rw [Set.not_subset] at hnotSubset
    obtain ⟨x, hxCore, hxNotBad⟩ := hnotSubset
    have hxIcc : x ∈ Set.Icc a b := hcore_subset i hiCand hxCore
    have hxGood : x ∈ good := by
      by_contra hxNotGood
      exact hxNotBad ⟨hxIcc, hxNotGood⟩
    have hxUpper : x ≤ b - H := by
      apply packingCore_start_le_sub hH hN
      · simpa only [candidates, Finset.mem_range] using hiCand
      · exact hxCore
    exact ⟨x, hxCore, hxGood, hxIcc.1, hxUpper⟩
  let start : ℕ → ℝ := fun i ↦
    if hi : i ∈ G then Classical.choose (hchoice i hi) else 0
  have hstart (i : ℕ) (hi : i ∈ G) :
      start i ∈ core i ∧ start i ∈ good ∩ Set.Icc a (b - H) := by
    simp only [start, dif_pos hi]
    exact Classical.choose_spec (hchoice i hi)
  refine ⟨G, start, ?_, ?_, ?_⟩
  · rw [hG_card]
    have hEdiv : 0 ≤ E / H := div_nonneg hE hH.le
    linarith
  · intro i hi
    exact (hstart i hi).2
  · apply windows_pairwiseDisjoint_of_mem_packingCore a hH G start
    intro i hi
    exact (hstart i hi).1

end

end MathlibAux
