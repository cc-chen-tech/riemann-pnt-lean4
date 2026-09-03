import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Complete open components of an interval with finitely many points removed -/

open Set

namespace MathlibAux

/-- Pair each left endpoint in `{U} ∪ K` with its next right endpoint in
`K ∪ {T}`. This yields all disjoint components, including when `K` is empty. -/
theorem exists_finite_zero_complement_components
    {K : Finset ℝ} {U T : ℝ} (hUT : U < T)
    (hK : ∀ t ∈ K, t ∈ Ioo U T) :
    ∃ b : ↥(insert U K) → ℝ,
      (∀ i : ↥(insert U K), U ≤ (i : ℝ) ∧ (i : ℝ) < b i ∧ b i ≤ T) ∧
      (∀ i, b i ∈ insert T K) ∧
      (∀ i : ↥(insert U K), ∀ t ∈ Ioo (i : ℝ) (b i), t ∉ K) ∧
      Pairwise (fun (i j : ↥(insert U K)) =>
        Disjoint (Ioo (i : ℝ) (b i)) (Ioo (j : ℝ) (b j))) ∧
      ∀ t ∈ Ioo U T, t ∉ K ↔ ∃ i : ↥(insert U K), t ∈ Ioo (i : ℝ) (b i) := by
  classical
  have hbase : ∀ i : ↥(insert U K), U ≤ (i : ℝ) ∧ (i : ℝ) < T := by
    intro i
    rcases Finset.mem_insert.mp i.2 with hi | hi
    · exact ⟨by rw [hi], by simpa only [hi] using hUT⟩
    · exact ⟨(hK i hi).1.le, (hK i hi).2⟩
  have hnext : ∀ i : ↥(insert U K), ∃ y ∈ insert T K,
      (i : ℝ) < y ∧ ∀ z ∈ insert T K, (i : ℝ) < z → y ≤ z := by
    intro i
    exact Finset.exists_next_right ⟨T, Finset.mem_insert_self _ _, (hbase i).2⟩
  choose b hbmem hblt hbmin using hnext
  have hgeom : ∀ i : ↥(insert U K), U ≤ (i : ℝ) ∧ (i : ℝ) < b i ∧ b i ≤ T :=
    fun i => ⟨(hbase i).1, hblt i,
      hbmin i T (Finset.mem_insert_self _ _) (hbase i).2⟩
  have hgap : ∀ i : ↥(insert U K), ∀ t ∈ Ioo (i : ℝ) (b i), t ∉ K := by
    intro i t ht htK
    exact (not_le_of_gt ht.2) (hbmin i t (Finset.mem_insert_of_mem htK) ht.1)
  have hbefore : ∀ i j : ↥(insert U K), (i : ℝ) < j → b i ≤ (j : ℝ) := by
    intro i j hij
    rcases Finset.mem_insert.mp j.2 with hj | hj
    · have hiU := (hbase i).1
      rw [hj] at hij
      linarith
    · exact hbmin i j (Finset.mem_insert_of_mem hj) hij
  have hdisjoint : Pairwise (fun (i j : ↥(insert U K)) =>
      Disjoint (Ioo (i : ℝ) (b i)) (Ioo (j : ℝ) (b j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    have hne : (i : ℝ) ≠ (j : ℝ) := fun h => hij (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle := hbefore i j hlt
      linarith [hti.2, htj.1]
    · have hle := hbefore j i hgt
      linarith [htj.2, hti.1]
  refine ⟨b, hgeom, hbmem, hgap, hdisjoint, ?_⟩
  intro t ht
  constructor
  · intro htK
    obtain ⟨u, hu, hut, hmax⟩ := Finset.exists_next_left
      (s := insert U K) ⟨U, Finset.mem_insert_self _ _, ht.1⟩
    let i : ↥(insert U K) := ⟨u, hu⟩
    refine ⟨i, hut, ?_⟩
    by_contra hnot
    have hbt : b i ≤ t := le_of_not_gt hnot
    have hbK : b i ∈ K := by
      rcases Finset.mem_insert.mp (hbmem i) with hbT | hbK
      · linarith [ht.2]
      · exact hbK
    have hbne : b i ≠ t := by
      intro h
      apply htK
      rwa [h] at hbK
    have hbless : b i < t := lt_of_le_of_ne hbt hbne
    have hle : b i ≤ (i : ℝ) := hmax (b i) (Finset.mem_insert_of_mem hbK) hbless
    exact (not_le_of_gt (hblt i)) hle
  · rintro ⟨i, hi⟩
    exact hgap i t hi

end MathlibAux
