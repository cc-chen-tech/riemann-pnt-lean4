import MathlibAux.MinReciprocalSquareSum
import MathlibAux.SeparatedFrequencyPacking

open scoped BigOperators

namespace MathlibAux

/-- A reciprocal envelope that is finite at its stationary point. -/
noncomputable def stationaryMinReciprocalEnvelope (H xi x : ℝ) : ℝ :=
  if x = xi then H else min H (2 / |x - xi|)

private noncomputable def radialLexKey (xi x : ℝ) : ℝ ×ₗ ℝ :=
  toLex (|x - xi|, x)

/-- The square sum of the stationary-safe reciprocal envelope over a separated
frequency set is bounded independently of the number of frequencies. -/
theorem sum_sq_stationaryMinReciprocalEnvelope_le
    (S : Finset ℝ) (Delta H xi : ℝ)
    (hDelta : 0 < Delta) (hH : 0 ≤ H)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Delta ≤ |x - y|) :
    (∑ x ∈ S, (stationaryMinReciprocalEnvelope H xi x) ^ 2) ≤
      H ^ 2 + 12 * H / Delta := by
  classical
  by_cases hHzero : H = 0
  · subst H
    have henv : ∀ x : ℝ, stationaryMinReciprocalEnvelope 0 xi x = 0 := by
      intro x
      rw [stationaryMinReciprocalEnvelope]
      split_ifs
      · rfl
      · exact min_eq_left (div_nonneg (by norm_num) (abs_nonneg _))
    simp only [henv, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero]
    positivity
  have hHpos : 0 < H := lt_of_le_of_ne hH (Ne.symm hHzero)
  let radialLE : ℝ → ℝ → Prop :=
    fun x y ↦ radialLexKey xi x ≤ radialLexKey xi y
  letI : IsTrans ℝ radialLE := ⟨by
    intro x y z hxy hyz
    exact hxy.trans hyz⟩
  letI : Std.Refl radialLE := ⟨by
    intro x
    exact le_rfl⟩
  letI : Std.Antisymm radialLE := ⟨by
    intro x y hxy hyx
    have hkey : radialLexKey xi x = radialLexKey xi y :=
      le_antisymm hxy hyx
    have hpairs :
        (|x - xi|, x) = (|y - xi|, y) := by
      exact congrArg ofLex hkey
    exact congrArg Prod.snd hpairs⟩
  letI : Std.Total radialLE := ⟨by
    intro x y
    exact le_total (radialLexKey xi x) (radialLexKey xi y)⟩
  let L := S.sort radialLE
  let f : ℕ → ℝ := fun k ↦ L.getD k 0
  have hlength : L.length = S.card :=
    Finset.length_sort radialLE
  have hpair : L.Pairwise radialLE :=
    Finset.pairwise_sort S radialLE
  have hnodup : L.Nodup :=
    Finset.sort_nodup S radialLE
  have hmem (k : ℕ) (hk : k < L.length) : f k ∈ S := by
    rw [← Finset.mem_sort radialLE]
    rw [show f k = L.get ⟨k, hk⟩ from List.getD_eq_get L 0 ⟨k, hk⟩]
    exact List.get_mem L ⟨k, hk⟩
  have hf (k : ℕ) (hk : k < L.length) :
      f k = L.get ⟨k, hk⟩ :=
    List.getD_eq_get L 0 ⟨k, hk⟩
  let F : ℝ → ℝ :=
    fun x ↦ (stationaryMinReciprocalEnvelope H xi x) ^ 2
  have hsum :
      (∑ k ∈ Finset.range S.card, F (f k)) =
        ∑ x ∈ S, F x := by
    apply Finset.sum_bij (fun k _hk ↦ f k)
    · intro k hk
      have hkL : k < L.length := by
        rw [hlength]
        exact Finset.mem_range.mp hk
      exact hmem k hkL
    · intro k₁ hk₁ k₂ hk₂ heq
      have hk₁L : k₁ < L.length := by
        rw [hlength]
        exact Finset.mem_range.mp hk₁
      have hk₂L : k₂ < L.length := by
        rw [hlength]
        exact Finset.mem_range.mp hk₂
      have hindex :
          (⟨k₁, hk₁L⟩ : Fin L.length) = ⟨k₂, hk₂L⟩ := by
        apply hnodup.injective_get
        simpa [hf k₁ hk₁L, hf k₂ hk₂L] using heq
      exact Fin.ext_iff.mp hindex
    · intro x hx
      have hxL : x ∈ L := by
        rw [Finset.mem_sort radialLE]
        exact hx
      obtain ⟨k, hk⟩ := List.mem_iff_get.mp hxL
      refine ⟨k, ?_, ?_⟩
      · exact Finset.mem_range.mpr (by simpa [hlength] using k.isLt)
      · simpa [hf k k.isLt] using hk
    · intro k hk
      rfl
  have hfirst (x : ℝ) : F x ≤ H ^ 2 := by
    have henv_nonneg : 0 ≤ stationaryMinReciprocalEnvelope H xi x := by
      rw [stationaryMinReciprocalEnvelope]
      split_ifs
      · exact hH
      · exact le_min hH (div_nonneg (by norm_num) (abs_nonneg _))
    have henv_le : stationaryMinReciprocalEnvelope H xi x ≤ H := by
      rw [stationaryMinReciprocalEnvelope]
      split_ifs
      · exact le_rfl
      · exact min_le_left _ _
    exact (sq_le_sq₀ henv_nonneg hH).2 henv_le
  have hpoint (j : ℕ) (hj : j ∈ Finset.Icc 1 (S.card - 1)) :
      F (f j) ≤ (min H ((4 / Delta) / j)) ^ 2 := by
    have hjBounds := Finset.mem_Icc.mp hj
    have hjPos : 0 < j := Nat.zero_lt_of_lt hjBounds.1
    have hjLt : j < S.card := by omega
    have hjL : j < L.length := by simpa [hlength] using hjLt
    have hprefixLen : j + 1 ≤ L.length := by omega
    let T : Finset ℝ := (L.take (j + 1)).toFinset
    have hcardT : T.card = j + 1 := by
      rw [show T = (L.take (j + 1)).toFinset from rfl]
      rw [List.toFinset_card_of_nodup
        (List.Pairwise.take (i := j + 1) hnodup)]
      exact List.length_take_of_le hprefixLen
    have hTmem (y : ℝ) (hy : y ∈ T) : y ∈ S := by
      rw [← Finset.mem_sort radialLE]
      apply List.mem_of_mem_take
      simpa [T] using hy
    have hballT : ∀ y ∈ T, |y - xi| ≤ |f j - xi| := by
      intro y hy
      have hyTake : y ∈ L.take (j + 1) := by simpa [T] using hy
      obtain ⟨i, hi, hiy⟩ := List.mem_take_iff_getElem.mp hyTake
      have hiL : i < L.length := lt_of_lt_of_le hi (Nat.min_le_right _ _)
      have hij : i ≤ j := by
        have : i < j + 1 := lt_of_lt_of_le hi (Nat.min_le_left _ _)
        omega
      have hkey :
          radialLexKey xi L[i] ≤ radialLexKey xi L[j] := by
        simpa [radialLE, List.get_eq_getElem] using
          hpair.rel_get_of_le
            (show (⟨i, hiL⟩ : Fin L.length) ≤ ⟨j, hjL⟩ by
              exact hij)
      have hradius :=
        Prod.Lex.monotone_fst
          (radialLexKey xi L[i]) (radialLexKey xi L[j]) hkey
      simpa [radialLexKey, hiy, hf j hjL] using hradius
    have hpack :=
      card_sub_one_mul_separation_le_two_mul_radius
        T Delta xi |f j - xi| hDelta (abs_nonneg _)
        (fun x hx y hy hxy ↦ hsep x (hTmem x hx) y (hTmem y hy) hxy)
        hballT
    have hradial : (j : ℝ) * Delta ≤ 2 * |f j - xi| := by
      simpa [hcardT] using hpack
    have hjRealPos : 0 < (j : ℝ) := by exact_mod_cast hjPos
    have hjDeltaPos : 0 < (j : ℝ) * Delta := mul_pos hjRealPos hDelta
    have hradiusPos : 0 < |f j - xi| := by nlinarith
    have hne : f j ≠ xi := by
      intro heq
      simp [heq] at hradiusPos
    have hrecip :
        2 / |f j - xi| ≤ 4 / ((j : ℝ) * Delta) := by
      apply (div_le_div_iff₀ hradiusPos hjDeltaPos).2
      nlinarith
    have htarget :
        (4 / Delta) / (j : ℝ) = 4 / ((j : ℝ) * Delta) := by
      field_simp
    have henv_nonneg : 0 ≤ stationaryMinReciprocalEnvelope H xi (f j) := by
      rw [stationaryMinReciprocalEnvelope, if_neg hne]
      exact le_min hH (div_nonneg (by norm_num) (abs_nonneg _))
    have htarget_nonneg :
        0 ≤ min H ((4 / Delta) / (j : ℝ)) := by
      rw [htarget]
      exact le_min hH (div_nonneg (by norm_num) hjDeltaPos.le)
    have henv_le :
        stationaryMinReciprocalEnvelope H xi (f j) ≤
          min H ((4 / Delta) / (j : ℝ)) := by
      rw [stationaryMinReciprocalEnvelope, if_neg hne, htarget]
      exact min_le_min le_rfl hrecip
    exact (sq_le_sq₀ henv_nonneg htarget_nonneg).2 henv_le
  by_cases hS : S.card = 0
  · have : S = ∅ := Finset.card_eq_zero.mp hS
    simp [this]
    positivity
  have hScard : 0 < S.card := Nat.pos_of_ne_zero hS
  have htail :
      (∑ k ∈ Finset.range (S.card - 1), F (f (k + 1))) ≤
        12 * H / Delta := by
    calc
      (∑ k ∈ Finset.range (S.card - 1), F (f (k + 1))) ≤
          ∑ k ∈ Finset.range (S.card - 1),
            (min H ((4 / Delta) / (k + 1 : ℕ))) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        apply hpoint (k + 1)
        exact Finset.mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le k), by
          have hklt := Finset.mem_range.mp hk
          omega⟩
      _ = ∑ j ∈ Finset.Icc 1 (S.card - 1),
            (min H ((4 / Delta) / j)) ^ 2 := by
        have hIcc :
            Finset.Icc 1 (S.card - 1) =
              Finset.Ico 1 ((S.card - 1) + 1) := by
          ext j
          simp only [Finset.mem_Icc, Finset.mem_Ico]
          omega
        rw [hIcc, Finset.sum_Ico_eq_sum_range]
        simp only [Nat.cast_add, Nat.cast_one]
        congr 1
        funext k
        ring_nf
      _ ≤ 3 * (4 / Delta) * H :=
        sum_sq_min_div_le (S.card - 1) hHpos
          (div_nonneg (by norm_num) hDelta.le)
      _ = 12 * H / Delta := by
        field_simp
        ring
  rw [← hsum]
  rw [show S.card = (S.card - 1) + 1 by omega, Finset.sum_range_succ']
  convert add_le_add (hfirst (f 0)) htail using 1 <;> ring_nf

end MathlibAux
