/-
# DRAFT (uncompiled): L1 Appendix B — windowed zero count, full proof

Paper proof: `docs/research/detection-point-choice-proof-draft.md`
(Appendix B).  Uncompiled; tactic details may need adjustment.

Mathlib lemmas verified in local sources:
- `norm_image_sub_le_of_norm_deriv_le_segment`
  (Mathlib/Analysis/Calculus/MeanValue.lean:337)
- `hasDerivAt_riemannVonMangoldtMainTerm`
  (repo, RiemannVonMangoldt/AllHeightAsymptotic.lean:10)
- `exists_abs_riemannZeroCount_sub_mainTerm_le_log`
  (same file, line 81)

PRE-REVIEW RISK LIST (checked by hand, to fix at first compile):
1. `derivWithin` vs `deriv`: the segment bound needs
   `‖derivWithin f (Icc a b) x‖ ≤ C`, while
   `hasDerivAt_riemannVonMangoldtMainTerm` gives the plain derivative.
   Fix: `HasDerivAt.hasDerivWithinAt` + the uniqueness lemma
   (candidates: `derivWithin_of_hasDerivWithinAt`,
   `HasDerivWithinAt.derivWithin_eq`, or
   `DifferentiableAt.derivWithin_eq` — verify exact name at compile time).
   At `x = T0` (left boundary, included in `Ico`) the uniqueness lemma
   must not need `nhdsWithin = nhds`; if it does, split `x = T0` by
   continuity or use the `Ioo` variant of the bound set.
2. `hlog_le`'s chain `x/(2π) ≤ x ≤ T0+H+6` uses `x ≥ 8`; fine, but the
   `div_le_iff₀` step is fussy — `nlinarith [Real.pi_pos]` should carry it.
3. Final constant packing `H L + 2 C0 L ≤ (C0+1)(H L + L)` reduces to
   `L ≥ 0` and `C0 H ≥ 0`; the `ring` normalization in the draft may need
   `ring_nf` instead.
4. `exact_mod_cast` on `Int.card_Ioo` is not used here (that is Appendix
   A); no ceiling appears in this file.
-/
import PrimeNumberTheorem.RiemannVonMangoldt.AllHeightAsymptotic

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt
namespace WindowedCount

open Set

/-- The main-term difference over `[T0, T0+H]` is bounded by `H` times a
logarithmic factor, for `8 <= T0`. -/
lemma abs_mainTerm_sub_le_mul_log_of_interval
    {T0 H : ℝ} (hT0 : 8 ≤ T0) (hH : 0 ≤ H) :
    |riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0| ≤
      H * (1 + Real.log (T0 + H + 6)) := by
  by_cases hH0 : H = 0
  · subst hH0; simp
  · have hHpos : 0 < H := lt_of_le_of_ne hH (Ne.symm hH0)
    have hT0pos : 0 < T0 := by linarith
    let C : ℝ := 1 + Real.log (T0 + H + 6)
    have hC0 : 0 ≤ C := by dsimp [C]; linarith [Real.log_nonneg (by linarith)]
    have hdiff : DifferentiableOn ℝ riemannVonMangoldtMainTerm (Icc T0 (T0 + H)) := by
      intro x hx
      have hx0 : x ≠ 0 := by
        have : 8 ≤ x := le_trans hT0 (by linarith [hx.1])
        linarith
      exact (hasDerivAt_riemannVonMangoldtMainTerm hx0).differentiableAt.differentiableWithinAt
    have hbound : ∀ x ∈ Ico T0 (T0 + H),
        ‖derivWithin riemannVonMangoldtMainTerm (Icc T0 (T0 + H)) x‖ ≤ C := by
      intro x hx
      have hx0 : x ≠ 0 := by
        have : 8 ≤ x := le_trans hT0 (by linarith [hx.1])
        linarith
      have hderiv : deriv riemannVonMangoldtMainTerm x =
          Real.log (x / (2 * Real.pi)) / (2 * Real.pi) := by
        exact (hasDerivAt_riemannVonMangoldtMainTerm hx0).deriv
      rw [hderiv]
      have hxpi : 1 ≤ x / (2 * Real.pi) := by
        have : 8 / (2 * Real.pi) ≤ x / (2 * Real.pi) :=
          div_le_div_of_nonneg_right hT0 (by positivity : 0 ≤ (2 * Real.pi))
        have : 1 ≤ 8 / (2 * Real.pi) := by
          have : (2 : ℝ) * Real.pi ≤ 8 := by nlinarith [Real.pi_le_four]
          exact one_le_div.mpr this
        linarith
      have hlog_nonneg : 0 ≤ Real.log (x / (2 * Real.pi)) := Real.log_nonneg hxpi
      have hlog_le : Real.log (x / (2 * Real.pi)) ≤ Real.log (T0 + H + 6) := by
        exact Real.log_le_log (by positivity) (by
          have : x / (2 * Real.pi) ≤ x := by
            have : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_pos]
            exact (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr (by
              exact (le_mul_iff_one_le_right (by positivity : 0 < 2 * Real.pi)).mpr (by linarith))
          exact le_trans this (by linarith [hx.2, le_add_of_nonneg_right (by norm_num : 0 ≤ (6 : ℝ))]))
      calc
        ‖Real.log (x / (2 * Real.pi)) / (2 * Real.pi)‖
            = Real.log (x / (2 * Real.pi)) / (2 * Real.pi) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlog_nonneg (by positivity))]
        _ ≤ Real.log (T0 + H + 6) := by
          calc
            Real.log (x / (2 * Real.pi)) / (2 * Real.pi) ≤ Real.log (x / (2 * Real.pi)) := by
              exact div_le_self hlog_nonneg (by nlinarith [Real.pi_pos])
            _ ≤ Real.log (T0 + H + 6) := hlog_le
        _ ≤ C := by dsimp [C]; linarith
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment
      (f := riemannVonMangoldtMainTerm) (a := T0) (b := T0 + H) (C := C)
      hdiff hbound (T0 + H) (by exact ⟨le_of_lt (lt_add_of_pos_left T0 hHpos), le_rfl⟩)
    simpa using hmv

/-- MAIN TARGET: windowed positive-side zero count. -/
theorem exists_windowedRiemannZeroCount_le
    (T0 H : ℝ) (hT0 : 8 ≤ T0) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧
      ((riemannZeroCount (T0 + H) : ℝ) - riemannZeroCount T0) ≤
        C * (H * (1 + Real.log (T0 + H + 6)) + (1 + Real.log (T0 + H + 6))) := by
  rcases exists_abs_riemannZeroCount_sub_mainTerm_le_log with ⟨C0, hC0, hb⟩
  let L : ℝ := 1 + Real.log (T0 + H + 6)
  have hL0 : 0 ≤ L := by dsimp [L]; linarith [Real.log_nonneg (by linarith)]
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hT0H : 8 ≤ T0 + H := le_trans hT0 (by linarith [hH])
  have hNsub :
      ((riemannZeroCount (T0 + H) : ℝ) - riemannZeroCount T0) ≤
        |riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0|
          + C0 * L + C0 * (1 + Real.log (T0 + 6)) := by
    have hbH := hb (T0 + H) hT0H
    have hb0 := hb T0 hT0
    have hdiff_eq :
        (riemannZeroCount (T0 + H) : ℝ) - riemannZeroCount T0 =
          (riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0)
            + ((riemannZeroCount (T0 + H) : ℝ) - riemannVonMangoldtMainTerm (T0 + H))
            - ((riemannZeroCount T0 : ℝ) - riemannVonMangoldtMainTerm T0) := by
      ring
    rw [hdiff_eq]
    have h1 : (riemannZeroCount (T0 + H) : ℝ) - riemannVonMangoldtMainTerm (T0 + H)
        ≤ |(riemannZeroCount (T0 + H) : ℝ) - riemannVonMangoldtMainTerm (T0 + H)| :=
      le_abs_self _
    have h2 : -((riemannZeroCount T0 : ℝ) - riemannVonMangoldtMainTerm T0)
        ≤ |(riemannZeroCount T0 : ℝ) - riemannVonMangoldtMainTerm T0| :=
      neg_le_abs_self _
    calc
      (riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0)
            + ((riemannZeroCount (T0 + H) : ℝ) - riemannVonMangoldtMainTerm (T0 + H))
            - ((riemannZeroCount T0 : ℝ) - riemannVonMangoldtMainTerm T0)
        ≤ |riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0|
            + |(riemannZeroCount (T0 + H) : ℝ) - riemannVonMangoldtMainTerm (T0 + H)|
            + |(riemannZeroCount T0 : ℝ) - riemannVonMangoldtMainTerm T0| := by
          have hm : riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0
              ≤ |riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0| :=
            le_abs_self _
          linarith [hm, h1, h2]
        _ ≤ |riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0|
            + C0 * L + C0 * (1 + Real.log (T0 + 6)) := by
          have hlog : 1 + Real.log (T0 + H + 6) ≤ L := by dsimp [L]; rfl
          linarith [hbH, hb0]
  have hmain : |riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0| ≤
      H * L := by
    simpa [L] using abs_mainTerm_sub_le_mul_log_of_interval hT0 hH
  have hlog : 1 + Real.log (T0 + 6) ≤ L := by
    dsimp [L]
    gcongr
    exact Real.log_le_log (by linarith) (by linarith)
  refine ⟨C0 + 1, by positivity, ?_⟩
  calc
    (riemannZeroCount (T0 + H) : ℝ) - riemannZeroCount T0 ≤
        |riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0|
          + C0 * L + C0 * (1 + Real.log (T0 + 6)) := hNsub
    _ ≤ H * L + C0 * L + C0 * L := by linarith [hmain, hlog]
    _ = H * L + 2 * C0 * L := by ring
    _ ≤ (C0 + 1) * (H * L + L) := by
      have hC0pos : 0 ≤ C0 := hC0
      -- (C0+1)(HL+L) = HL + L + C0HL + C0L ≥ HL + 2 C0 L
      -- ⟺ L + C0 H L ≥ C0 L  ⟺  L ≥ 0 与 C0 H ≥ 0 ✓
      calc
        H * L + 2 * C0 * L = H * L + C0 * L + C0 * L := by ring
        _ ≤ H * L + C0 * L + L + C0 * (H * L) := by
          have h1 : C0 * L ≤ L + C0 * (H * L) := by
            calc
              C0 * L ≤ C0 * L + L := by linarith [hL0, hC0pos]
              _ ≤ C0 * L + L + C0 * (H * L) := by
                exact le_add_of_nonneg_right (mul_nonneg hC0pos (mul_nonneg hH hL0))
              _ = L + C0 * (H * L) + C0 * L := by ring
          linarith
        _ = H * L + L + C0 * H * L + C0 * L := by ring
        _ = (C0 + 1) * (H * L + L) := by ring

end WindowedCount
end RiemannVonMangoldt
end PrimeNumberTheorem
