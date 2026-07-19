import HardyTheorem.ShortIntervalDistinctZeroCount
import MathlibAux.IntervalPackingFromMeasure

open Complex MeasureTheory Set

namespace HardyTheorem

/-!
# The final Hardy--Littlewood packing bridge

This file converts a fixed-length good-window estimate into a linear lower
bound for the number of distinct critical-line zeros.  The analytic input is
kept abstract: almost every start in a high dyadic block is good, and each
good start detects a zero in its associated window.
-/

/-- A fixed window length, a uniform bad-start measure bound, and zero
detection on every good window imply the Hardy--Littlewood linear lower
bound for distinct critical-line zeros. -/
theorem hardy_littlewood_lower_bound_target_of_good_window_measure
    (H T0 : ℝ) (good : ℝ → Set ℝ) (hH : 0 < H)
    (hbad : ∀ T ≥ T0,
      volume.real (Set.Icc T (2 * T - H) \ good T) ≤ T / 12)
    (hhit : ∀ T ≥ T0, ∀ t ∈ good T ∩ Set.Icc T (2 * T - 2 * H),
      ∃ u ∈ Set.Ioo t (t + H),
        riemannZeta ((1 / 2 : ℂ) + I * u) = 0) :
    hardy_littlewood_lower_bound_target := by
  let C : ℝ := 1 / (24 * H)
  let X0 : ℝ := 2 * max T0 (8 * H)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, X0, ?_⟩
  intro X hX
  let T : ℝ := X / 2
  have hTlarge : max T0 (8 * H) ≤ T := by
    dsimp only [T, X0] at hX ⊢
    linarith
  have hT0 : T0 ≤ T := (le_max_left _ _).trans hTlarge
  have hT8H : 8 * H ≤ T := (le_max_right _ _).trans hTlarge
  have hTpos : 0 < T := by linarith
  have hab : T ≤ 2 * T - H := by linarith
  obtain ⟨G, start, hGcard, hstart, hdisj⟩ :=
    MathlibAux.exists_many_pairwiseDisjoint_windows_of_measure_compl_le
      (good T) T (2 * T - H) H (T / 12) hH hab (hbad T hT0)
  have hcountNat : G.card ≤ criticalLineDistinctZeroCount (2 * T) := by
    apply card_le_criticalLineDistinctZeroCount_of_pairwiseDisjoint_hits
      G (fun i ↦ Set.Ioo (start i) (start i + H)) (2 * T) hdisj
    intro i hi
    have hsi := hstart i hi
    have hsi' : start i ∈ good T ∩ Set.Icc T (2 * T - 2 * H) := by
      rcases hsi with ⟨hgood, hlow, hupp⟩
      exact ⟨hgood, hlow, by linarith⟩
    obtain ⟨u, huWindow, huZero⟩ := hhit T hT0 (start i) hsi'
    refine ⟨u, ⟨huWindow, ?_, ?_⟩, huZero⟩
    · have hstartNonneg : 0 ≤ start i := hTpos.le.trans hsi'.2.1
      exact hstartNonneg.trans huWindow.1.le
    · nlinarith [hsi'.2.2, huWindow.2]
  have hcountReal :
      (G.card : ℝ) ≤ (criticalLineDistinctZeroCount (2 * T) : ℝ) := by
    exact_mod_cast hcountNat
  let q : ℝ := (T - H) / (3 * H)
  have hfloorLower : q - 1 ≤ (Nat.floor q : ℝ) :=
    (Nat.sub_one_lt_floor q).le
  have halgebra :
      T / (12 * H) ≤ q - 1 - (T / 12) / H := by
    have hnonneg : 0 ≤ (T - 8 * H) / (6 * H) := by
      exact div_nonneg (by linarith) (by positivity)
    have hid :
        q - 1 - (T / 12) / H - T / (12 * H) =
          (T - 8 * H) / (6 * H) := by
      dsimp only [q]
      field_simp [ne_of_gt hH]
      all_goals ring_nf
    linarith
  have hpack : T / (12 * H) ≤ (G.card : ℝ) := by
    calc
      T / (12 * H) ≤ q - 1 - (T / 12) / H := halgebra
      _ ≤ (Nat.floor q : ℝ) - (T / 12) / H :=
        sub_le_sub_right hfloorLower _
      _ ≤ (G.card : ℝ) := by
        dsimp only [q]
        convert hGcard using 1
        all_goals ring_nf
  rw [zeroCountOnCriticalLine_eq_criticalLineDistinctZeroCount]
  calc
    C * X = T / (12 * H) := by
      dsimp only [C, T]
      field_simp [ne_of_gt hH]
      all_goals ring_nf
    _ ≤ (G.card : ℝ) := hpack
    _ ≤ (criticalLineDistinctZeroCount (2 * T) : ℝ) := hcountReal
    _ = (criticalLineDistinctZeroCount X : ℝ) := by
      congr 2
      dsimp only [T]
      ring

end HardyTheorem
