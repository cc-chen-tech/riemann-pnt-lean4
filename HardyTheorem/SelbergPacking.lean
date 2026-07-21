import HardyTheorem.ShortIntervalSignChangeMeasure
import MathlibAux.IntervalPackingFromMeasure

open Complex MeasureTheory Set

namespace HardyTheorem

/-!
# Selberg-scale packing from local Hardy-Z sign changes

This file packages the finite combinatorial bridge needed by a Selberg-scale
short-interval argument: a small exceptional set of window starts and a local
Hardy-Z sign change in every remaining window force many odd-order zeros on
the critical line.
-/

/-- A bad-start measure bound and a local Hardy-Z sign change in every good
window give a finite lower bound for odd-order critical-line zeros.  The
`8 * H ≤ T` hypothesis absorbs the floor loss in the three-block packing. -/
theorem criticalLineOddZeroCount_two_mul_lower_bound_of_good_window_measure
    (T H : ℝ) (good : Set ℝ) (hH : 0 < H) (hT8H : 8 * H ≤ T)
    (hbad : volume.real (Set.Icc T (2 * T - H) \ good) ≤ T / 12)
    (hsign : ∀ t ∈ good ∩ Set.Icc T (2 * T - 2 * H),
      ∃ u ∈ Set.Ioo t (t + H), HasLocalSignChangeAt hardyZ u) :
    T / (12 * H) ≤ (criticalLineOddZeroCount (2 * T) : ℝ) := by
  have hTpos : 0 < T := by
    nlinarith [hH]
  have hab : T ≤ 2 * T - H := by
    linarith
  obtain ⟨G, start, hGcard, hstart, hdisj⟩ :=
    MathlibAux.exists_many_pairwiseDisjoint_windows_of_measure_compl_le
      good T (2 * T - H) H (T / 12) hH hab hbad
  have hcountNat : G.card ≤ criticalLineOddZeroCount (2 * T) := by
    apply card_le_criticalLineOddZeroCount_of_pairwiseDisjoint_hardyZ_localSignChanges
      G (fun i ↦ Set.Ioo (start i) (start i + H)) (2 * T) hdisj
    intro i hi
    have hsi := hstart i hi
    have hsi' : start i ∈ good ∩ Set.Icc T (2 * T - 2 * H) := by
      rcases hsi with ⟨hgood, hlow, hupp⟩
      exact ⟨hgood, hlow, by linarith⟩
    obtain ⟨u, huWindow, huSign⟩ := hsign (start i) hsi'
    refine ⟨u, huWindow, ?_, huSign⟩
    constructor
    · have hstartNonneg : 0 ≤ start i := hTpos.le.trans hsi'.2.1
      exact hstartNonneg.trans huWindow.1.le
    · nlinarith [hsi'.2.2, huWindow.2]
  have hcountReal :
      (G.card : ℝ) ≤ (criticalLineOddZeroCount (2 * T) : ℝ) := by
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
  exact hpack.trans hcountReal

/-- Eventual good windows of length `A / log T`, each carrying a local
Hardy-Z sign change, imply the repository's Selberg odd-zero proportion
target. -/
theorem selberg_odd_zero_proportion_target_of_log_good_window_measure
    (A T0 : ℝ) (good : ℝ → Set ℝ) (hA : 0 < A)
    (hbad : ∀ T ≥ T0,
      volume.real
          (Set.Icc T (2 * T - A / Real.log T) \ good T) ≤ T / 12)
    (hsign : ∀ T ≥ T0, ∀ t ∈
      good T ∩ Set.Icc T (2 * T - 2 * (A / Real.log T)),
      ∃ u ∈ Set.Ioo t (t + A / Real.log T),
        HasLocalSignChangeAt hardyZ u) :
    selberg_odd_zero_proportion_target := by
  let c : ℝ := Real.pi / (24 * A)
  let X0 : ℝ := 2 * max T0 (max (Real.exp 1) (8 * A))
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  refine ⟨c, hc, X0, ?_⟩
  intro X hX
  let T : ℝ := X / 2
  have hTlarge : max T0 (max (Real.exp 1) (8 * A)) ≤ T := by
    dsimp only [T, X0] at hX ⊢
    linarith
  have hT0 : T0 ≤ T :=
    (le_max_left _ _).trans hTlarge
  have hTexp : Real.exp 1 ≤ T :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hTlarge)
  have hT8A : 8 * A ≤ T :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hTlarge)
  have hTpos : 0 < T :=
    (Real.exp_pos 1).trans_le hTexp
  have hlogone : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]
    exact hTexp
  have hlogpos : 0 < Real.log T :=
    lt_of_lt_of_le zero_lt_one hlogone
  let H : ℝ := A / Real.log T
  have hH : 0 < H := by
    dsimp only [H]
    exact div_pos hA hlogpos
  have hHleA : H ≤ A := by
    dsimp only [H]
    apply (div_le_iff₀ hlogpos).2
    nlinarith [mul_le_mul_of_nonneg_left hlogone hA.le]
  have hT8H : 8 * H ≤ T := by
    calc
      8 * H ≤ 8 * A := mul_le_mul_of_nonneg_left hHleA (by norm_num)
      _ ≤ T := hT8A
  have hfinite :
      T / (12 * H) ≤ (criticalLineOddZeroCount (2 * T) : ℝ) :=
    criticalLineOddZeroCount_two_mul_lower_bound_of_good_window_measure
      T H (good T) hH hT8H
      (by simpa only [H] using hbad T hT0)
      (by simpa only [H] using hsign T hT0)
  have hlogtwo : Real.log 2 ≤ Real.log T := by
    calc
      Real.log 2 ≤ 2 - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
      _ ≤ Real.log T := hlogone
  have hlogTwoT : Real.log (2 * T) ≤ 2 * Real.log T := by
    calc
      Real.log (2 * T) = Real.log 2 + Real.log T :=
        Real.log_mul (by norm_num) (ne_of_gt hTpos)
      _ ≤ Real.log T + Real.log T := by linarith
      _ = 2 * Real.log T := by ring
  have hlogMul : T * Real.log (2 * T) ≤ 2 * T * Real.log T := by
    calc
      T * Real.log (2 * T) ≤ T * (2 * Real.log T) :=
        mul_le_mul_of_nonneg_left hlogTwoT hTpos.le
      _ = 2 * T * Real.log T := by ring
  have hX : X = 2 * T := by
    dsimp only [T]
    ring
  calc
    c * (X / (2 * Real.pi) * Real.log X) =
        T * Real.log (2 * T) / (24 * A) := by
      rw [hX]
      dsimp only [c]
      field_simp [ne_of_gt hA, ne_of_gt Real.pi_pos]
    _ ≤ (2 * T * Real.log T) / (24 * A) :=
      (div_le_div_iff_of_pos_right (by positivity)).2 hlogMul
    _ = T * Real.log T / (12 * A) := by ring
    _ = T / (12 * H) := by
      dsimp only [H]
      field_simp [ne_of_gt hA, ne_of_gt hlogpos]
    _ ≤ (criticalLineOddZeroCount (2 * T) : ℝ) := hfinite
    _ = (criticalLineOddZeroCount X : ℝ) := by
      congr 2
      exact hX.symm

end HardyTheorem
