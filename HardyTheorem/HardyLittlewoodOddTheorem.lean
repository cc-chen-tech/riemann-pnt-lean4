import HardyTheorem.HardyGoodWindowMeasure
import HardyTheorem.ShortIntervalSignChangeMeasure
import MathlibAux.ContinuousLocalSignChange
import MathlibAux.IntervalPackingFromMeasure

open Complex MeasureTheory Set

namespace HardyTheorem

/-!
# The odd-multiplicity Hardy--Littlewood theorem

Strict cancellation in each good short interval forces Hardy's `Z` function
to take both signs.  Bounded-height finiteness of its zero set upgrades this
to a genuine local sign change, hence to an odd-order zeta zero.  The existing
interval-packing argument then gives linearly many such zeros.
-/

/-- Hardy's `Z` function is nonzero somewhere in every nonempty real
interval. -/
theorem exists_hardyZ_ne_zero_Ioo {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Set.Ioo a b, hardyZ t ≠ 0 := by
  let B : ℝ := max |a| |b|
  let Z : Set ℝ := {t | |t| ≤ B ∧ hardyZ t = 0}
  have hZfinite : Z.Finite := by
    simpa only [Z] using
      PrimeNumberTheorem.hardyZ_zeros_bounded_height_finite B
  have hIooInfinite : (Set.Ioo a b).Infinite := Set.Ioo_infinite hab
  have hnotSubset : ¬ Set.Ioo a b ⊆ Z := by
    intro hsubset
    exact hIooInfinite (hZfinite.subset hsubset)
  obtain ⟨t, ht, htZ⟩ := Set.not_subset.mp hnotSubset
  refine ⟨t, ht, ?_⟩
  intro htzero
  apply htZ
  refine ⟨?_, htzero⟩
  dsimp only [B]
  exact abs_le_max_abs_abs ht.1.le ht.2.le

/-- Strict cancellation in a Hardy short integral produces a genuine local
sign-changing Hardy `Z` zero in the open interval. -/
theorem exists_hardyZ_localSignChange_of_strict_shortIntegral
    {delta t : ℝ} (hdelta : 0 ≤ delta)
    (hstrict : |hardyShortIntegral delta t| <
      hardyShortAbsIntegral delta t) :
    ∃ u ∈ Set.Ioo t (t + delta), HasLocalSignChangeAt hardyZ u := by
  have hchange :=
    MathlibAux.exists_local_sign_change_of_abs_intervalIntegral_lt_intervalIntegral_abs
      hardyZ_continuous (show t ≤ t + delta by linarith)
      (by simpa only [hardyShortIntegral, hardyShortAbsIntegral] using hstrict)
      (fun a b hab => exists_hardyZ_ne_zero_Ioo hab)
  simpa only [HasLocalSignChangeAt, HasNegToPosLocalSignChangeAt,
    HasPosToNegLocalSignChangeAt] using hchange

/-- A fixed good-window estimate and local sign-change detection imply a
linear lower bound for odd-multiplicity critical-line zeros. -/
theorem hardy_littlewood_odd_lower_bound_target_of_good_window_measure
    (H T0 : ℝ) (good : ℝ → Set ℝ) (hH : 0 < H)
    (hbad : ∀ T ≥ T0,
      volume.real (Set.Icc T (2 * T - H) \ good T) ≤ T / 12)
    (hhit : ∀ T ≥ T0, ∀ t ∈ good T ∩ Set.Icc T (2 * T - 2 * H),
      ∃ u ∈ Set.Ioo t (t + H), HasLocalSignChangeAt hardyZ u) :
    hardy_littlewood_odd_lower_bound_target := by
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
  have hcountNat : G.card ≤ criticalLineOddZeroCount (2 * T) := by
    apply card_le_criticalLineOddZeroCount_of_pairwiseDisjoint_hardyZ_localSignChanges
      G (fun i ↦ Set.Ioo (start i) (start i + H)) (2 * T) hdisj
    intro i hi
    have hsi := hstart i hi
    have hsi' : start i ∈ good T ∩ Set.Icc T (2 * T - 2 * H) := by
      rcases hsi with ⟨hgood, hlow, hupp⟩
      exact ⟨hgood, hlow, by linarith⟩
    obtain ⟨u, huWindow, huChange⟩ := hhit T hT0 (start i) hsi'
    refine ⟨u, huWindow, ?_, huChange⟩
    constructor
    · exact hTpos.le.trans (hsi'.2.1.trans huWindow.1.le)
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
  calc
    C * X = T / (12 * H) := by
      dsimp only [C, T]
      field_simp [ne_of_gt hH]
      all_goals ring_nf
    _ ≤ (G.card : ℝ) := hpack
    _ ≤ (criticalLineOddZeroCount (2 * T) : ℝ) := hcountReal
    _ = (criticalLineOddZeroCount X : ℝ) := by
      congr 2
      dsimp only [T]
      ring

/-- Hardy--Littlewood's linear lower bound for odd-multiplicity critical-line
zeta zeros, each ordinate counted once. -/
theorem hardy_littlewood_odd_lower_bound_target_proved :
    hardy_littlewood_odd_lower_bound_target := by
  obtain ⟨H, hH, T0, _hT0, hbad⟩ :=
    exists_fixed_window_bad_start_measure_le
  apply hardy_littlewood_odd_lower_bound_target_of_good_window_measure
    H T0 (fun _T => hardyGoodWindowStarts H) hH
  · intro T hT
    exact hbad T hT
  · intro T _hT t ht
    exact exists_hardyZ_localSignChange_of_strict_shortIntegral hH.le ht.1

end HardyTheorem
