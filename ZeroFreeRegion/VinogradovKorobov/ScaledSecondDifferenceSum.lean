import ZeroFreeRegion.VinogradovKorobov.SecondDifferenceSum
import ZeroFreeRegion.VinogradovKorobov.ThirdDifferenceScale

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- Explicit scale bound obtained by inserting the `h k / (81 x^3)` third
difference lower bound into the twice-differenced Kusmin--Landau estimate. -/
theorem iteratedShiftedZetaPhase_two_kusminLandau_scaled_range
    (t : ℝ) (h k m R : ℕ)
    (ht : 0 < t) (hh : 0 < h) (hk : 0 < k) (hm : 0 < m)
    (hR : 1 ≤ R) (hhm : h ≤ m) (hkm : k ≤ m)
    (hturn :
      t * logSecondDifferenceDecrement h k m ≤
        2 * Real.pi -
          t * logSecondDifferenceDecrement h k
            ((m + (R - 1) : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.range R,
        phaseTerm
          (iteratedPhaseDifference [h, k] (shiftedZetaPhase t m)) n‖ ≤
      162 * Real.pi * ((m + (R - 1) : ℕ) : ℝ) ^ 3 /
        (t * h * k) := by
  let x : ℝ := ((m + (R - 1) : ℕ) : ℝ)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast (show 1 ≤ m + (R - 1) by omega)
  have hhR : 0 < (h : ℝ) := Nat.cast_pos.mpr hh
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hhx : (h : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hhm.trans (Nat.le_add_right m (R - 1))
  have hkx : (k : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hkm.trans (Nat.le_add_right m (R - 1))
  have hdec :
      (h : ℝ) * k / (81 * x ^ 3) ≤
        logSecondDifferenceDecrement h k x :=
    div_eightyOne_cube_le_logSecondDifferenceDecrement
      hx hhR hkR hhx hkx
  have hden :
      t * ((h : ℝ) * k / (81 * x ^ 3)) ≤
        t * logSecondDifferenceDecrement h k x :=
    mul_le_mul_of_nonneg_left hdec ht.le
  have hsmallPos :
      0 < t * ((h : ℝ) * k / (81 * x ^ 3)) := by positivity
  have hbase := iteratedShiftedZetaPhase_two_kusminLandau_range
    t h k m R ht hh hk hm hR hturn
  dsimp [x] at hden hsmallPos
  calc
    ‖∑ n ∈ Finset.range R,
        phaseTerm
          (iteratedPhaseDifference [h, k] (shiftedZetaPhase t m)) n‖ ≤
        2 * Real.pi /
          (t * logSecondDifferenceDecrement h k
            ((m + (R - 1) : ℕ) : ℝ)) := hbase
    _ ≤ 2 * Real.pi /
          (t * ((h : ℝ) * k /
            (81 * ((m + (R - 1) : ℕ) : ℝ) ^ 3))) :=
      div_le_div_of_nonneg_left (by positivity) hsmallPos hden
    _ = 162 * Real.pi * ((m + (R - 1) : ℕ) : ℝ) ^ 3 /
          (t * h * k) := by
      field_simp
      ring

/-- Fully algebraic turn condition for the scaled second-difference bound.
The hypothesis `5 t h k ≤ π m^3` guarantees that every third difference on
the block stays inside one nonresonant turn. -/
theorem iteratedShiftedZetaPhase_two_kusminLandau_scaled_range_of_start_scale
    (t : ℝ) (h k m R : ℕ)
    (ht : 0 < t) (hh : 0 < h) (hk : 0 < k) (hm : 0 < m)
    (hR : 1 ≤ R) (hhm : h ≤ m) (hkm : k ≤ m)
    (hscale :
      5 * t * (h : ℝ) * (k : ℝ) ≤ Real.pi * (m : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.range R,
        phaseTerm
          (iteratedPhaseDifference [h, k] (shiftedZetaPhase t m)) n‖ ≤
      162 * Real.pi * ((m + (R - 1) : ℕ) : ℝ) ^ 3 /
        (t * h * k) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hmOne : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hhR : 0 < (h : ℝ) := Nat.cast_pos.mpr hh
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hhmR : (h : ℝ) ≤ (m : ℝ) := by exact_mod_cast hhm
  have hkmR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
  have hfrac := decrementFraction_le_five_mul_div_cube
    hmOne hhR hkR hhmR hkmR
  have hdec := logSecondDifferenceDecrement_le_fraction hmR hhR hkR
  have hdecScale :
      logSecondDifferenceDecrement h k m ≤
        5 * (h : ℝ) * k / (m : ℝ) ^ 3 := hdec.trans hfrac
  have hscaleDiv :
      5 * t * (h : ℝ) * k / (m : ℝ) ^ 3 ≤ Real.pi :=
    (div_le_iff₀ (pow_pos hmR 3)).2 hscale
  have hstart :
      t * logSecondDifferenceDecrement h k m ≤ Real.pi := by
    calc
      t * logSecondDifferenceDecrement h k m ≤
          t * (5 * (h : ℝ) * k / (m : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hdecScale ht.le
      _ = 5 * t * (h : ℝ) * k / (m : ℝ) ^ 3 := by ring
      _ ≤ Real.pi := hscaleDiv
  have hendPos : 0 < ((m + (R - 1) : ℕ) : ℝ) := by
    exact Nat.cast_pos.mpr (by omega)
  have hmEnd : (m : ℝ) ≤ ((m + (R - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_right m (R - 1)
  have hend :
      logSecondDifferenceDecrement h k ((m + (R - 1) : ℕ) : ℝ) ≤
        logSecondDifferenceDecrement h k m :=
    antitoneOn_logSecondDifferenceDecrement hhR hkR hmR hendPos hmEnd
  have hendT :
      t * logSecondDifferenceDecrement h k
          ((m + (R - 1) : ℕ) : ℝ) ≤
        t * logSecondDifferenceDecrement h k m :=
    mul_le_mul_of_nonneg_left hend ht.le
  have hturn :
      t * logSecondDifferenceDecrement h k m ≤
        2 * Real.pi -
          t * logSecondDifferenceDecrement h k
            ((m + (R - 1) : ℕ) : ℝ) := by
    nlinarith
  exact iteratedShiftedZetaPhase_two_kusminLandau_scaled_range
    t h k m R ht hh hk hm hR hhm hkm hturn

end ZeroFreeRegion.VinogradovKorobov
