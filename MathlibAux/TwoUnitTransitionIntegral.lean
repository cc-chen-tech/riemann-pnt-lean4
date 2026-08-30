import MathlibAux.PositiveRpowIntervalIntegral

/-! Integration over two unit transition intervals with a vanishing core. -/

open Set MeasureTheory

namespace MathlibAux

/-- A continuous function vanishing on the central plateau incurs only the
length of its two unit transition intervals. -/
theorem intervalIntegral_le_two_unit_transitions
    {f : ℝ → ℝ} {x N C : ℝ} (hxN : x ≤ N)
    (hf : ContinuousOn f (Icc (x - 1) (N + 1)))
    (hbound : ∀ u ∈ Icc (x - 1) (N + 1), f u ≤ C)
    (hzero : ∀ u ∈ Icc x N, f u = 0) :
    (∫ u in (x - 1)..(N + 1), f u) ≤ 2 * C := by
  have hl : IntervalIntegrable f volume (x - 1) x :=
    (hf.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc
      (by linarith)
  have hm : IntervalIntegrable f volume x N :=
    (hf.mono (Icc_subset_Icc (by linarith) (by linarith))).intervalIntegrable_of_Icc hxN
  have hr : IntervalIntegrable f volume N (N + 1) :=
    (hf.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc
      (by linarith)
  have hleft : (∫ u in (x - 1)..x, f u) ≤ C := by
    calc
      (∫ u in (x - 1)..x, f u) ≤ ∫ _u in (x - 1)..x, C := by
        apply intervalIntegral.integral_mono_on (by linarith) hl intervalIntegrable_const
        intro u hu
        exact hbound u ⟨hu.1, by linarith [hu.2]⟩
      _ = C := by simp
  have hright : (∫ u in N..(N + 1), f u) ≤ C := by
    calc
      (∫ u in N..(N + 1), f u) ≤ ∫ _u in N..(N + 1), C := by
        apply intervalIntegral.integral_mono_on (by linarith) hr intervalIntegrable_const
        intro u hu
        exact hbound u ⟨by linarith [hu.1], hu.2⟩
      _ = C := by simp
  have hmiddle : (∫ u in x..N, f u) = 0 := by
    calc
      (∫ u in x..N, f u) = ∫ _u in x..N, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact hzero u (by simpa [uIcc_of_le hxN] using hu)
      _ = 0 := by simp
  calc
    (∫ u in (x - 1)..(N + 1), f u) =
        (∫ u in (x - 1)..x, f u) + (∫ u in x..N, f u) +
          (∫ u in N..(N + 1), f u) := by
      rw [intervalIntegral.integral_add_adjacent_intervals hl hm,
        intervalIntegral.integral_add_adjacent_intervals (hl.trans hm) hr]
    _ ≤ 2 * C := by rw [hmiddle]; linarith

/-- Adding a decreasing real-power weight preserves the transition-only
cost; in particular there is no dependence on the central plateau length. -/
theorem intervalIntegral_abs_mul_rpow_le_two_unit_transitions
    {f : ℝ → ℝ} {x N C p : ℝ} (hx : 1 < x) (hxN : x ≤ N)
    (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hf : ContinuousOn f (Icc (x - 1) (N + 1)))
    (hbound : ∀ u ∈ Icc (x - 1) (N + 1), |f u| ≤ C)
    (hzero : ∀ u ∈ Icc x N, f u = 0) :
    (∫ u in (x - 1)..(N + 1), |f u| * u ^ (-p)) ≤
      2 * C * (x - 1) ^ (-p) := by
  have ha : 0 < x - 1 := by linarith
  have hpow : ContinuousOn (fun u : ℝ => u ^ (-p)) (Icc (x - 1) (N + 1)) := by
    intro u hu
    exact (Real.continuousAt_rpow_const u (-p)
      (Or.inl (ha.trans_le hu.1).ne')).continuousWithinAt
  have hweighted := intervalIntegral_le_two_unit_transitions
    (f := fun u => |f u| * u ^ (-p)) (C := C * (x - 1) ^ (-p))
    hxN (hf.abs.mul hpow) (by
      intro u hu
      have hmono := Real.rpow_le_rpow_of_nonpos ha hu.1 (neg_nonpos.mpr hp)
      exact (mul_le_mul_of_nonneg_right (hbound u hu)
        (Real.rpow_nonneg (ha.trans_le hu.1).le _)).trans
        (mul_le_mul_of_nonneg_left hmono hC)) (by
      intro u hu
      simp [hzero u hu])
  simpa only [mul_assoc] using hweighted

end MathlibAux
