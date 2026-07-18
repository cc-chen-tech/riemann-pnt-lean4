import ZeroFreeRegion.VinogradovKorobov.IteratedDifference
import ZeroFreeRegion.VinogradovKorobov.LogSum

namespace ZeroFreeRegion.VinogradovKorobov

/-- The shifted logarithmic phase of a zeta Dirichlet block. -/
noncomputable def shiftedZetaPhase (t : ℝ) (m n : ℕ) : ℝ :=
  -t * Real.log (m + n)

/-- The positive second signed finite difference of the logarithm. -/
noncomputable def logSecondDifference (h k x : ℝ) : ℝ :=
  (Real.log (x + h) - Real.log x) -
    (Real.log (x + h + k) - Real.log (x + k))

/-- The decrease of the positive second logarithmic difference over one unit
step. -/
noncomputable def logSecondDifferenceDecrement (h k x : ℝ) : ℝ :=
  logSecondDifference h k x - logSecondDifference h k (x + 1)

/-- Rational quantity whose `log (1 + ·)` is the unit decrement of the
second logarithmic difference. -/
noncomputable def logSecondDifferenceDecrementFraction
    (h k x : ℝ) : ℝ :=
  h * k * (2 * x + h + k + 1) /
    (x * (x + h + k) *
      ((x + 1) * (x + h + k + 1) + h * k))

/-- Rational-logarithmic normal form of the second finite difference. -/
lemma logSecondDifference_eq
    {h k x : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k) :
    logSecondDifference h k x =
      Real.log (1 + h * k / (x * (x + h + k))) := by
  have hx0 : x ≠ 0 := hx.ne'
  have hxh0 : x + h ≠ 0 := by positivity
  have hxk0 : x + k ≠ 0 := by positivity
  have hxhk0 : x + h + k ≠ 0 := by positivity
  rw [logSecondDifference, ← Real.log_div hxh0 hx0,
    ← Real.log_div hxhk0 hxk0]
  rw [← Real.log_div (div_ne_zero hxh0 hx0) (div_ne_zero hxhk0 hxk0)]
  congr 1
  field_simp
  ring

lemma logSecondDifference_pos
    {h k x : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k) :
    0 < logSecondDifference h k x := by
  rw [logSecondDifference_eq hx hh hk]
  apply Real.log_pos
  have hden : 0 < x * (x + h + k) := by positivity
  exact lt_add_of_pos_right 1 (div_pos (mul_pos hh hk) hden)

lemma logSecondDifference_le_fraction
    {h k x : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k) :
    logSecondDifference h k x ≤ h * k / (x * (x + h + k)) := by
  rw [logSecondDifference_eq hx hh hk]
  have hden : 0 < x * (x + h + k) := by positivity
  have harg : 0 < 1 + h * k / (x * (x + h + k)) := by positivity
  have hlog := Real.log_le_sub_one_of_pos harg
  linarith

lemma fraction_le_logSecondDifference
    {h k x : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k) :
    h * k / (x * (x + h + k) + h * k) ≤
      logSecondDifference h k x := by
  rw [logSecondDifference_eq hx hh hk]
  have hden : 0 < x * (x + h + k) := by positivity
  have harg : 0 < 1 + h * k / (x * (x + h + k)) := by positivity
  calc
    h * k / (x * (x + h + k) + h * k) =
        1 - (1 + h * k / (x * (x + h + k)))⁻¹ := by
      field_simp
      ring
    _ ≤ Real.log (1 + h * k / (x * (x + h + k))) :=
      Real.one_sub_inv_le_log_of_pos harg

/-- The second logarithmic difference decreases as the base point moves to
the right. -/
lemma antitoneOn_logSecondDifference
    {h k : ℝ} (hh : 0 < h) (hk : 0 < k) :
    AntitoneOn (logSecondDifference h k) (Set.Ioi 0) := by
  intro x hx y hy hxy
  rw [logSecondDifference_eq hy hh hk, logSecondDifference_eq hx hh hk]
  have hxpos : 0 < x := hx
  have hypos : 0 < y := hy
  have hdx : 0 < x * (x + h + k) := by positivity
  have hdy : 0 < y * (y + h + k) := by positivity
  have hden : x * (x + h + k) ≤ y * (y + h + k) := by
    exact mul_le_mul hxy (by linarith) (by positivity) (by positivity)
  have hnum : 0 ≤ h * k := (mul_pos hh hk).le
  have hfrac :
      h * k / (y * (y + h + k)) ≤
        h * k / (x * (x + h + k)) := by
    exact (div_le_div_iff₀ hdy hdx).2
      (mul_le_mul_of_nonneg_left hden hnum)
  exact Real.strictMonoOn_log.monotoneOn
    (by exact add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hnum hdy.le))
    (by exact add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hnum hdx.le))
    (add_le_add_right hfrac 1)

/-- Exact logarithmic normal form of the third finite-difference magnitude. -/
lemma logSecondDifferenceDecrement_eq
    {h k x : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k) :
    logSecondDifferenceDecrement h k x =
      Real.log (1 + logSecondDifferenceDecrementFraction h k x) := by
  have hx1 : 0 < x + 1 := by positivity
  rw [logSecondDifferenceDecrement,
    logSecondDifference_eq hx hh hk,
    logSecondDifference_eq hx1 hh hk]
  have hden0 : 0 < x * (x + h + k) := by positivity
  have hden1 : 0 < (x + 1) * (x + 1 + h + k) := by positivity
  have harg0 : 0 < 1 + h * k / (x * (x + h + k)) := by positivity
  have harg1 : 0 < 1 + h * k / ((x + 1) * (x + 1 + h + k)) := by
    positivity
  rw [← Real.log_div harg0.ne' harg1.ne']
  congr 1
  unfold logSecondDifferenceDecrementFraction
  field_simp
  ring

lemma logSecondDifferenceDecrement_pos
    {h k x : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k) :
    0 < logSecondDifferenceDecrement h k x := by
  rw [logSecondDifferenceDecrement_eq hx hh hk]
  apply Real.log_pos
  unfold logSecondDifferenceDecrementFraction
  have hden :
      0 < x * (x + h + k) *
        ((x + 1) * (x + h + k + 1) + h * k) := by positivity
  exact lt_add_of_pos_right 1
    (div_pos (mul_pos (mul_pos hh hk) (by positivity)) hden)

lemma logSecondDifferenceDecrement_le_fraction
    {h k x : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k) :
    logSecondDifferenceDecrement h k x ≤
      logSecondDifferenceDecrementFraction h k x := by
  rw [logSecondDifferenceDecrement_eq hx hh hk]
  have hfrac : 0 < logSecondDifferenceDecrementFraction h k x := by
    unfold logSecondDifferenceDecrementFraction
    positivity
  have hlog := Real.log_le_sub_one_of_pos (show
    0 < 1 + logSecondDifferenceDecrementFraction h k x by positivity)
  linarith

private lemma logSecondDifferenceDecrementFraction_factor
    {h k x : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k) :
    logSecondDifferenceDecrementFraction h k x =
      (h * k) * ((2 * x + h + k + 1) / x) *
        (x + h + k)⁻¹ *
        ((x + 1) * (x + h + k + 1) + h * k)⁻¹ := by
  unfold logSecondDifferenceDecrementFraction
  field_simp

/-- The third finite-difference magnitude decreases with the base point. -/
lemma antitoneOn_logSecondDifferenceDecrement
    {h k : ℝ} (hh : 0 < h) (hk : 0 < k) :
    AntitoneOn (logSecondDifferenceDecrement h k) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := hx
  have hypos : 0 < y := hy
  have hfracY : 0 < logSecondDifferenceDecrementFraction h k y := by
    unfold logSecondDifferenceDecrementFraction
    positivity
  have hfracX : 0 < logSecondDifferenceDecrementFraction h k x := by
    unfold logSecondDifferenceDecrementFraction
    positivity
  rw [logSecondDifferenceDecrement_eq hypos hh hk,
    logSecondDifferenceDecrement_eq hxpos hh hk]
  apply Real.strictMonoOn_log.monotoneOn
  · exact add_pos_of_pos_of_nonneg zero_lt_one hfracY.le
  · exact add_pos_of_pos_of_nonneg zero_lt_one hfracX.le
  · apply add_le_add_right
    rw [logSecondDifferenceDecrementFraction_factor hypos hh hk,
      logSecondDifferenceDecrementFraction_factor hxpos hh hk]
    have hratio :
        (2 * y + h + k + 1) / y ≤
          (2 * x + h + k + 1) / x := by
      apply (div_le_div_iff₀ hypos hxpos).2
      nlinarith
    have hlinear : x + h + k ≤ y + h + k := by linarith
    have hinvLinear :
        (y + h + k)⁻¹ ≤ (x + h + k)⁻¹ := by
      exact (inv_le_inv₀ (by positivity) (by positivity)).2 hlinear
    have hquad :
        (x + 1) * (x + h + k + 1) + h * k ≤
          (y + 1) * (y + h + k + 1) + h * k := by
      have hleft : x + 1 ≤ y + 1 := by linarith
      have hright : x + h + k + 1 ≤ y + h + k + 1 := by linarith
      have hprod :
          (x + 1) * (x + h + k + 1) ≤
            (y + 1) * (y + h + k + 1) := by
        exact mul_le_mul hleft hright (by positivity) (by positivity)
      simpa [add_comm] using add_le_add_right hprod (h * k)
    have hinvQuad :
        ((y + 1) * (y + h + k + 1) + h * k)⁻¹ ≤
          ((x + 1) * (x + h + k + 1) + h * k)⁻¹ := by
      exact (inv_le_inv₀ (by positivity) (by positivity)).2 hquad
    gcongr

/-- Two A-process differences of the shifted zeta phase are exactly `t`
times the positive second logarithmic difference. -/
lemma iterated_shiftedZetaPhase_two
    (t : ℝ) (m n h k : ℕ) :
    iteratedPhaseDifference [h, k] (shiftedZetaPhase t m) n =
      t * logSecondDifference h k (m + n) := by
  simp only [iteratedPhaseDifference_cons, iteratedPhaseDifference_nil]
  unfold phaseDifference shiftedZetaPhase logSecondDifference
  push_cast
  ring_nf

/-- The shifted phase notation agrees with the zeta oscillation used by the
Dirichlet-block modules. -/
lemma phaseTerm_shiftedZetaPhase (t : ℝ) (m n : ℕ) :
    phaseTerm (shiftedZetaPhase t m) n = zetaOscillation t (m + n) := by
  unfold shiftedZetaPhase zetaOscillation phaseTerm
  congr 1
  push_cast
  rfl

end ZeroFreeRegion.VinogradovKorobov
