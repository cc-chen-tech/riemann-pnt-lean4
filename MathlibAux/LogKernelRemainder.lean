import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

open Real

namespace MathlibAux

/-- The logarithmic kernel differs by a bounded amount from its symmetric
first-order approximation on the central third.  This is the scalar remainder
estimate used to pass from integer Hilbert kernels to logarithmic frequencies. -/
theorem abs_inv_log_ratio_sub_inv_two_mul_le_one
    {x : ℝ} (hx : 0 < x) (hxthird : x ≤ 1 / 3) :
    |1 / Real.log ((1 + x) / (1 - x)) - 1 / (2 * x)| ≤ 1 := by
  have hxlt : x < 1 := lt_of_le_of_lt hxthird (by norm_num)
  have hxabs : |x| < 1 := by simpa [abs_of_pos hx] using hxlt
  let L : ℝ := 1 / 2 * Real.log ((1 + x) / (1 - x))
  have happrox : |L - x| ≤ x ^ 3 / (1 - x ^ 2) := by
    have h := Real.sum_range_sub_log_div_le hxabs 1
    norm_num [L, abs_of_pos hx] at h ⊢
    simpa using h
  have hlower : x ≤ L := by
    have h := Real.sum_range_le_log_div hx.le hxlt 1
    norm_num [L] at h ⊢
    simpa using h
  have hL : 0 < L := lt_of_lt_of_le hx hlower
  have hx2 : 0 < 2 * x * x := by positivity
  have hLx : 0 < 2 * L * x := by positivity
  have hdenmono : 2 * x * x ≤ 2 * L * x := by
    nlinarith
  have hdenrem : 0 < 1 - x ^ 2 := by nlinarith [sq_nonneg x]
  have hlog : Real.log ((1 + x) / (1 - x)) = 2 * L := by
    dsimp only [L]
    ring
  have hlogpos : 0 < Real.log ((1 + x) / (1 - x)) := by
    rw [hlog]
    positivity
  have hid :
      1 / Real.log ((1 + x) / (1 - x)) - 1 / (2 * x) =
        (x - L) / (2 * L * x) := by
    rw [hlog]
    field_simp [hL.ne', hx.ne']
  rw [hid, abs_div, abs_of_pos hLx, abs_sub_comm]
  calc
    |L - x| / (2 * L * x) ≤ |L - x| / (2 * x * x) := by
      rw [div_le_div_iff₀ hLx hx2]
      nlinarith [abs_nonneg (L - x)]
    _ ≤ (x ^ 3 / (1 - x ^ 2)) / (2 * x * x) := by
      exact div_le_div_of_nonneg_right happrox hx2.le
    _ ≤ 1 := by
      rw [div_div]
      rw [div_le_iff₀ (mul_pos hdenrem hx2)]
      have hsimple : x ≤ 2 * (1 - x ^ 2) := by
        nlinarith [sq_nonneg x]
      calc
        x ^ 3 = x * x ^ 2 := by ring
        _ ≤ (2 * (1 - x ^ 2)) * x ^ 2 :=
          mul_le_mul_of_nonneg_right hsimple (sq_nonneg x)
        _ = 1 * ((1 - x ^ 2) * (2 * x * x)) := by ring

/-- Symmetric two-variable form of the bounded logarithmic-kernel remainder.
Both variables are positive and lie within a factor two of one another. -/
theorem abs_inv_log_sub_sub_symmetric_le_one
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (ha2 : a ≤ 2 * b) (hb2 : b ≤ 2 * a) :
    |1 / (Real.log a - Real.log b) -
        (a + b) / (2 * (a - b))| ≤ 1 := by
  have hordered : ∀ {u v : ℝ}, 0 < u → 0 < v → v < u → u ≤ 2 * v →
      |1 / (Real.log u - Real.log v) -
          (u + v) / (2 * (u - v))| ≤ 1 := by
    intro u v hu hv hvu hu2
    let x : ℝ := (u - v) / (u + v)
    have hsum : 0 < u + v := by positivity
    have hx : 0 < x := div_pos (sub_pos.2 hvu) hsum
    have hxthird : x ≤ 1 / 3 := by
      dsimp only [x]
      rw [div_le_iff₀ hsum]
      nlinarith
    have hkernel :=
      abs_inv_log_ratio_sub_inv_two_mul_le_one hx hxthird
    have hratio : (1 + x) / (1 - x) = u / v := by
      dsimp only [x]
      field_simp [hsum.ne', hv.ne']
      ring
    have hmain : 1 / (2 * x) = (u + v) / (2 * (u - v)) := by
      dsimp only [x]
      field_simp [hsum.ne', sub_ne_zero.mpr hvu.ne']
    rw [hratio, Real.log_div hu.ne' hv.ne', hmain] at hkernel
    exact hkernel
  by_cases hba : b < a
  · exact hordered ha hb hba ha2
  · have hablt : a < b := lt_of_le_of_ne (le_of_not_gt hba) hab
    have hswap := hordered hb ha hablt hb2
    have hloglt : Real.log a < Real.log b :=
      Real.strictMonoOn_log ha hb hablt
    have hlogne : Real.log a - Real.log b ≠ 0 :=
      sub_ne_zero.mpr hloglt.ne
    have hlogne' : Real.log b - Real.log a ≠ 0 :=
      sub_ne_zero.mpr hloglt.ne.symm
    have hsubne : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hsubne' : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    have hneg :
        1 / (Real.log b - Real.log a) -
            (b + a) / (2 * (b - a)) =
          -(1 / (Real.log a - Real.log b) -
            (a + b) / (2 * (a - b))) := by
      field_simp [hlogne, hlogne', hsubne, hsubne']
      ring
    rw [hneg, abs_neg] at hswap
    exact hswap

/-- The symmetric logarithmic-kernel remainder is globally bounded.  The
factor-two hypothesis in `abs_inv_log_sub_sub_symmetric_le_one` is useful for
the sharp dyadic estimate, while this coarser bound also covers indices in
widely separated dyadic blocks. -/
theorem abs_inv_log_sub_sub_symmetric_le_four
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    |1 / (Real.log a - Real.log b) -
        (a + b) / (2 * (a - b))| ≤ 4 := by
  have hordered : ∀ {u v : ℝ}, 0 < u → 0 < v → v < u →
      |1 / (Real.log u - Real.log v) -
          (u + v) / (2 * (u - v))| ≤ 4 := by
    intro u v hu hv hvu
    by_cases hnear : u ≤ 2 * v
    · exact (abs_inv_log_sub_sub_symmetric_le_one hu hv hvu.ne'
        hnear (by nlinarith)).trans (by norm_num)
    · have hfar : 2 * v < u := lt_of_not_ge hnear
      have hratio : 2 < u / v := (lt_div_iff₀ hv).2 hfar
      have hlogmono : Real.log 2 < Real.log (u / v) :=
        Real.strictMonoOn_log (by norm_num) (div_pos hu hv) hratio
      have hlogeq : Real.log (u / v) = Real.log u - Real.log v := by
        rw [Real.log_div hu.ne' hv.ne']
      have hloghalf : (1 / 2 : ℝ) < Real.log 2 := by
        exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
          Real.log_two_gt_d9
      have hlogpos : 0 < Real.log u - Real.log v := by
        exact sub_pos.mpr (Real.strictMonoOn_log hv hu hvu)
      have hinv : 1 / (Real.log u - Real.log v) ≤ 2 := by
        have hhalfDiff : (1 / 2 : ℝ) < Real.log u - Real.log v := by
          rw [← hlogeq]
          exact hloghalf.trans hlogmono
        rw [div_le_iff₀ hlogpos]
        nlinarith
      have hdenpos : 0 < 2 * (u - v) := by nlinarith
      have hfrac : (u + v) / (2 * (u - v)) ≤ 3 / 2 := by
        rw [div_le_iff₀ hdenpos]
        nlinarith
      calc
        |1 / (Real.log u - Real.log v) -
            (u + v) / (2 * (u - v))| ≤
            |1 / (Real.log u - Real.log v)| +
              |(u + v) / (2 * (u - v))| := abs_sub _ _
        _ = 1 / (Real.log u - Real.log v) +
              (u + v) / (2 * (u - v)) := by
            rw [abs_of_pos (one_div_pos.mpr hlogpos),
              abs_of_pos (div_pos (by positivity) hdenpos)]
        _ ≤ 4 := by nlinarith
  by_cases hba : b < a
  · exact hordered ha hb hba
  · have hablt : a < b := lt_of_le_of_ne (le_of_not_gt hba) hab
    have hswap := hordered hb ha hablt
    have hloglt : Real.log a < Real.log b :=
      Real.strictMonoOn_log ha hb hablt
    have hlogne : Real.log a - Real.log b ≠ 0 :=
      sub_ne_zero.mpr hloglt.ne
    have hlogne' : Real.log b - Real.log a ≠ 0 :=
      sub_ne_zero.mpr hloglt.ne.symm
    have hsubne : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hsubne' : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    have hneg :
        1 / (Real.log b - Real.log a) -
            (b + a) / (2 * (b - a)) =
          -(1 / (Real.log a - Real.log b) -
            (a + b) / (2 * (a - b))) := by
      field_simp [hlogne, hlogne', hsubne, hsubne']
      ring
    rw [hneg, abs_neg] at hswap
    exact hswap

end MathlibAux
