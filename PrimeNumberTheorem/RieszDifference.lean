import PrimeNumberTheorem.Perron

/-!
# Recovering Chebyshev psi from the first Riesz mean

This module proves the finite-difference inequalities connecting the first
von Mangoldt Riesz mean supplied by second-order Perron inversion back to
`chebyshevPsi`.
-/

open Real

namespace PrimeNumberTheorem

theorem max_log_div_sub_max_log_div_bounds
    {x y n : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hn : 0 < n) :
    0 ≤ max (Real.log (y / n)) 0 - max (Real.log (x / n)) 0 ∧
      max (Real.log (y / n)) 0 - max (Real.log (x / n)) 0 ≤ Real.log (y / x) := by
  have hy : 0 < y := hx.trans_le hxy
  have hxn : 0 < x / n := div_pos hx hn
  have hdiv : x / n ≤ y / n := div_le_div_of_nonneg_right hxy hn.le
  have hlog : Real.log (x / n) ≤ Real.log (y / n) := Real.log_le_log hxn hdiv
  have hratio : 1 ≤ y / x := (le_div_iff₀ hx).2 (by simpa using hxy)
  have hlogratio : 0 ≤ Real.log (y / x) := Real.log_nonneg hratio
  have hlog_sub : Real.log (y / n) - Real.log (x / n) = Real.log (y / x) := by
    rw [Real.log_div hy.ne' hn.ne', Real.log_div hx.ne' hn.ne',
      Real.log_div hy.ne' hx.ne']
    ring
  constructor
  · exact sub_nonneg.mpr (max_le_max hlog le_rfl)
  · calc
      max (Real.log (y / n)) 0 - max (Real.log (x / n)) 0 ≤
          |max (Real.log (y / n)) 0 - max (Real.log (x / n)) 0| := le_abs_self _
      _ ≤ |Real.log (y / n) - Real.log (x / n)| :=
        abs_max_sub_max_le_abs _ _ _
      _ = Real.log (y / x) := by rw [hlog_sub, abs_of_nonneg hlogratio]

theorem max_log_div_sub_max_log_div_eq
    {x y n : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hn : 0 < n) (hnx : n ≤ x) :
    max (Real.log (y / n)) 0 - max (Real.log (x / n)) 0 = Real.log (y / x) := by
  have hy : 0 < y := hx.trans_le hxy
  have hnx_one : 1 ≤ x / n := (le_div_iff₀ hn).2 (by simpa using hnx)
  have hny_one : 1 ≤ y / n := (le_div_iff₀ hn).2 (by simpa using hnx.trans hxy)
  rw [max_eq_left (Real.log_nonneg hny_one), max_eq_left (Real.log_nonneg hnx_one),
    Real.log_div hy.ne' hn.ne', Real.log_div hx.ne' hn.ne',
    Real.log_div hy.ne' hx.ne']
  ring

theorem sum_vonMangoldt_max_log_div_eq_smoothedChebyshevPsi
    (x : ℝ) (hx : 0 < x) (N : ℕ) (hN : Nat.floor x < N) :
    (∑ n ∈ Finset.Ico 1 N,
      vonMangoldt n * max (Real.log (x / n)) 0) = smoothedChebyshevPsi x := by
  have hcut : Nat.floor x + 1 ≤ N := Nat.succ_le_iff.mpr hN
  rw [← Finset.sum_Ico_consecutive _ (Nat.succ_le_succ (Nat.zero_le _)) hcut]
  rw [smoothedChebyshevPsi]
  have htail :
      (∑ n ∈ Finset.Ico (Nat.floor x + 1) N,
        vonMangoldt n * max (Real.log (x / n)) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rcases Finset.mem_Ico.mp hn with ⟨hn_lower, hn_upper⟩
    have hn_pos_nat : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ _) hn_lower
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
    have hxn : x < (n : ℝ) := by
      exact (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hn_lower)
    have hratio_nonneg : 0 ≤ x / (n : ℝ) := div_nonneg hx.le hn_pos.le
    have hratio_le : x / (n : ℝ) ≤ 1 := (div_le_one₀ hn_pos).2 hxn.le
    rw [max_eq_right (Real.log_nonpos hratio_nonneg hratio_le), mul_zero]
  rw [htail, add_zero]
  apply Finset.sum_congr rfl
  intro n hn
  rcases Finset.mem_Ico.mp hn with ⟨hn_one, hn_upper⟩
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_one)
  have hn_floor : n ≤ Nat.floor x := by omega
  have hn_x : (n : ℝ) ≤ x :=
    le_trans (by exact_mod_cast hn_floor) (Nat.floor_le hx.le)
  have hratio : 1 ≤ x / (n : ℝ) :=
    (le_div_iff₀ hn_pos).2 (by simpa using hn_x)
  rw [max_eq_left (Real.log_nonneg hratio)]

theorem smoothedChebyshevPsi_sub_le_chebyshevPsi_mul_log_div
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    smoothedChebyshevPsi y - smoothedChebyshevPsi x ≤
      chebyshevPsi y * Real.log (y / x) := by
  have hy : 0 < y := hx.trans_le hxy
  have hfloor : Nat.floor x ≤ Nat.floor y := Nat.floor_mono hxy
  have hxrepr := sum_vonMangoldt_max_log_div_eq_smoothedChebyshevPsi
    x hx (Nat.floor y + 1) (lt_of_le_of_lt hfloor (Nat.lt_succ_self _))
  have hyrepr := sum_vonMangoldt_max_log_div_eq_smoothedChebyshevPsi
    y hy (Nat.floor y + 1) (Nat.lt_succ_self _)
  rw [← hyrepr, ← hxrepr, chebyshevPsi, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro n hn
  rcases Finset.mem_Ico.mp hn with ⟨hn_one, hn_upper⟩
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_one)
  have hv_nonneg : 0 ≤ vonMangoldt n := by
    rw [vonMangoldt_eq_mathlib]
    exact ArithmeticFunction.vonMangoldt_nonneg
  have hbound := (max_log_div_sub_max_log_div_bounds hx hxy hn_pos).2
  calc
    vonMangoldt n * max (Real.log (y / n)) 0 -
        vonMangoldt n * max (Real.log (x / n)) 0 =
      vonMangoldt n *
        (max (Real.log (y / n)) 0 - max (Real.log (x / n)) 0) := by ring
    _ ≤ vonMangoldt n * Real.log (y / x) :=
      mul_le_mul_of_nonneg_left hbound hv_nonneg

theorem chebyshevPsi_mul_log_div_le_smoothedChebyshevPsi_sub
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    chebyshevPsi x * Real.log (y / x) ≤
      smoothedChebyshevPsi y - smoothedChebyshevPsi x := by
  have hy : 0 < y := hx.trans_le hxy
  have hfloor : Nat.floor x ≤ Nat.floor y := Nat.floor_mono hxy
  have hcut : Nat.floor x + 1 ≤ Nat.floor y + 1 := Nat.succ_le_succ hfloor
  have hxrepr := sum_vonMangoldt_max_log_div_eq_smoothedChebyshevPsi
    x hx (Nat.floor y + 1) (lt_of_le_of_lt hfloor (Nat.lt_succ_self _))
  have hyrepr := sum_vonMangoldt_max_log_div_eq_smoothedChebyshevPsi
    y hy (Nat.floor y + 1) (Nat.lt_succ_self _)
  let f : ℕ → ℝ := fun n => vonMangoldt n *
    (max (Real.log (y / n)) 0 - max (Real.log (x / n)) 0)
  have hdiff : smoothedChebyshevPsi y - smoothedChebyshevPsi x =
      ∑ n ∈ Finset.Ico 1 (Nat.floor y + 1), f n := by
    calc
      smoothedChebyshevPsi y - smoothedChebyshevPsi x =
          (∑ n ∈ Finset.Ico 1 (Nat.floor y + 1),
              vonMangoldt n * max (Real.log (y / n)) 0) -
            (∑ n ∈ Finset.Ico 1 (Nat.floor y + 1),
              vonMangoldt n * max (Real.log (x / n)) 0) := by rw [hyrepr, hxrepr]
      _ = ∑ n ∈ Finset.Ico 1 (Nat.floor y + 1),
          (vonMangoldt n * max (Real.log (y / n)) 0 -
            vonMangoldt n * max (Real.log (x / n)) 0) :=
        (Finset.sum_sub_distrib
          (s := Finset.Ico 1 (Nat.floor y + 1))
          (fun n => vonMangoldt n * max (Real.log (y / n)) 0)
          (fun n => vonMangoldt n * max (Real.log (x / n)) 0)).symm
      _ = ∑ n ∈ Finset.Ico 1 (Nat.floor y + 1), f n := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [f]
        ring
  have hpsi : chebyshevPsi x * Real.log (y / x) =
      ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1), f n := by
    rw [chebyshevPsi, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rcases Finset.mem_Ico.mp hn with ⟨hn_one, hn_upper⟩
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_one)
    have hn_floor : n ≤ Nat.floor x := by omega
    have hn_x : (n : ℝ) ≤ x :=
      le_trans (by exact_mod_cast hn_floor) (Nat.floor_le hx.le)
    simp only [f]
    rw [max_log_div_sub_max_log_div_eq hx hxy hn_pos hn_x]
  rw [hpsi, hdiff, ← Finset.sum_Ico_consecutive _
    (Nat.succ_le_succ (Nat.zero_le _)) hcut]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro n hn
  rcases Finset.mem_Ico.mp hn with ⟨hn_lower, hn_upper⟩
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ _) hn_lower
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hv_nonneg : 0 ≤ vonMangoldt n := by
    rw [vonMangoldt_eq_mathlib]
    exact ArithmeticFunction.vonMangoldt_nonneg
  exact mul_nonneg hv_nonneg (max_log_div_sub_max_log_div_bounds hx hxy hn_pos).1

/-- Finite differences of the first Riesz mean recover `ψ` between the two endpoints. -/
theorem chebyshevPsi_le_rieszDifference_div_log_le
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    chebyshevPsi x ≤
        (smoothedChebyshevPsi y - smoothedChebyshevPsi x) / Real.log (y / x) ∧
      (smoothedChebyshevPsi y - smoothedChebyshevPsi x) / Real.log (y / x) ≤
        chebyshevPsi y := by
  have hxy_le : x ≤ y := hxy.le
  have hratio : 1 < y / x := (lt_div_iff₀ hx).2 (by simpa using hxy)
  have hlog : 0 < Real.log (y / x) := Real.log_pos hratio
  constructor
  · exact (le_div_iff₀ hlog).2
      (chebyshevPsi_mul_log_div_le_smoothedChebyshevPsi_sub hx hxy_le)
  · exact (div_le_iff₀ hlog).2
      (smoothedChebyshevPsi_sub_le_chebyshevPsi_mul_log_div hx hxy_le)

end PrimeNumberTheorem
