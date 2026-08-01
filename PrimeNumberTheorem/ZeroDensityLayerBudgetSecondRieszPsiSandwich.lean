import PrimeNumberTheorem.ZeroDensityLayerBudgetQuadraticHingeSecondDifference

open Real

namespace PrimeNumberTheorem

theorem sum_vonMangoldt_quadraticHinge_log_div_eq_secondRieszChebyshevPsi
    (x : ℝ) (hx : 0 < x) (N : ℕ) (hN : Nat.floor x < N) :
    (∑ n ∈ Finset.Ico 1 N,
      vonMangoldt n * quadraticHinge (Real.log (x / n))) =
      secondRieszChebyshevPsi x := by
  have hcut : Nat.floor x + 1 ≤ N := Nat.succ_le_iff.mpr hN
  rw [← Finset.sum_Ico_consecutive _ (Nat.succ_le_succ (Nat.zero_le _)) hcut]
  rw [secondRieszChebyshevPsi]
  have htail :
      (∑ n ∈ Finset.Ico (Nat.floor x + 1) N,
        vonMangoldt n * quadraticHinge (Real.log (x / n))) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rcases Finset.mem_Ico.mp hn with ⟨hn_lower, hn_upper⟩
    have hn_pos_nat : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ _) hn_lower
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
    have hxn : x < (n : ℝ) :=
      (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hn_lower)
    have hratio_nonneg : 0 ≤ x / (n : ℝ) := div_nonneg hx.le hn_pos.le
    have hratio_le : x / (n : ℝ) ≤ 1 := (div_le_one₀ hn_pos).2 hxn.le
    rw [quadraticHinge, max_eq_right (Real.log_nonpos hratio_nonneg hratio_le)]
    norm_num
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
  rw [quadraticHinge, max_eq_left (Real.log_nonneg hratio)]
  ring

lemma log_mul_exp_div_eq_log_div_add
    {x n h : ℝ} (hx : 0 < x) (hn : 0 < n) :
    Real.log ((x * Real.exp h) / n) = Real.log (x / n) + h := by
  rw [Real.log_div (mul_pos hx (Real.exp_pos h)).ne' hn.ne',
    Real.log_mul hx.ne' (Real.exp_ne_zero h), Real.log_exp,
    Real.log_div hx.ne' hn.ne']
  ring

lemma log_mul_exp_two_mul_div_eq_log_div_add_two_mul
    {x n h : ℝ} (hx : 0 < x) (hn : 0 < n) :
    Real.log ((x * Real.exp (2 * h)) / n) = Real.log (x / n) + 2 * h := by
  rw [Real.log_div (mul_pos hx (Real.exp_pos (2 * h))).ne' hn.ne',
    Real.log_mul hx.ne' (Real.exp_ne_zero (2 * h)), Real.log_exp,
    Real.log_div hx.ne' hn.ne']
  ring

/-- Two logarithmic forward differences of the actual von Mangoldt second
Riesz mean are sandwiched between Chebyshev psi at the two endpoints. -/
theorem chebyshevPsi_le_secondRieszSecondDifference_div_sq_le
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    let y := x * Real.exp h
    let z := x * Real.exp (2 * h)
    chebyshevPsi x ≤
        (secondRieszChebyshevPsi z - 2 * secondRieszChebyshevPsi y +
          secondRieszChebyshevPsi x) / h ^ 2 ∧
      (secondRieszChebyshevPsi z - 2 * secondRieszChebyshevPsi y +
          secondRieszChebyshevPsi x) / h ^ 2 ≤ chebyshevPsi z := by
  dsimp only
  let y : ℝ := x * Real.exp h
  let z : ℝ := x * Real.exp (2 * h)
  let Sx := Finset.Ico 1 (Nat.floor x + 1)
  let Sz := Finset.Ico 1 (Nat.floor z + 1)
  let q : ℕ → ℝ := fun n => Real.log (x / n)
  let f : ℕ → ℝ := fun n =>
    vonMangoldt n * quadraticHingeSecondDifferenceNumerator (q n) h
  have hy : 0 < y := mul_pos hx (Real.exp_pos h)
  have hz : 0 < z := mul_pos hx (Real.exp_pos (2 * h))
  have honeexp : 1 ≤ Real.exp h := (Real.one_lt_exp_iff.mpr hh).le
  have honeexp2 : 1 ≤ Real.exp (2 * h) :=
    (Real.one_lt_exp_iff.mpr (by linarith)).le
  have hxy : x ≤ y := by
    dsimp [y]
    nlinarith
  have hxz : x ≤ z := by
    dsimp [z]
    nlinarith
  have hyz : y ≤ z := by
    dsimp [y, z]
    have hexp_mul : Real.exp (2 * h) = Real.exp h * Real.exp h := by
      rw [show 2 * h = h + h by ring, Real.exp_add]
    rw [hexp_mul]
    nlinarith [Real.exp_pos h]
  have hfloor_xz : Nat.floor x ≤ Nat.floor z := Nat.floor_mono hxz
  have hfloor_yz : Nat.floor y ≤ Nat.floor z := Nat.floor_mono hyz
  have hxrepr := sum_vonMangoldt_quadraticHinge_log_div_eq_secondRieszChebyshevPsi
    x hx (Nat.floor z + 1) (lt_of_le_of_lt hfloor_xz (Nat.lt_succ_self _))
  have hyrepr := sum_vonMangoldt_quadraticHinge_log_div_eq_secondRieszChebyshevPsi
    y hy (Nat.floor z + 1) (lt_of_le_of_lt hfloor_yz (Nat.lt_succ_self _))
  have hzrepr := sum_vonMangoldt_quadraticHinge_log_div_eq_secondRieszChebyshevPsi
    z hz (Nat.floor z + 1) (Nat.lt_succ_self _)
  have hdiff :
      secondRieszChebyshevPsi z - 2 * secondRieszChebyshevPsi y +
          secondRieszChebyshevPsi x = ∑ n ∈ Sz, f n := by
    rw [← hzrepr, ← hyrepr, ← hxrepr]
    simp only [Sz]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hnS
    rcases Finset.mem_Ico.mp hnS with ⟨hn_one, hn_upper⟩
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_one)
    rw [log_mul_exp_two_mul_div_eq_log_div_add_two_mul hx hn_pos,
      log_mul_exp_div_eq_log_div_add hx hn_pos]
    dsimp [f, q, quadraticHingeSecondDifferenceNumerator]
    ring
  have hleft : chebyshevPsi x * h ^ 2 = ∑ n ∈ Sx, f n := by
    rw [chebyshevPsi, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hnS
    rcases Finset.mem_Ico.mp hnS with ⟨hn_one, hn_upper⟩
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_one)
    have hn_floor : n ≤ Nat.floor x := by omega
    have hn_x : (n : ℝ) ≤ x :=
      le_trans (by exact_mod_cast hn_floor) (Nat.floor_le hx.le)
    have hratio : 1 ≤ x / (n : ℝ) :=
      (le_div_iff₀ hn_pos).2 (by simpa using hn_x)
    dsimp [f, q]
    rw [quadraticHingeSecondDifferenceNumerator_eq_sq_of_nonneg
      (Real.log_nonneg hratio) hh.le]
  have hlower : chebyshevPsi x * h ^ 2 ≤
      secondRieszChebyshevPsi z - 2 * secondRieszChebyshevPsi y +
        secondRieszChebyshevPsi x := by
    rw [hleft, hdiff]
    have hcut : Nat.floor x + 1 ≤ Nat.floor z + 1 :=
      Nat.succ_le_succ hfloor_xz
    rw [show Sz = Finset.Ico 1 (Nat.floor z + 1) by rfl,
      ← Finset.sum_Ico_consecutive f (Nat.succ_le_succ (Nat.zero_le _)) hcut]
    apply le_add_of_nonneg_right
    apply Finset.sum_nonneg
    intro n hn
    dsimp [f]
    have hv_nonneg : 0 ≤ vonMangoldt n := by
      rw [vonMangoldt_eq_mathlib]
      exact ArithmeticFunction.vonMangoldt_nonneg
    exact mul_nonneg hv_nonneg
      (quadraticHingeSecondDifferenceNumerator_bounds (q := q n) hh).1
  have hupper :
      secondRieszChebyshevPsi z - 2 * secondRieszChebyshevPsi y +
          secondRieszChebyshevPsi x ≤ chebyshevPsi z * h ^ 2 := by
    rw [hdiff, chebyshevPsi, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro n hnS
    dsimp [Sz] at hnS
    have hv_nonneg : 0 ≤ vonMangoldt n := by
      rw [vonMangoldt_eq_mathlib]
      exact ArithmeticFunction.vonMangoldt_nonneg
    dsimp [f]
    exact mul_le_mul_of_nonneg_left
      (quadraticHingeSecondDifferenceNumerator_bounds (q := q n) hh).2 hv_nonneg
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  constructor
  · exact (le_div_iff₀ hh2).2 hlower
  · exact (div_le_iff₀ hh2).2 hupper

end PrimeNumberTheorem
