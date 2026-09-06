import HardyTheorem.SelbergS13AbsoluteBound

open scoped BigOperators

namespace HardyTheorem

/-!
# Selberg S-arith: the finite Euler weight

The fourth power of the Euler factor inherited from two applications of S12
and one application of S13 is dominated by a divisor-expandable factor with
the concrete coefficient `9`.
-/

theorem selbergSArith_local_fourth_le_nine {p : ℕ} (hp : p.Prime) :
    (1 + (p : ℝ)⁻¹) ^ 4 ≤ 1 + 9 * (p : ℝ)⁻¹ := by
  let x : ℝ := (p : ℝ)⁻¹
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxhalf : x ≤ 1 / 2 := by
    dsimp [x]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2)
  have hx2 : x ^ 2 ≤ x / 2 := by
    calc
      x ^ 2 = x * x := by ring
      _ ≤ x * (1 / 2) := mul_le_mul_of_nonneg_left hxhalf hx
      _ = x / 2 := by ring
  have hx3 : x ^ 3 ≤ x / 4 := by
    calc
      x ^ 3 = x ^ 2 * x := by ring
      _ ≤ (x / 2) * x := mul_le_mul_of_nonneg_right hx2 hx
      _ ≤ (x / 2) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hxhalf (by positivity)
      _ = x / 4 := by ring
  have hx4 : x ^ 4 ≤ x / 8 := by
    calc
      x ^ 4 = x ^ 3 * x := by ring
      _ ≤ (x / 4) * x := mul_le_mul_of_nonneg_right hx3 hx
      _ ≤ (x / 4) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hxhalf (by positivity)
      _ = x / 8 := by ring
  change (1 + x) ^ 4 ≤ 1 + 9 * x
  ring_nf
  nlinarith

noncomputable def selbergSArithEulerWeight (r : ℕ) : ℝ :=
  (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) ^ 4

theorem selbergSArithEulerWeight_nonneg (r : ℕ) :
    0 ≤ selbergSArithEulerWeight r := by
  unfold selbergSArithEulerWeight
  positivity

/-- Concrete finite-product majorant used before Möbius inversion of the
Euler weight. -/
theorem selbergSArithEulerWeight_le_nineProduct (r : ℕ) :
    selbergSArithEulerWeight r ≤
      ∏ p ∈ r.primeFactors, (1 + 9 * (p : ℝ)⁻¹) := by
  unfold selbergSArithEulerWeight
  rw [← Finset.prod_pow]
  exact Finset.prod_le_prod
    (fun _ _ => by positivity)
    (fun p hp => selbergSArith_local_fourth_le_nine
      (Nat.prime_of_mem_primeFactors hp))

end HardyTheorem
