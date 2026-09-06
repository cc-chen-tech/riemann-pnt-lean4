import HardyTheorem.SelbergS12RealCutoff
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open scoped BigOperators ArithmeticFunction ArithmeticFunction.zeta
  ArithmeticFunction.Moebius

namespace HardyTheorem

/-!
# The generalized Jordan weight in Selberg's arithmetic square

For positive integers, `selbergRpowArithmetic alpha n = n^alpha`.  Its
Möbius convolution is the generalized Jordan weight.  Möbius inversion gives
the exact divisor identity, while the local prime-power formula gives
positivity and the elementary upper bound used in the energy estimate.
-/

noncomputable def selbergRpowArithmetic (alpha : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (n : ℝ) ^ alpha, by simp⟩

@[simp] theorem selbergRpowArithmetic_apply_pos
    (alpha : ℝ) {n : ℕ} (hn : n ≠ 0) :
    selbergRpowArithmetic alpha n = (n : ℝ) ^ alpha := by
  simp [selbergRpowArithmetic, hn]

theorem selbergRpowArithmetic_isMultiplicative (alpha : ℝ) :
    (selbergRpowArithmetic alpha).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [selbergRpowArithmetic]
  · intro m n hm hn _
    rw [selbergRpowArithmetic_apply_pos alpha (Nat.mul_ne_zero hm hn),
      selbergRpowArithmetic_apply_pos alpha hm,
      selbergRpowArithmetic_apply_pos alpha hn, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

noncomputable def selbergJordanWeight (alpha : ℝ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
    selbergRpowArithmetic alpha

theorem selbergJordanWeight_isMultiplicative (alpha : ℝ) :
    (selbergJordanWeight alpha).IsMultiplicative := by
  exact ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    (selbergRpowArithmetic_isMultiplicative alpha)

/-- Exact generalized Jordan divisor identity. -/
theorem sum_divisors_selbergJordanWeight
    (alpha : ℝ) {q : ℕ} (hq : q ≠ 0) :
    (∑ r ∈ q.divisors, selbergJordanWeight alpha r) =
      (q : ℝ) ^ alpha := by
  have hconv :
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          selbergJordanWeight alpha = selbergRpowArithmetic alpha := by
    unfold selbergJordanWeight
    rw [← mul_assoc]
    have hzmu :
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            (ArithmeticFunction.moebius : ArithmeticFunction ℝ) = 1 := by
      simpa using congrArg
        (fun f : ArithmeticFunction ℤ => (f : ArithmeticFunction ℝ))
        ArithmeticFunction.coe_zeta_mul_moebius
    rw [hzmu, one_mul]
  calc
    (∑ r ∈ q.divisors, selbergJordanWeight alpha r) =
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          selbergJordanWeight alpha) q := by
      rw [ArithmeticFunction.coe_zeta_mul_apply]
    _ = selbergRpowArithmetic alpha q := by rw [hconv]
    _ = (q : ℝ) ^ alpha :=
      selbergRpowArithmetic_apply_pos alpha hq

theorem selbergJordanWeight_prime_pow_succ
    (alpha : ℝ) {p k : ℕ} (hp : p.Prime) :
    selbergJordanWeight alpha (p ^ (k + 1)) =
      ((p ^ (k + 1) : ℕ) : ℝ) ^ alpha -
        ((p ^ k : ℕ) : ℝ) ^ alpha := by
  have hsucc := sum_divisors_selbergJordanWeight alpha
    (pow_ne_zero (k + 1) hp.ne_zero)
  have hprev := sum_divisors_selbergJordanWeight alpha
    (pow_ne_zero k hp.ne_zero)
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ] at hsucc
  rw [Nat.sum_divisors_prime_pow hp] at hprev
  linarith

theorem selbergJordanWeight_nonneg
    {alpha : ℝ} (halpha : 0 ≤ alpha) (r : ℕ) :
    0 ≤ selbergJordanWeight alpha r := by
  by_cases hr : r = 0
  · simp [hr]
  rw [(selbergJordanWeight_isMultiplicative alpha).multiplicative_factorization
    (selbergJordanWeight alpha) hr]
  apply Finset.prod_nonneg
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hkne : r.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hkne
  rw [hk]
  change 0 ≤ selbergJordanWeight alpha (p ^ (k + 1))
  rw [selbergJordanWeight_prime_pow_succ alpha hpprime]
  apply sub_nonneg.mpr
  apply Real.rpow_le_rpow (by positivity) _ halpha
  exact_mod_cast Nat.pow_le_pow_right hpprime.pos (Nat.le_succ k)

theorem selbergJordanWeight_le_rpow
    {alpha : ℝ} (halpha : 0 ≤ alpha) {r : ℕ} (hr : r ≠ 0) :
    selbergJordanWeight alpha r ≤ (r : ℝ) ^ alpha := by
  calc
    selbergJordanWeight alpha r ≤
        ∑ d ∈ r.divisors, selbergJordanWeight alpha d := by
      apply Finset.single_le_sum
      · intro d hd
        exact selbergJordanWeight_nonneg halpha d
      · simp [hr]
    _ = (r : ℝ) ^ alpha := sum_divisors_selbergJordanWeight alpha hr

end HardyTheorem
