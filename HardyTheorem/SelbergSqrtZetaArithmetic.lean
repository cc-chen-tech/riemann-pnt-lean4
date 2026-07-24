import HardyTheorem.SelbergSqrtZetaLocal
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# The arithmetic coefficients of `ζ⁻¹ᐟ²`

The local coefficients from `SelbergSqrtZetaLocal` are multiplied over the
prime-power factorization of an integer.  The resulting arithmetic function
is multiplicative, and its Dirichlet-convolution square is the Möbius
function.  This is the coefficient identity required by Selberg's mollifier.
-/

/-- The multiplicative arithmetic function whose value at every prime power
`p^k` is the coefficient of `X^k` in `(1 - X)^(1/2)`. -/
noncomputable def selbergSqrtZetaCoeff : ArithmeticFunction ℝ :=
  ⟨fun n =>
      if n = 0 then 0
      else n.factorization.prod fun _ k => selbergSqrtZetaLocalCoeff k,
    by simp⟩

@[simp] theorem selbergSqrtZetaCoeff_zero :
    selbergSqrtZetaCoeff 0 = 0 := by
  simp [selbergSqrtZetaCoeff]

@[simp] theorem selbergSqrtZetaCoeff_one :
    selbergSqrtZetaCoeff 1 = 1 := by
  simp [selbergSqrtZetaCoeff]

theorem selbergSqrtZetaCoeff_apply_ne_zero
    {n : ℕ} (hn : n ≠ 0) :
    selbergSqrtZetaCoeff n =
      n.factorization.prod fun _ k => selbergSqrtZetaLocalCoeff k := by
  simp [selbergSqrtZetaCoeff, hn]

theorem selbergSqrtZetaCoeff_apply_prime_pow
    {p k : ℕ} (hp : p.Prime) :
    selbergSqrtZetaCoeff (p ^ k) = selbergSqrtZetaLocalCoeff k := by
  rw [selbergSqrtZetaCoeff_apply_ne_zero (pow_ne_zero k hp.ne_zero)]
  rw [hp.factorization_pow]
  exact Finsupp.prod_single_index selbergSqrtZetaLocalCoeff_zero

/-- The square-root zeta coefficient function is multiplicative. -/
theorem selbergSqrtZetaCoeff_isMultiplicative :
    ArithmeticFunction.IsMultiplicative selbergSqrtZetaCoeff := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨selbergSqrtZetaCoeff_one, ?_⟩
  intro m n hm hn hcop
  rw [selbergSqrtZetaCoeff_apply_ne_zero (mul_ne_zero hm hn),
    selbergSqrtZetaCoeff_apply_ne_zero hm,
    selbergSqrtZetaCoeff_apply_ne_zero hn,
    Nat.factorization_mul_of_coprime hcop,
    Finsupp.prod_add_index_of_disjoint hcop.disjoint_primeFactors]

/-- On a prime power, the convolution square is the local coefficient
convolution. -/
theorem selbergSqrtZetaCoeff_sq_apply_prime_pow
    {p k : ℕ} (hp : p.Prime) :
    (selbergSqrtZetaCoeff * selbergSqrtZetaCoeff) (p ^ k) =
      if k = 0 then 1 else if k = 1 then -1 else 0 := by
  rw [ArithmeticFunction.mul_apply]
  change
    (∑ x ∈ (p ^ k).divisorsAntidiagonal,
      (fun i j => selbergSqrtZetaCoeff i * selbergSqrtZetaCoeff j)
        x.1 x.2) =
      if k = 0 then 1 else if k = 1 then -1 else 0
  rw [Nat.sum_divisorsAntidiagonal
      (fun i j => selbergSqrtZetaCoeff i * selbergSqrtZetaCoeff j),
    Nat.sum_divisors_prime_pow hp]
  calc
    (∑ i ∈ Finset.range (k + 1),
        selbergSqrtZetaCoeff (p ^ i) *
          selbergSqrtZetaCoeff (p ^ k / p ^ i)) =
        ∑ i ∈ Finset.range (k + 1),
          selbergSqrtZetaLocalCoeff i *
            selbergSqrtZetaLocalCoeff (k - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := by
        simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hi
      rw [selbergSqrtZetaCoeff_apply_prime_pow hp,
        Nat.pow_div hik hp.pos,
        selbergSqrtZetaCoeff_apply_prime_pow hp]
    _ = if k = 0 then 1 else if k = 1 then -1 else 0 := by
      have hlocal :=
        sum_antidiagonal_selbergSqrtZetaLocalCoeff_mul k
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j =>
          selbergSqrtZetaLocalCoeff i *
            selbergSqrtZetaLocalCoeff j) k] at hlocal
      simpa [Nat.succ_eq_add_one] using hlocal

/-- Globally, the Dirichlet-convolution square of the square-root
coefficients is the Möbius function. -/
theorem selbergSqrtZetaCoeff_mul_self :
    selbergSqrtZetaCoeff * selbergSqrtZetaCoeff =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    (selbergSqrtZetaCoeff * selbergSqrtZetaCoeff)
    (selbergSqrtZetaCoeff_isMultiplicative.mul
      selbergSqrtZetaCoeff_isMultiplicative)
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
    ArithmeticFunction.isMultiplicative_moebius.intCast).2
  intro p k hp
  rw [selbergSqrtZetaCoeff_sq_apply_prime_pow hp]
  by_cases hk : k = 0
  · subst k
    simp
  rw [ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.moebius_apply_prime_pow hp hk]
  split_ifs <;> norm_num

end HardyTheorem
