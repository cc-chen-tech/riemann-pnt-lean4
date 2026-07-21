import HardyTheorem.SelbergMertensBound

open Finset
open scoped BigOperators

namespace HardyTheorem

/-!
# Lower bound for Selberg's mollified triple main coefficient

This file turns the explicit Mertens bounds of `SelbergMertensBound.lean`
into a quantitative lower bound for the real part of the main coefficient
`selbergMollifiedTripleCollectedCoeff N X 1`.

The main coefficient equals `1 - W / log X` where

```
W = ∑_{p ≤ X} (1 - log p / log X) * log p / p .
```

The key steps are:

* a lower Mertens bound for the von Mangoldt sum,
  `log N - 1 ≤ ∑_{n ≤ N} Λ(n) / n`, read off the factorial identity;
* a two-scale split at `sqrt X` giving
  `∑_{n ≤ X} Λ(n) log n / n ≥ (log X)² / 4 - ((log 4 + 6) / 2) * log X`;
* enlarging the prime sum `W` to the von Mangoldt weighted sum, which
  telescopes as `S1 - S2 / log X`;
* assembly into
  `(selbergMollifiedTripleCollectedCoeff N X 1).re ≥ 1/4 - C / log X`
  with `C = (3 log 4 + 16) / 2`, and a `1/8` corollary for
  `log X ≥ 12 log 4 + 64`.
-/

/-- Lower Mertens bound for the von Mangoldt sum, from the factorial
identity: `log N - 1 ≤ ∑_{n ≤ N} Λ(n) / n`. -/
theorem log_sub_one_le_vonMangoldt_sum_div {N : ℕ} (hN : 1 ≤ N) :
    Real.log N - 1 ≤
      ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hid := log_sum_Icc_eq_sum_vonMangoldt_mul_div N
  have hle := le_log_sum_Icc hN
  have hfloor : ∑ d ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) ≤
      (N : ℝ) * ∑ d ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt d / (d : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd1)
    have hcast : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
    have h1 : ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) ≤
        ArithmeticFunction.vonMangoldt d * ((N : ℝ) / (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hcast ArithmeticFunction.vonMangoldt_nonneg
    have h2 : ArithmeticFunction.vonMangoldt d * ((N : ℝ) / (d : ℝ)) =
        (N : ℝ) * (ArithmeticFunction.vonMangoldt d / (d : ℝ)) := by
      field_simp
    exact h1.trans_eq h2
  rw [← hid] at hfloor
  have hmain : (N : ℝ) * Real.log N - N + 1 ≤
      (N : ℝ) * ∑ d ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt d / (d : ℝ) :=
    hle.trans hfloor
  have h3 : Real.log (N : ℝ) - 1 ≤ ((N : ℝ) * Real.log N - N + 1) / N := by
    rw [le_div_iff₀ hNpos]
    have hexp : (Real.log (N : ℝ) - 1) * (N : ℝ) =
        (N : ℝ) * Real.log (N : ℝ) - N := by ring
    linarith [hexp]
  have h4 : ((N : ℝ) * Real.log N - N + 1) / N ≤
      ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d / (d : ℝ) := by
    rw [div_le_iff₀ hNpos]
    have hcomm : (N : ℝ) * ∑ d ∈ Finset.Icc 1 N,
          ArithmeticFunction.vonMangoldt d / (d : ℝ) =
        (∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d / (d : ℝ)) *
          N := mul_comm _ _
    linarith [hmain, hcomm]
  exact h3.trans h4

/-- Two-scale lower bound for the log-weighted von Mangoldt sum: splitting
at `sqrt X`, every term above the split carries a factor `log n ≥ log X / 2`,
so the Mertens upper bound at `sqrt X` and the lower bound at `X` yield
`∑_{n ≤ X} Λ(n) log n / n ≥ (log X)² / 4 - ((log 4 + 6) / 2) * log X`. -/
theorem vonMangoldt_log_sum_div_ge {X : ℕ} (hX : 2 ≤ X) :
    (Real.log (X : ℝ)) ^ 2 / 4 - ((Real.log 4 + 6) / 2) * Real.log (X : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 X,
        ArithmeticFunction.vonMangoldt n * Real.log n / (n : ℝ) := by
  have hX1 : 1 ≤ X := by omega
  have hs1 : 1 ≤ Nat.sqrt X := Nat.sqrt_pos.2 (by omega : 0 < X)
  have hLpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hsplit : Finset.Icc 1 (Nat.sqrt X) ∪ Finset.Ioc (Nat.sqrt X) X =
      Finset.Icc 1 X := by
    have hsX : Nat.sqrt X ≤ X := Nat.sqrt_le_self X
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (Nat.sqrt X)) (Finset.Ioc (Nat.sqrt X) X) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    rcases Finset.mem_Icc.mp hn1 with ⟨-, hn1'⟩
    rcases Finset.mem_Ioc.mp hn2 with ⟨hn2', -⟩
    omega
  have hsqrt_low : Real.log (X : ℝ) / 2 ≤ Real.log ((Nat.sqrt X : ℝ) + 1) := by
    have h' : X ≤ (Nat.sqrt X + 1) * (Nat.sqrt X + 1) :=
      le_of_lt (Nat.lt_succ_sqrt X)
    have hcast : (X : ℝ) ≤ ((Nat.sqrt X : ℝ) + 1) * ((Nat.sqrt X : ℝ) + 1) := by
      exact_mod_cast h'
    have h3 : Real.sqrt (X : ℝ) ≤ (Nat.sqrt X : ℝ) + 1 := by
      have h4 := Real.sqrt_le_sqrt hcast
      rwa [show ((Nat.sqrt X : ℝ) + 1) * ((Nat.sqrt X : ℝ) + 1) =
          ((Nat.sqrt X : ℝ) + 1) ^ 2 by ring,
        Real.sqrt_sq (by positivity)] at h4
    calc Real.log (X : ℝ) / 2 = Real.log (Real.sqrt (X : ℝ)) :=
          (Real.log_sqrt (Nat.cast_nonneg X)).symm
      _ ≤ Real.log ((Nat.sqrt X : ℝ) + 1) :=
          Real.log_le_log (Real.sqrt_pos.2 (by positivity)) h3
  have hlogY : Real.log (Nat.sqrt X : ℝ) ≤ Real.log (X : ℝ) / 2 := by
    have hle : (Nat.sqrt X : ℝ) ≤ Real.sqrt (X : ℝ) := Real.nat_sqrt_le_real_sqrt
    calc Real.log (Nat.sqrt X : ℝ) ≤ Real.log (Real.sqrt (X : ℝ)) :=
          Real.log_le_log (by exact_mod_cast hs1) hle
      _ = Real.log (X : ℝ) / 2 := Real.log_sqrt (Nat.cast_nonneg X)
  have htop : (Real.log (X : ℝ) / 2) * ∑ n ∈ Finset.Ioc (Nat.sqrt X) X,
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤
      ∑ n ∈ Finset.Ioc (Nat.sqrt X) X,
        ArithmeticFunction.vonMangoldt n * Real.log n / (n : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hsn : Nat.sqrt X + 1 ≤ n := (Finset.mem_Ioc.mp hn).1
    have hlogn : Real.log (X : ℝ) / 2 ≤ Real.log (n : ℝ) := by
      have h1 : Real.log ((Nat.sqrt X : ℝ) + 1) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hsn)
      exact hsqrt_low.trans h1
    have hnnonneg : 0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hlogn hnnonneg
    rw [mul_comm] at h1
    have h2 : ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) / (n : ℝ) =
        (ArithmeticFunction.vonMangoldt n / (n : ℝ)) * Real.log (n : ℝ) := by ring
    exact h1.trans_eq h2.symm
  have hIoc_le : ∑ n ∈ Finset.Ioc (Nat.sqrt X) X,
        ArithmeticFunction.vonMangoldt n * Real.log n / (n : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 X,
        ArithmeticFunction.vonMangoldt n * Real.log n / (n : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rcases Finset.mem_Ioc.mp hn with ⟨h1, h2⟩
      exact Finset.mem_Icc.mpr ⟨by omega, h2⟩
    · intro n hn1 hn2
      exact div_nonneg
        (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hn1).1)))
        (by positivity)
  have hS1split : ∑ n ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt n / (n : ℝ) =
      ∑ n ∈ Finset.Icc 1 (Nat.sqrt X), ArithmeticFunction.vonMangoldt n / (n : ℝ) +
      ∑ n ∈ Finset.Ioc (Nat.sqrt X) X, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
    rw [← hsplit, Finset.sum_union hdisj]
  have hS1X := log_sub_one_le_vonMangoldt_sum_div (N := X) hX1
  have hS1Y := vonMangoldt_sum_div_le_log_add (N := Nat.sqrt X) hs1
  have hA : Real.log (X : ℝ) / 2 - (1 + (Real.log 4 + 5)) ≤
      ∑ n ∈ Finset.Ioc (Nat.sqrt X) X, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
    linarith [hS1X, hS1Y, hlogY, hS1split]
  have hmul := mul_le_mul_of_nonneg_left hA
    (show (0 : ℝ) ≤ Real.log (X : ℝ) / 2 by linarith [hLpos])
  have hexp : (Real.log (X : ℝ) / 2) * (Real.log (X : ℝ) / 2 - (1 + (Real.log 4 + 5))) =
      (Real.log (X : ℝ)) ^ 2 / 4 - ((Real.log 4 + 6) / 2) * Real.log (X : ℝ) := by ring
  linarith [htop, hIoc_le, hmul, hexp]

/-- The mollified prime sum is majorized by the mollified von Mangoldt sum:
the two agree on primes, and every remaining von Mangoldt term is
nonnegative on `n ≤ X`. -/
theorem weighted_primeLogSum_le_weighted_vonMangoldt {X : ℕ} (hX : 2 ≤ X) :
    ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
        selbergMoebiusWeight X p * Real.log p / (p : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 X,
        selbergMoebiusWeight X n * ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
  have hterm : ∀ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
      selbergMoebiusWeight X p * Real.log p / (p : ℝ) =
        selbergMoebiusWeight X p * ArithmeticFunction.vonMangoldt p / (p : ℝ) := by
    intro p hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl hterm]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpI, -⟩
    rcases Finset.mem_Icc.mp hpI with ⟨hp2, hpX⟩
    exact Finset.mem_Icc.mpr ⟨by omega, hpX⟩
  · intro n hn1 hn2
    have hmem := Finset.mem_Icc.mp hn1
    have hw := (selbergMoebiusWeight_mem_Icc hX hmem.1 hmem.2).1
    exact div_nonneg (mul_nonneg hw ArithmeticFunction.vonMangoldt_nonneg)
      (by positivity)

/-- The mollified von Mangoldt sum telescopes as `S1 - S2 / log X`, where
`S1 = ∑ Λ(n)/n` and `S2 = ∑ Λ(n) log n / n`. -/
theorem weighted_vonMangoldt_sum_eq (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X,
        selbergMoebiusWeight X n * ArithmeticFunction.vonMangoldt n / (n : ℝ) =
      (∑ n ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
        (∑ n ∈ Finset.Icc 1 X,
          ArithmeticFunction.vonMangoldt n * Real.log n / (n : ℝ)) /
          Real.log X := by
  have hterm : ∀ n ∈ Finset.Icc 1 X,
      selbergMoebiusWeight X n * ArithmeticFunction.vonMangoldt n / (n : ℝ) =
        ArithmeticFunction.vonMangoldt n / (n : ℝ) -
          (ArithmeticFunction.vonMangoldt n * Real.log n / (n : ℝ)) /
            Real.log X := by
    intro n hn
    rw [selbergMoebiusWeight]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_div]

/-- Quantitative lower bound `1/4 - C / log X`, `C = (3 log 4 + 16) / 2`,
for the mollified prime main term `1 - W / log X`. -/
theorem one_sub_primeLogSum_div_ge {X : ℕ} (hX : 2 ≤ X) :
    (1 : ℝ) / 4 - ((3 * Real.log 4 + 16) / 2) / Real.log X ≤
      1 - (∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
          selbergMoebiusWeight X p * Real.log p / (p : ℝ)) / Real.log X := by
  have hL : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hL0 : Real.log (X : ℝ) ≠ 0 := ne_of_gt hL
  have hW := weighted_primeLogSum_le_weighted_vonMangoldt hX
  have hWΛ := weighted_vonMangoldt_sum_eq X
  have hS1 := vonMangoldt_sum_div_le_log_add (N := X) (by omega : 1 ≤ X)
  have hS2 := vonMangoldt_log_sum_div_ge hX
  have hS2div : ((Real.log (X : ℝ)) ^ 2 / 4 - ((Real.log 4 + 6) / 2) * Real.log (X : ℝ)) /
        Real.log X ≤
      (∑ n ∈ Finset.Icc 1 X,
          ArithmeticFunction.vonMangoldt n * Real.log n / (n : ℝ)) /
        Real.log X := by
    rw [div_le_iff₀ hL, div_mul_cancel₀ _ hL0]
    exact hS2
  have hk : ((Real.log (X : ℝ)) ^ 2 / 4 - ((Real.log 4 + 6) / 2) * Real.log (X : ℝ)) /
        Real.log X =
      Real.log (X : ℝ) / 4 - (Real.log 4 + 6) / 2 := by
    rw [div_eq_iff hL0]
    ring
  have hWΛ34 : ∑ n ∈ Finset.Icc 1 X,
        selbergMoebiusWeight X n * ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤
      3 * Real.log (X : ℝ) / 4 + (3 * Real.log 4 + 16) / 2 := by
    rw [hWΛ]
    linarith [hS1, hS2div, hk]
  have hW34 : ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
        selbergMoebiusWeight X p * Real.log p / (p : ℝ) ≤
      3 * Real.log (X : ℝ) / 4 + (3 * Real.log 4 + 16) / 2 := hW.trans hWΛ34
  have hW34L : (∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
        selbergMoebiusWeight X p * Real.log p / (p : ℝ)) / Real.log X ≤
      (3 * Real.log (X : ℝ) / 4 + (3 * Real.log 4 + 16) / 2) / Real.log X := by
    rw [div_le_iff₀ hL, div_mul_cancel₀ _ hL0]
    exact hW34
  have hLinv : Real.log (X : ℝ) * (Real.log (X : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hL0
  have heq : (3 * Real.log (X : ℝ) / 4 + (3 * Real.log 4 + 16) / 2) / Real.log X =
      3 / 4 + ((3 * Real.log 4 + 16) / 2) / Real.log X := by
    rw [div_eq_mul_inv, div_eq_mul_inv ((3 * Real.log 4 + 16) / 2), add_mul]
    have h2 : (3 * Real.log (X : ℝ) / 4) * (Real.log (X : ℝ))⁻¹ = 3 / 4 := by
      have h3 : (3 * Real.log (X : ℝ) / 4) * (Real.log (X : ℝ))⁻¹ =
          (3 / 4) * (Real.log (X : ℝ) * (Real.log (X : ℝ))⁻¹) := by ring
      rw [h3, hLinv, mul_one]
    rw [h2]
  linarith [hW34L, heq]

/-- The real part of Selberg's mollified triple main coefficient is at least
`1/4 - C / log X` with `C = (3 log 4 + 16) / 2`. -/
theorem selbergMollifiedTripleCollectedCoeff_one_re_ge {N X : ℕ}
    (hX : 2 ≤ X) (hNX : X ≤ N) :
    (1 : ℝ) / 4 - ((3 * Real.log 4 + 16) / 2) / Real.log X ≤
      (selbergMollifiedTripleCollectedCoeff N X 1).re := by
  have h := selbergMollifiedTripleCollectedCoeff_one_eq_primeMainTerm
    (N := N) (X := X) (by omega : 1 ≤ X) hNX
  rw [h, Complex.ofReal_re]
  exact one_sub_primeLogSum_div_ge hX

/-- For `log X ≥ 12 log 4 + 64` the main coefficient has real part at least
`1/8`: the principal contribution `1/4` dominates the explicit error. -/
theorem selbergMollifiedTripleCollectedCoeff_one_re_ge_one_eighth {N X : ℕ}
    (hX : 2 ≤ X) (hNX : X ≤ N) (hXL : 12 * Real.log 4 + 64 ≤ Real.log X) :
    (1 : ℝ) / 8 ≤ (selbergMollifiedTripleCollectedCoeff N X 1).re := by
  have h := selbergMollifiedTripleCollectedCoeff_one_re_ge hX hNX
  have hL : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hCL : ((3 * Real.log 4 + 16) / 2) / Real.log X ≤ 1 / 8 := by
    rw [div_le_iff₀ hL]
    linarith [hXL]
  linarith [h, hCL]

end HardyTheorem
