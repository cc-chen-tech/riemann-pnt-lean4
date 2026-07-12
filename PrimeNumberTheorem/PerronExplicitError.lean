import PrimeNumberTheorem.VonMangoldtPerronTruncated

/-!
# Closed-form error for truncated von Mangoldt Perron inversion

This module combines the finite-height von Mangoldt formula with Chebyshev's
explicit upper bound to remove the remaining coefficient sum from the error.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace PrimeNumberTheorem

theorem norm_truncated_vonMangoldt_secondOrderPerron_sub_smoothedPsi_le_explicit
    {x c W : ℝ} (hx : 1 ≤ x) (hc : 0 < c) (hW : 0 < W) :
    ‖(∫ w : ℝ in (-W)..W,
        ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1), (vonMangoldt n : ℂ) *
          (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) *
            Real.log (x / n)) /
              ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)) -
        (smoothedChebyshevPsi x : ℂ)‖ ≤
      x ^ c * ((Real.log 4 + 4) * x) / (2 * Real.pi ^ 2 * W) := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hden : 0 ≤ 2 * Real.pi ^ 2 * W := by positivity
  have hsum :
      (∑ n ∈ Finset.Ico 1 (Nat.floor x + 1), vonMangoldt n * (x / n) ^ c) ≤
        x ^ c * chebyshevPsi x := by
    rw [chebyshevPsi, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rcases Finset.mem_Ico.mp hn with ⟨hn_one, hn_upper⟩
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_one)
    have hn_one_real : 1 ≤ (n : ℝ) := by exact_mod_cast hn_one
    have hratio_nonneg : 0 ≤ x / (n : ℝ) := div_nonneg hx_pos.le hn_pos.le
    have hratio_le : x / (n : ℝ) ≤ x := by
      apply (div_le_iff₀ hn_pos).2
      nlinarith
    have hrpow : (x / (n : ℝ)) ^ c ≤ x ^ c :=
      Real.rpow_le_rpow hratio_nonneg hratio_le hc.le
    have hv_nonneg : 0 ≤ vonMangoldt n := by
      rw [vonMangoldt_eq_mathlib]
      exact ArithmeticFunction.vonMangoldt_nonneg
    nlinarith
  have hpsi : chebyshevPsi x ≤ (Real.log 4 + 4) * x := by
    rw [chebyshevPsi_eq_mathlib]
    exact Chebyshev.psi_le_const_mul_self hx_pos.le
  have hprod : x ^ c * chebyshevPsi x ≤ x ^ c * ((Real.log 4 + 4) * x) :=
    mul_le_mul_of_nonneg_left hpsi (Real.rpow_nonneg hx_pos.le c)
  calc
    _ ≤ ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1),
        vonMangoldt n * (x / n) ^ c / (2 * Real.pi ^ 2 * W) :=
      norm_truncated_vonMangoldt_secondOrderPerron_sub_smoothedPsi_le hx_pos hc hW
    _ = (∑ n ∈ Finset.Ico 1 (Nat.floor x + 1),
        vonMangoldt n * (x / n) ^ c) / (2 * Real.pi ^ 2 * W) := by
      rw [Finset.sum_div]
    _ ≤ (x ^ c * chebyshevPsi x) / (2 * Real.pi ^ 2 * W) :=
      div_le_div_of_nonneg_right hsum hden
    _ ≤ x ^ c * ((Real.log 4 + 4) * x) / (2 * Real.pi ^ 2 * W) :=
      div_le_div_of_nonneg_right hprod hden

end PrimeNumberTheorem
