import PrimeNumberTheorem.PerronTruncation
import PrimeNumberTheorem.RieszDifference

/-!
# Finite-height Perron formula for von Mangoldt coefficients

This module sums the second-order kernel truncation error over nonnegative
coefficients and specializes the result to the von Mangoldt first Riesz mean.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace PrimeNumberTheorem

theorem norm_truncated_finset_secondOrderPerron_sub_sum_max_le
    {ι : Type*} (S : Finset ι) (a : ι → ℝ) (u : ι → ℝ)
    {c W : ℝ} (ha : ∀ i ∈ S, 0 ≤ a i) (hc : 0 < c) (hW : 0 < W) :
    ‖(∫ w : ℝ in (-W)..W, ∑ i ∈ S, (a i : ℂ) *
        (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u i) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)) -
      ∑ i ∈ S, (a i : ℂ) * ((max (u i) 0 : ℝ) : ℂ)‖ ≤
      ∑ i ∈ S, a i * Real.exp (c * u i) / (2 * Real.pi ^ 2 * W) := by
  let K : ι → ℝ → ℂ := fun i w =>
    Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u i) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2
  have hK (i : ι) : Integrable (K i) := by
    simpa [K] using integrable_secondOrderPerronKernel c hc (u i)
  have hinter :
      (∫ w : ℝ in (-W)..W, ∑ i ∈ S, (a i : ℂ) * K i w) =
        ∑ i ∈ S, (a i : ℂ) * (∫ w : ℝ in (-W)..W, K i w) := by
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i hi
      exact intervalIntegral.integral_const_mul (a i : ℂ) (K i)
    · intro i hi
      exact (hK i).const_mul (a i : ℂ) |>.intervalIntegrable
  rw [show (fun w : ℝ => ∑ i ∈ S, (a i : ℂ) *
      (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u i) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)) =
      (fun w : ℝ => ∑ i ∈ S, (a i : ℂ) * K i w) by rfl]
  rw [hinter, ← Finset.sum_sub_distrib]
  calc
    ‖∑ i ∈ S,
        ((a i : ℂ) * (∫ w : ℝ in (-W)..W, K i w) -
          (a i : ℂ) * ((max (u i) 0 : ℝ) : ℂ))‖ =
        ‖∑ i ∈ S, (a i : ℂ) *
          ((∫ w : ℝ in (-W)..W, K i w) - ((max (u i) 0 : ℝ) : ℂ))‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ S, ‖(a i : ℂ) *
          ((∫ w : ℝ in (-W)..W, K i w) - ((max (u i) 0 : ℝ) : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ S, a i * Real.exp (c * u i) / (2 * Real.pi ^ 2 * W) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (ha i hi)]
      calc
        a i * ‖(∫ w : ℝ in (-W)..W, K i w) - ((max (u i) 0 : ℝ) : ℂ)‖ ≤
            a i * (Real.exp (c * u i) / (2 * Real.pi ^ 2 * W)) := by
          apply mul_le_mul_of_nonneg_left _ (ha i hi)
          simpa [K] using norm_truncated_secondOrderPerron_sub_max_le
            (c := c) (u := u i) (W := W) hc hW
        _ = a i * Real.exp (c * u i) / (2 * Real.pi ^ 2 * W) := by ring

/-- Finite-height second-order Perron formula for the von Mangoldt Riesz mean. -/
theorem norm_truncated_vonMangoldt_secondOrderPerron_sub_smoothedPsi_le
    {x c W : ℝ} (hx : 0 < x) (hc : 0 < c) (hW : 0 < W) :
    ‖(∫ w : ℝ in (-W)..W,
        ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1), (vonMangoldt n : ℂ) *
          (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) *
            Real.log (x / n)) /
              ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)) -
        (smoothedChebyshevPsi x : ℂ)‖ ≤
      ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1),
        vonMangoldt n * (x / n) ^ c / (2 * Real.pi ^ 2 * W) := by
  let S := Finset.Ico 1 (Nat.floor x + 1)
  have ha : ∀ n ∈ S, 0 ≤ vonMangoldt n := by
    intro n hn
    rw [vonMangoldt_eq_mathlib]
    exact ArithmeticFunction.vonMangoldt_nonneg
  have hgen := norm_truncated_finset_secondOrderPerron_sub_sum_max_le
    S vonMangoldt (fun n => Real.log (x / n)) ha hc hW
  have hcenter_real :
      (∑ n ∈ S, vonMangoldt n * max (Real.log (x / n)) 0) =
        smoothedChebyshevPsi x := by
    exact sum_vonMangoldt_max_log_div_eq_smoothedChebyshevPsi
      x hx (Nat.floor x + 1) (Nat.lt_succ_self _)
  have hcenter_complex :
      (∑ n ∈ S, (vonMangoldt n : ℂ) * ((max (Real.log (x / n)) 0 : ℝ) : ℂ)) =
        (smoothedChebyshevPsi x : ℂ) := by
    rw [← hcenter_real, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    exact (Complex.ofReal_mul _ _).symm
  rw [hcenter_complex] at hgen
  change _ ≤ ∑ n ∈ S, vonMangoldt n * (x / n) ^ c / (2 * Real.pi ^ 2 * W)
  apply hgen.trans_eq
  apply Finset.sum_congr rfl
  intro n hn
  rcases Finset.mem_Ico.mp hn with ⟨hn_one, hn_upper⟩
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_one)
  have hratio : 0 < x / (n : ℝ) := div_pos hx hn_pos
  rw [Real.rpow_def_of_pos hratio]
  congr 2
  ring

end PrimeNumberTheorem
