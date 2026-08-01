import PrimeNumberTheorem.RieszDifference
import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderPerronTruncation

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace PrimeNumberTheorem

/-- The second Riesz mean of the von Mangoldt coefficients. -/
noncomputable def secondRieszChebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1),
    vonMangoldt n * Real.log (x / n) ^ 2 / 2

theorem norm_truncated_finset_thirdOrderPerron_sub_sum_half_sq_max_le
    {ι : Type*} (S : Finset ι) (a : ι → ℝ) (u : ι → ℝ)
    {c W : ℝ} (ha : ∀ i ∈ S, 0 ≤ a i) (hc : 0 < c) (hW : 0 < W) :
    ‖(∫ w : ℝ in (-W)..W, ∑ i ∈ S, (a i : ℂ) *
        (exp (((c : ℂ) + 2 * Real.pi * w * I) * u i) /
          ((c : ℂ) + 2 * Real.pi * w * I) ^ 3)) -
      ∑ i ∈ S, (a i : ℂ) * ((((max (u i) 0) ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      ∑ i ∈ S, a i * Real.exp (c * u i) /
        (8 * Real.pi ^ 3 * W ^ 2) := by
  let K : ι → ℝ → ℂ := fun i w =>
    exp (((c : ℂ) + 2 * Real.pi * w * I) * u i) /
      ((c : ℂ) + 2 * Real.pi * w * I) ^ 3
  have hK (i : ι) : Integrable (K i) := by
    simpa [K] using integrable_thirdOrderPerronKernel c hc (u i)
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
      (exp (((c : ℂ) + 2 * Real.pi * w * I) * u i) /
        ((c : ℂ) + 2 * Real.pi * w * I) ^ 3)) =
      (fun w : ℝ => ∑ i ∈ S, (a i : ℂ) * K i w) by rfl]
  rw [hinter, ← Finset.sum_sub_distrib]
  calc
    ‖∑ i ∈ S,
        ((a i : ℂ) * (∫ w : ℝ in (-W)..W, K i w) -
          (a i : ℂ) * ((((max (u i) 0) ^ 2 / 2 : ℝ) : ℂ)))‖ =
        ‖∑ i ∈ S, (a i : ℂ) *
          ((∫ w : ℝ in (-W)..W, K i w) -
            ((((max (u i) 0) ^ 2 / 2 : ℝ) : ℂ)))‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ S, ‖(a i : ℂ) *
          ((∫ w : ℝ in (-W)..W, K i w) -
            ((((max (u i) 0) ^ 2 / 2 : ℝ) : ℂ)))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, a i * Real.exp (c * u i) /
        (8 * Real.pi ^ 3 * W ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (ha i hi)]
      calc
        a i * ‖(∫ w : ℝ in (-W)..W, K i w) -
            ((((max (u i) 0) ^ 2 / 2 : ℝ) : ℂ))‖ ≤
            a i * (Real.exp (c * u i) /
              (8 * Real.pi ^ 3 * W ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (ha i hi)
          simpa [K] using norm_truncated_thirdOrderPerron_sub_half_sq_max_le
            (c := c) (u := u i) (W := W) hc hW
        _ = a i * Real.exp (c * u i) /
            (8 * Real.pi ^ 3 * W ^ 2) := by ring

lemma sum_vonMangoldt_half_sq_max_log_div_eq_secondRieszChebyshevPsi
    (x : ℝ) (hx : 0 < x) :
    (∑ n ∈ Finset.Ico 1 (Nat.floor x + 1),
      vonMangoldt n * (max (Real.log (x / n)) 0) ^ 2 / 2) =
      secondRieszChebyshevPsi x := by
  rw [secondRieszChebyshevPsi]
  apply Finset.sum_congr rfl
  intro n hn
  rcases Finset.mem_Ico.mp hn with ⟨hn_one, hn_upper⟩
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_one)
  have hn_floor : n ≤ Nat.floor x := by omega
  have hn_x : (n : ℝ) ≤ x := by
    exact le_trans (by exact_mod_cast hn_floor) (Nat.floor_le hx.le)
  have hratio : 1 ≤ x / (n : ℝ) :=
    (le_div_iff₀ hn_pos).2 (by simpa using hn_x)
  rw [max_eq_left (Real.log_nonneg hratio)]

/-- Finite-height cubic Perron formula for the actual von Mangoldt second
Riesz mean, with an explicit quadratic truncation error. -/
theorem norm_truncated_vonMangoldt_thirdOrderPerron_sub_secondRieszPsi_le
    {x c W : ℝ} (hx : 0 < x) (hc : 0 < c) (hW : 0 < W) :
    ‖(∫ w : ℝ in (-W)..W,
        ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1), (vonMangoldt n : ℂ) *
          (exp (((c : ℂ) + 2 * Real.pi * w * I) *
            Real.log (x / n)) /
              ((c : ℂ) + 2 * Real.pi * w * I) ^ 3)) -
        (secondRieszChebyshevPsi x : ℂ)‖ ≤
      ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1),
        vonMangoldt n * (x / n) ^ c /
          (8 * Real.pi ^ 3 * W ^ 2) := by
  let S := Finset.Ico 1 (Nat.floor x + 1)
  have ha : ∀ n ∈ S, 0 ≤ vonMangoldt n := by
    intro n hn
    rw [vonMangoldt_eq_mathlib]
    exact ArithmeticFunction.vonMangoldt_nonneg
  have hgen := norm_truncated_finset_thirdOrderPerron_sub_sum_half_sq_max_le
    S vonMangoldt (fun n => Real.log (x / n)) ha hc hW
  have hcenter_real :
      (∑ n ∈ S, vonMangoldt n * (max (Real.log (x / n)) 0) ^ 2 / 2) =
        secondRieszChebyshevPsi x := by
    exact sum_vonMangoldt_half_sq_max_log_div_eq_secondRieszChebyshevPsi x hx
  have hcenter_complex :
      (∑ n ∈ S, (vonMangoldt n : ℂ) *
        ((((max (Real.log (x / n)) 0) ^ 2 / 2 : ℝ) : ℂ))) =
        (secondRieszChebyshevPsi x : ℂ) := by
    rw [← hcenter_real, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring
  rw [hcenter_complex] at hgen
  change _ ≤ ∑ n ∈ S, vonMangoldt n * (x / n) ^ c /
    (8 * Real.pi ^ 3 * W ^ 2)
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
