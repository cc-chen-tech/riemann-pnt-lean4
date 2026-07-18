import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet

open Complex
open scoped ArithmeticFunction BigOperators LSeries.notation

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- Absolute von Mangoldt Dirichlet-series majorant on the real line
`Re(s) = 1 + ε`. -/
noncomputable def vonMangoldtLSeriesNorm (ε : ℝ) : ℝ :=
  ∑' n : ℕ, ‖LSeries.term
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((1 + ε : ℝ) : ℂ) n‖

private theorem tsum_one_div_nat_rpow_le_one_add_inv_sub_one
    {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, 1 / (n : ℝ) ^ s) ≤ 1 + 1 / (s - 1) := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ s) :=
    Real.summable_one_div_nat_rpow.mpr hs
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have hshift :
      (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) =
        ∑' n : ℕ, 1 / (n : ℝ) ^ s := by
    simpa [Real.zero_rpow (by linarith : s ≠ 0)] using hsplit
  have hterm : 0 ≤ ZetaAsymptotics.term_tsum s :=
    tsum_nonneg fun n => ZetaAsymptotics.term_nonneg (n + 1) s
  have haux := ZetaAsymptotics.zeta_limit_aux1 hs
  rw [← hshift]
  nlinarith [mul_nonneg (by linarith : 0 ≤ s) hterm]

/-- Quantitative growth of the absolute von Mangoldt Dirichlet series as its
real part approaches one. -/
theorem vonMangoldtLSeriesNorm_le_two_div_mul_one_add_two_div
    {ε : ℝ} (hε : 0 < ε) :
    vonMangoldtLSeriesNorm ε ≤
      (2 / ε) * (1 + 2 / ε) := by
  let p : ℝ := 1 + ε / 2
  let f : ℕ → ℝ := fun n =>
    ‖LSeries.term
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((1 + ε : ℝ) : ℂ) n‖
  let g : ℕ → ℝ := fun n => (2 / ε) * (1 / (n : ℝ) ^ p)
  have hp : 1 < p := by dsimp [p]; linarith
  have hf : Summable f := by
    have h := ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := ((1 + ε : ℝ) : ℂ)) (by simpa using hε)
    rw [LSeriesSummable, ← summable_norm_iff] at h
    simpa [f] using h
  have hpseries : Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) :=
    Real.summable_one_div_nat_rpow.mpr hp
  have hg : Summable g := hpseries.mul_left (2 / ε)
  have hpoint : ∀ n : ℕ, f n ≤ g n := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [f, g, LSeries.term,
        Real.zero_rpow (zero_lt_one.trans hp).ne']
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hvnonneg : 0 ≤ ArithmeticFunction.vonMangoldt n :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hvlog : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    have hlogpow : Real.log (n : ℝ) ≤
        (n : ℝ) ^ (ε / 2) / (ε / 2) :=
      Real.log_natCast_le_rpow_div n (by linarith)
    have hvpow : ArithmeticFunction.vonMangoldt n ≤
        (n : ℝ) ^ (ε / 2) / (ε / 2) := hvlog.trans hlogpow
    dsimp [f, g, p]
    rw [LSeries.norm_term_eq]
    simp only [hn, if_false, Complex.ofReal_re]
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hvnonneg]
    calc
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + ε) ≤
          ((n : ℝ) ^ (ε / 2) / (ε / 2)) /
            (n : ℝ) ^ (1 + ε) := by
        exact div_le_div_of_nonneg_right hvpow (Real.rpow_nonneg hnpos.le _)
      _ = (2 / ε) * (1 / (n : ℝ) ^ (1 + ε / 2)) := by
        rw [show 1 + ε = ε / 2 + (1 + ε / 2) by ring,
          Real.rpow_add hnpos]
        field_simp [hε.ne', (Real.rpow_pos_of_pos hnpos (ε / 2)).ne',
          (Real.rpow_pos_of_pos hnpos (1 + ε / 2)).ne']
  have hmajor := Summable.tsum_le_tsum hpoint hf hg
  have hpbound := tsum_one_div_nat_rpow_le_one_add_inv_sub_one hp
  change vonMangoldtLSeriesNorm ε ≤ _
  rw [show vonMangoldtLSeriesNorm ε = ∑' n, f n by rfl]
  calc
    (∑' n, f n) ≤ ∑' n, g n := hmajor
    _ = (2 / ε) * (∑' n : ℕ, 1 / (n : ℝ) ^ p) := tsum_mul_left
    _ ≤ (2 / ε) * (1 + 1 / (p - 1)) := by
      exact mul_le_mul_of_nonneg_left hpbound (by positivity)
    _ = (2 / ε) * (1 + 2 / ε) := by
      dsimp [p]
      field_simp [hε.ne']
      <;> ring

end ExplicitFormulaResidues
end PrimeNumberTheorem
