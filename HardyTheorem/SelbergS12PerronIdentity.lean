import HardyTheorem.SelbergS12CoprimeDirichlet
import HardyTheorem.SelbergPerronLSeries

open Complex MeasureTheory Filter
open scoped LSeries.notation BigOperators

namespace HardyTheorem

/-!
# Selberg S12: the exact coprime weighted Perron identity

We absorb `n^{-(1-theta)}` into the coefficients, apply the absolute logarithmic Perron theorem,
and then use the support of `log⁺(Y/n)` to turn the infinite sum into the exact finite sum
`1 ≤ n < Y`.
-/

noncomputable def selbergS12ShiftedCoprimeCoeff
    (r : ℕ) (theta : ℝ) (n : ℕ) : ℂ :=
  selbergS12CoprimeCoeff r n *
    (n : ℂ) ^ (-((1 - theta : ℝ) : ℂ))

theorem LSeries_term_selbergS12ShiftedCoprimeCoeff
    (r : ℕ) (theta : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (selbergS12ShiftedCoprimeCoeff r theta) s n =
      LSeries.term (selbergS12CoprimeCoeff r)
        (((1 - theta : ℝ) : ℂ) + s) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    unfold selbergS12ShiftedCoprimeCoeff
    rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn), Complex.cpow_neg]
    field_simp [Complex.cpow_ne_zero_iff, Nat.cast_ne_zero.mpr hn]

theorem LSeries_selbergS12ShiftedCoprimeCoeff_eq
    (r : ℕ) (theta : ℝ) (s : ℂ) :
    L (selbergS12ShiftedCoprimeCoeff r theta) s =
      selbergS12CoprimeDirichletSeries r
        (((1 - theta : ℝ) : ℂ) + s) := by
  unfold LSeries selbergS12CoprimeDirichletSeries
  apply tsum_congr
  exact LSeries_term_selbergS12ShiftedCoprimeCoeff r theta s

theorem LSeriesSummable_selbergS12ShiftedCoprimeCoeff
    {r : ℕ} {theta sigma : ℝ} (h : theta < sigma) :
    LSeriesSummable (selbergS12ShiftedCoprimeCoeff r theta) (sigma : ℂ) := by
  have hre : 1 < ((((1 - theta : ℝ) : ℂ) + (sigma : ℂ)).re) := by
    norm_num
    linarith
  have horig := LSeriesSummable_selbergS12CoprimeCoeff (r := r) hre
  rw [LSeriesSummable] at horig ⊢
  exact horig.congr fun n =>
    (LSeries_term_selbergS12ShiftedCoprimeCoeff r theta (sigma : ℂ) n).symm

noncomputable def selbergS12WeightedCoprimeSum
    (r : ℕ) (theta : ℝ) (Y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico 1 Y,
    selbergS12ShiftedCoprimeCoeff r theta n *
      (Real.log ((Y : ℝ) / (n : ℝ)) : ℂ)

theorem tsum_selbergS12ShiftedCoprimeCoeff_mul_cutoff_eq
    (r : ℕ) (theta : ℝ) {Y : ℕ} (hY : 0 < Y) :
    (∑' n : ℕ, selbergS12ShiftedCoprimeCoeff r theta n *
        perronLogCutoff ((n : ℝ) / (Y : ℝ))) =
      selbergS12WeightedCoprimeSum r theta Y := by
  rw [tsum_eq_sum (s := Finset.Ico 1 Y)]
  · unfold selbergS12WeightedCoprimeSum
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
    have hnY : n ≤ Y := (Finset.mem_Ico.mp hn).2.le
    rw [perronLogCutoff_nat_div_eq_log (Nat.zero_lt_of_lt hn1) hY hnY]
  · intro n hnout
    by_cases hn0 : n = 0
    · subst n
      simp [selbergS12ShiftedCoprimeCoeff, selbergS12CoprimeCoeff]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn0
      have hYn : Y ≤ n := by
        by_contra hnot
        exact hnout (Finset.mem_Ico.2 ⟨hn1, Nat.lt_of_not_ge hnot⟩)
      rw [perronLogCutoff_nat_div_eq_zero (Nat.pos_of_ne_zero hn0) hY hYn]
      simp

noncomputable def selbergS12PerronIntegrand
    (r : ℕ) (theta Y sigma t : ℝ) : ℂ :=
  (Y : ℂ) ^ selbergPerronLine sigma t *
    selbergS12CoprimeDirichletSeries r
      (((1 - theta : ℝ) : ℂ) + selbergPerronLine sigma t) *
      (1 / (selbergPerronLine sigma t) ^ 2)

private theorem selbergS12PerronIntegrand_eq_generic
    (r : ℕ) (theta Y sigma t : ℝ) :
    selbergS12PerronIntegrand r theta Y sigma t =
      selbergPerronLSeriesIntegrand
        (selbergS12ShiftedCoprimeCoeff r theta) Y sigma t := by
  unfold selbergS12PerronIntegrand selbergPerronLSeriesIntegrand
  rw [LSeries_selbergS12ShiftedCoprimeCoeff_eq]

theorem normalized_integral_selbergS12PerronIntegrand_eq_weightedSum
    (r : ℕ) (theta : ℝ) {Y : ℕ} {sigma : ℝ}
    (htheta : 0 ≤ theta) (hY : 0 < Y) (hsigma : theta < sigma) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, selbergS12PerronIntegrand r theta (Y : ℝ) sigma t) =
      selbergS12WeightedCoprimeSum r theta Y := by
  have hsigma0 : 0 < sigma := htheta.trans_lt hsigma
  have hsum : LSeriesSummable
      (selbergS12ShiftedCoprimeCoeff r theta) (sigma : ℂ) :=
    LSeriesSummable_selbergS12ShiftedCoprimeCoeff hsigma
  rw [integral_congr_ae (Eventually.of_forall
    (selbergS12PerronIntegrand_eq_generic r theta (Y : ℝ) sigma))]
  rw [normalized_integral_selbergPerronLSeries_eq
    (selbergS12ShiftedCoprimeCoeff r theta)
    (by exact_mod_cast hY) hsigma0 hsum]
  exact tsum_selbergS12ShiftedCoprimeCoeff_mul_cutoff_eq r theta hY

end HardyTheorem
