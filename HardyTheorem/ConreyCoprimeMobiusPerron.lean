import HardyTheorem.SelbergS12CoprimeDirichlet
import HardyTheorem.SelbergPerronLSeries

open Complex MeasureTheory Filter
open ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.Moebius LSeries.notation BigOperators

namespace HardyTheorem

/-!
# The actual coprime Möbius logarithmic Perron identity

On `u > 0`, `Re(alpha) + u > 0`, principal-character inversion identifies
the absolutely convergent shifted series with `1/(zeta * finite Euler factors)`.
The square kernel gives absolute integrability. Its logarithmic cutoff is
exactly the finite sum up to the floor of any positive real `X`.
This is the starting identity for the contour shift, not an asymptotic estimate.
-/

noncomputable def conreyCoprimeMobiusCoeff (d n : ℕ) : ℂ :=
  selbergPrincipalCharacter d n * (ArithmeticFunction.moebius n : ℂ)

theorem conreyCoprimeMobiusCoeff_eq (d n : ℕ) :
    conreyCoprimeMobiusCoeff d n =
      if n.Coprime d then (ArithmeticFunction.moebius n : ℂ) else 0 := by
  unfold conreyCoprimeMobiusCoeff selbergPrincipalCharacter
  by_cases h : n.Coprime d
  · rw [if_pos h, MulChar.one_apply ((ZMod.isUnit_iff_coprime n d).2 h), one_mul]
  · rw [if_neg h, MulChar.map_nonunit _
      (fun hu => h ((ZMod.isUnit_iff_coprime n d).1 hu)), zero_mul]

theorem LSeriesSummable_conreyCoprimeMobiusCoeff {d : ℕ} {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (conreyCoprimeMobiusCoeff d) s :=
  DirichletCharacter.LSeriesSummable_mul (selbergPrincipalCharacter d)
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)

theorem LSeries_conreyCoprimeMobiusCoeff_eq {d : ℕ} [NeZero d] {s : ℂ}
    (hs : 1 < s.re) :
    L (conreyCoprimeMobiusCoeff d) s =
      (riemannZeta s * ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-s)))⁻¹ := by
  have hmul : L (↗(selbergPrincipalCharacter d) : ℕ → ℂ) s *
      L (conreyCoprimeMobiusCoeff d) s = 1 :=
    DirichletCharacter.LSeries.mul_mu_eq_one (selbergPrincipalCharacter d) hs
  have hinv : L (conreyCoprimeMobiusCoeff d) s =
      (L (↗(selbergPrincipalCharacter d) : ℕ → ℂ) s)⁻¹ :=
    (inv_eq_of_mul_eq_one_right hmul).symm
  rw [hinv, selbergPrincipalLSeries_eq_zeta_mul_eulerFactors hs]

noncomputable def conreyShiftedCoprimeMobiusCoeff (d : ℕ) (α : ℂ) (n : ℕ) : ℂ :=
  conreyCoprimeMobiusCoeff d n * (n : ℂ) ^ (-(1 + α))

theorem LSeries_term_conreyShiftedCoprimeMobiusCoeff (d : ℕ) (α w : ℂ) (n : ℕ) :
    LSeries.term (conreyShiftedCoprimeMobiusCoeff d α) w n =
      LSeries.term (conreyCoprimeMobiusCoeff d) (1 + α + w) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    unfold conreyShiftedCoprimeMobiusCoeff
    rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn), Complex.cpow_neg]
    field_simp [Complex.cpow_ne_zero_iff, Nat.cast_ne_zero.mpr hn]

theorem LSeriesSummable_conreyShiftedCoprimeMobiusCoeff {d : ℕ} {α w : ℂ}
    (h : 0 < α.re + w.re) :
    LSeriesSummable (conreyShiftedCoprimeMobiusCoeff d α) w := by
  have hs : 1 < (1 + α + w).re := by simp only [add_re, one_re]; linarith
  have horig := LSeriesSummable_conreyCoprimeMobiusCoeff (d := d) hs
  rw [LSeriesSummable] at horig ⊢
  exact horig.congr fun n => (LSeries_term_conreyShiftedCoprimeMobiusCoeff d α w n).symm

theorem LSeries_conreyShiftedCoprimeMobiusCoeff_eq {d : ℕ} [NeZero d] {α w : ℂ}
    (h : 0 < α.re + w.re) :
    L (conreyShiftedCoprimeMobiusCoeff d α) w =
      (riemannZeta (1 + α + w) *
        ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + w))))⁻¹ := by
  have heq : L (conreyShiftedCoprimeMobiusCoeff d α) w =
      L (conreyCoprimeMobiusCoeff d) (1 + α + w) :=
    tsum_congr (LSeries_term_conreyShiftedCoprimeMobiusCoeff d α w)
  rw [heq, LSeries_conreyCoprimeMobiusCoeff_eq]
  simp only [add_re, one_re]
  linarith

noncomputable def conreyCoprimeMobiusLogSum (d : ℕ) (α : ℂ) (X : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
    conreyShiftedCoprimeMobiusCoeff d α n * (Real.log (X / (n : ℝ)) : ℂ)

private theorem perronLogCutoff_real_div_eq_log {x X : ℝ}
    (hx : 0 < x) (hX : 0 < X) (hle : x ≤ X) :
    perronLogCutoff (x / X) = (Real.log (X / x) : ℂ) := by
  unfold perronLogCutoff
  rw [inv_div, Real.posLog_eq_log]
  rw [abs_of_pos (div_pos hX hx)]
  exact (one_le_div hx).2 hle

private theorem perronLogCutoff_real_div_eq_zero {x X : ℝ}
    (hx : 0 < x) (hX : 0 < X) (hle : X ≤ x) :
    perronLogCutoff (x / X) = 0 := by
  unfold perronLogCutoff
  norm_cast
  rw [Real.posLog_eq_zero_iff, inv_div, abs_of_pos (div_pos hX hx)]
  exact (div_le_one hx).2 hle

theorem tsum_conreyShiftedCoprimeMobiusCoeff_mul_cutoff_eq (d : ℕ) (α : ℂ)
    {X : ℝ} (hX : 0 < X) :
    (∑' n : ℕ, conreyShiftedCoprimeMobiusCoeff d α n * perronLogCutoff (n / X)) =
      conreyCoprimeMobiusLogSum d α X := by
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊X⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn1
    rw [perronLogCutoff_real_div_eq_log hnpos hX ((Nat.le_floor_iff hX.le).mp hnX)]
  · intro n hnout
    by_cases hn0 : n = 0
    · subst n
      simp [perronLogCutoff]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnX : ¬n ≤ ⌊X⌋₊ := fun hn => hnout (Finset.mem_Icc.mpr ⟨hn1, hn⟩)
      have hXn : X < (n : ℝ) := lt_of_not_ge (fun hn => hnX ((Nat.le_floor_iff hX.le).mpr hn))
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      rw [perronLogCutoff_real_div_eq_zero hnpos hX hXn.le, mul_zero]

/-- The literal Euler-factor integral is absolutely integrable and equals the
actual finite Möbius sum. This includes `alpha = 0` and integer cutoffs. -/
theorem conrey_coprime_mobius_log_perron {d : ℕ} [NeZero d] (α : ℂ) {X u : ℝ}
    (hX : 0 < X) (hu : 0 < u) (hα : 0 < α.re + u) :
    Integrable (fun t : ℝ =>
      (X : ℂ) ^ selbergPerronLine u t *
        (riemannZeta (1 + α + selbergPerronLine u t) *
          ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + selbergPerronLine u t))))⁻¹ *
        (1 / selbergPerronLine u t ^ 2)) ∧
    (1 / (2 * Real.pi) : ℂ) *
      (∫ t : ℝ, (X : ℂ) ^ selbergPerronLine u t *
        (riemannZeta (1 + α + selbergPerronLine u t) *
          ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + selbergPerronLine u t))))⁻¹ *
        (1 / selbergPerronLine u t ^ 2)) =
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        (if n.Coprime d then (ArithmeticFunction.moebius n : ℂ) else 0) *
          (n : ℂ) ^ (-(1 + α)) * (Real.log (X / (n : ℝ)) : ℂ) := by
  have hsum : LSeriesSummable (conreyShiftedCoprimeMobiusCoeff d α) (u : ℂ) :=
    LSeriesSummable_conreyShiftedCoprimeMobiusCoeff hα
  have hline (t : ℝ) :
      L (conreyShiftedCoprimeMobiusCoeff d α) (selbergPerronLine u t) =
        (riemannZeta (1 + α + selbergPerronLine u t) *
          ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + selbergPerronLine u t))))⁻¹ :=
    LSeries_conreyShiftedCoprimeMobiusCoeff_eq (by simpa [selbergPerronLine] using hα)
  constructor
  · have hi :=
      integrable_selbergPerronLSeriesIntegrand (conreyShiftedCoprimeMobiusCoeff d α) hX hu hsum
    change Integrable (fun t : ℝ => (X : ℂ) ^ selbergPerronLine u t *
      L (conreyShiftedCoprimeMobiusCoeff d α) (selbergPerronLine u t) *
        (1 / selbergPerronLine u t ^ 2)) at hi
    simpa only [hline] using hi
  · have h := normalized_integral_selbergPerronLSeries_eq
      (conreyShiftedCoprimeMobiusCoeff d α) hX hu hsum
    rw [tsum_conreyShiftedCoprimeMobiusCoeff_mul_cutoff_eq d α hX] at h
    simpa only [selbergPerronLSeriesIntegrand, hline, conreyCoprimeMobiusLogSum,
      conreyShiftedCoprimeMobiusCoeff, conreyCoprimeMobiusCoeff_eq] using h

end HardyTheorem
