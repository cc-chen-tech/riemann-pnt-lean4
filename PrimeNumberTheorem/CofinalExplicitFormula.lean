import PrimeNumberTheorem.CentralHorizontalEdge
import PrimeNumberTheorem.FirstOrderExplicitFormula
import PrimeNumberTheorem.LeftHorizontalEdge
import PrimeNumberTheorem.NontrivialZeroMultiplicity

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open ExplicitFormulaAux

/-- On a good horizontal height, the first-order explicit-formula integrand is
interval integrable on every finite real interval. -/
theorem intervalIntegrable_explicitFormulaIntegrand_goodHeight_horizontal
    {x T t a b : ℝ} (hx : 0 < x) (hT : 0 < T) (ht : |t| = T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    IntervalIntegrable
      (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * t))
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro σ _hσ
  have htne : t ≠ 0 := by
    intro h
    subst t
    simp at ht
    linarith
  have hzeta := riemannZeta_ne_zero_on_goodHeight_horizontal
    (T := T) (t := t) (σ := σ) hT ht hgood
  have hs0 : (σ : ℂ) + I * t ≠ 0 := by
    intro hs
    apply htne
    have him := congrArg Complex.im hs
    simpa using him
  have hs1 : (σ : ℂ) + I * t ≠ 1 := by
    intro hs
    apply htne
    have him := congrArg Complex.im hs
    simpa using him
  have han : ContinuousAt (explicitFormulaIntegrand x) ((σ : ℂ) + I * t) :=
    (analyticAt_explicitFormulaIntegrand_of_ne_zero_of_ne_one_of_zeta_ne_zero
      hx hs0 hs1 hzeta).continuousAt
  have hmap : ContinuousAt (fun r : ℝ => ((r : ℂ) + I * t)) σ := by
    fun_prop
  change ContinuousWithinAt
    (explicitFormulaIntegrand x ∘ fun r : ℝ => ((r : ℂ) + I * t)) _ σ
  exact (ContinuousAt.comp
    (f := fun r : ℝ => ((r : ℂ) + I * t))
    (x := σ) (g := explicitFormulaIntegrand x) han hmap).continuousWithinAt

/-- Quantitative finite moving-rectangle remainder at one good height in each
unit interval.  The horizontal contribution is `O_x(log^2 A / A)` uniformly
in the left endpoint, while the displayed second term is the exponentially
small moving-left vertical contribution. -/
theorem
    exists_goodHeight_Icc_norm_firstOrderContourRemainder_le_horizontal_add_left
    {x : ℝ} (hx : 1 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1), ExplicitFormulaAux.goodHeight T ∧
        ∀ N : ℕ,
          ‖firstOrderContourRemainder x (-(2 * (N : ℝ) + 1)) 2
              (T / (2 * Real.pi))‖ ≤
            (C * (1 + Real.log (A + 6)) ^ 2 / T +
              ((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
                2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
                  Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
                x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
              (2 * Real.pi) := by
  rcases
      exists_goodHeight_Icc_norm_horizontal_complete_explicitFormulaContour_difference_le
        hx with ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hTmem, hgood, hhorizontal⟩
  have hTpos : 0 < T := by linarith [hTmem.1]
  refine ⟨T, hTmem, hgood, ?_⟩
  intro N
  let a : ℝ := -(2 * (N : ℝ) + 1)
  have ha : a ≤ -1 := by
    dsimp [a]
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hh := hhorizontal ha
  have hleft :=
    (norm_integral_explicitFormulaIntegrand_odd_vertical_le
      (N := N) hx hTpos.le).2
  have hscale : 2 * Real.pi * (T / (2 * Real.pi)) = T := by
    field_simp
  have hhorizontal' :
      ‖(∫ σ : ℝ in a..2,
            explicitFormulaIntegrand x
              ((σ : ℂ) + (((-T : ℝ) : ℂ) * I))) -
        (∫ σ : ℝ in a..2,
            explicitFormulaIntegrand x
              ((σ : ℂ) + (((T : ℝ) : ℂ) * I)))‖ ≤
        C * (1 + Real.log (A + 6)) ^ 2 / T := by
    simpa [mul_comm] using hh
  have hden : ‖(2 * Real.pi : ℂ) * I‖ = 2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  change ‖firstOrderContourRemainder x a 2 (T / (2 * Real.pi))‖ ≤ _
  rw [firstOrderContourRemainder, hscale, norm_div, hden]
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2 * Real.pi)
  calc
    ‖(∫ σ : ℝ in a..2,
          explicitFormulaIntegrand x
            ((σ : ℂ) + (((-T : ℝ) : ℂ) * I))) -
        (∫ σ : ℝ in a..2,
          explicitFormulaIntegrand x
            ((σ : ℂ) + (((T : ℝ) : ℂ) * I))) -
        I * (∫ t : ℝ in (-T)..T,
          explicitFormulaIntegrand x ((a : ℂ) + t * I))‖ ≤
      ‖(∫ σ : ℝ in a..2,
          explicitFormulaIntegrand x
            ((σ : ℂ) + (((-T : ℝ) : ℂ) * I))) -
        (∫ σ : ℝ in a..2,
          explicitFormulaIntegrand x
            ((σ : ℂ) + (((T : ℝ) : ℂ) * I)))‖ +
        ‖∫ t : ℝ in (-T)..T,
          explicitFormulaIntegrand x ((a : ℂ) + t * I)‖ := by
            calc
              _ ≤ ‖(∫ σ : ℝ in a..2,
                    explicitFormulaIntegrand x
                      ((σ : ℂ) + (((-T : ℝ) : ℂ) * I))) -
                  (∫ σ : ℝ in a..2,
                    explicitFormulaIntegrand x
                      ((σ : ℂ) + (((T : ℝ) : ℂ) * I)))‖ +
                  ‖I * (∫ t : ℝ in (-T)..T,
                    explicitFormulaIntegrand x ((a : ℂ) + t * I))‖ :=
                norm_sub_le _ _
              _ = _ := by rw [norm_mul, norm_I, one_mul]
    _ ≤ C * (1 + Real.log (A + 6)) ^ 2 / T +
        ((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
          2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
            Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
          x ^ (-(2 * (N : ℝ) + 1))) * (2 * T) := by
      apply add_le_add hhorizontal'
      simpa [a] using hleft

/-- Quantitative first-order truncated explicit formula at one good height in
every unit interval.  The abstract contour remainder has disappeared: the
first term combines Perron truncation with both horizontal edges, and the
second displayed term is the complete moving-left edge. -/
theorem
    exists_goodHeight_Icc_norm_truncatedExplicitFormula_sub_chebyshevPsi0_le_horizontal_add_left
    {x : ℝ} (hx : 1 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 8 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1), goodHeight T ∧ ∀ N : ℕ,
        ‖(∑ p ∈ finiteTrivialZeroSum (2 * (N : ℝ)), -((x : ℂ) ^ p) / p) +
            ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
              ∑ ρ ∈ nontrivialZerosFinset T,
                -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
            (chebyshevPsi0 x : ℂ)‖ ≤
          C * (1 + Real.log (A + 6)) ^ 2 / T +
            (((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
              2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
                Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
              x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
              (2 * Real.pi) := by
  rcases
      exists_norm_truncated_neg_logDeriv_firstOrderPerron_sub_chebyshevPsi0_le_div
        (zero_lt_one.trans hx) (by norm_num : (1 : ℝ) < 2) with
    ⟨Cp, hCp, hperron⟩
  rcases exists_goodHeight_Icc_norm_firstOrderContourRemainder_le_horizontal_add_left
      hx with ⟨Cr, hCr, hremainder⟩
  let C : ℝ := Cr + 2 * Real.pi * Cp
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hremainder A (by linarith) with ⟨T, hTmem, hgood, hrem⟩
  have hTpos : 0 < T := by linarith [hTmem.1]
  have htwoPi : 2 * Real.pi ≤ T := by
    nlinarith [Real.pi_lt_four, hTmem.1]
  have hW : 1 ≤ T / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity : 0 < 2 * Real.pi)]
    simpa using htwoPi
  have hscale : 2 * Real.pi * (T / (2 * Real.pi)) = T := by
    field_simp
  let L : ℝ := 1 + Real.log (A + 6)
  have hlog : 0 ≤ Real.log (A + 6) :=
    Real.log_nonneg (by linarith)
  have hLsq : 1 ≤ L ^ 2 := by
    have hL : 1 ≤ L := by dsimp [L]; linarith
    nlinarith [sq_nonneg (L - 1)]
  refine ⟨T, hTmem, hgood, ?_⟩
  intro N
  let approx : ℂ :=
    (∑ p ∈ finiteTrivialZeroSum (2 * (N : ℝ)), -((x : ℂ) ^ p) / p) +
      ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
        ∑ ρ ∈ nontrivialZerosFinset T,
          -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ)
  let rem : ℂ := firstOrderContourRemainder x (-(2 * (N : ℝ) + 1)) 2
    (T / (2 * Real.pi))
  let left : ℝ :=
    ((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
      2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
        Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
      x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)
  have hWpos : 0 < T / (2 * Real.pi) := by positivity
  have hgoodW : goodHeight (2 * Real.pi * (T / (2 * Real.pi))) := by
    simpa [hscale] using hgood
  have hidentity := movingLeft_scaledRightIntegral_eq_truncatedExplicitFormula
    (x := x) (c := 2) (W := T / (2 * Real.pi)) N
    (zero_lt_one.trans hx) (by norm_num) hWpos hgoodW
  have hintegral :
      (∫ w : ℝ in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)),
          explicitFormulaIntegrand x ((2 : ℂ) + 2 * Real.pi * w * I)) =
        ∫ w : ℝ in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)),
          (x : ℂ) ^ perronLine 2 w *
            (-deriv riemannZeta (perronLine 2 w) /
              riemannZeta (perronLine 2 w)) /
                perronLine 2 w := by
    apply intervalIntegral.integral_congr
    intro w _hw
    change explicitFormulaIntegrand x
        ((2 : ℂ) + 2 * Real.pi * w * I) =
      (x : ℂ) ^ perronLine 2 w *
        (-deriv riemannZeta (perronLine 2 w) /
          riemannZeta (perronLine 2 w)) /
            perronLine 2 w
    have hs : (2 : ℂ) + 2 * Real.pi * w * I = perronLine 2 w := by
      simp only [perronLine]
      push_cast
      ring
    rw [hs]
    simp only [explicitFormulaIntegrand, perronLine, logDeriv_apply]
    ring
  have hpBound0 := hperron (T / (2 * Real.pi)) hW
  have hrightEq :
      (∫ w : ℝ in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)),
          (x : ℂ) ^ perronLine 2 w *
            (-deriv riemannZeta (perronLine 2 w) /
              riemannZeta (perronLine 2 w)) /
                perronLine 2 w) = approx - rem := by
    calc
      _ = ∫ w : ℝ in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)),
          explicitFormulaIntegrand x ((2 : ℂ) + 2 * Real.pi * w * I) :=
        hintegral.symm
      _ = (∑ p ∈ finiteTrivialZeroSum (2 * (N : ℝ)), -((x : ℂ) ^ p) / p) +
          ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
            ∑ ρ ∈ nontrivialZerosFinset (2 * Real.pi * (T / (2 * Real.pi))),
              -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
          firstOrderContourRemainder x (-(2 * (N : ℝ) + 1)) 2
            (T / (2 * Real.pi)) := hidentity
      _ = approx - rem := by simp [approx, rem, hscale]
  have hpBound' : ‖(approx - rem) - (chebyshevPsi0 x : ℂ)‖ ≤ Cp /
      (T / (2 * Real.pi)) := by
    rw [hrightEq] at hpBound0
    exact hpBound0
  have hrem := hrem N
  have hrem' : ‖rem‖ ≤ Cr * L ^ 2 / T + left / (2 * Real.pi) := by
    have hbase : ‖rem‖ ≤ (Cr * L ^ 2 / T + left) / (2 * Real.pi) := by
      simpa [rem, left, L] using hrem
    apply hbase.trans
    rw [add_div]
    have hhoriz : 0 ≤ Cr * L ^ 2 / T := by positivity
    have hfirst := div_le_self hhoriz (by nlinarith [Real.pi_gt_three] :
      1 ≤ 2 * Real.pi)
    linarith
  change ‖approx - (chebyshevPsi0 x : ℂ)‖ ≤ _
  have hsplit :
      approx - (chebyshevPsi0 x : ℂ) =
        ((approx - rem) - (chebyshevPsi0 x : ℂ)) + rem := by ring
  rw [hsplit]
  calc
    _ ≤ ‖(approx - rem) - (chebyshevPsi0 x : ℂ)‖ + ‖rem‖ := norm_add_le _ _
    _ ≤ Cp / (T / (2 * Real.pi)) +
        (Cr * L ^ 2 / T + left / (2 * Real.pi)) :=
      add_le_add hpBound' hrem'
    _ ≤ C * L ^ 2 / T +
        (((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
          2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
            Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
          x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
          (2 * Real.pi) := by
      have hpRate : Cp / (T / (2 * Real.pi)) ≤
          (2 * Real.pi * Cp) * L ^ 2 / T := by
        have heq : Cp / (T / (2 * Real.pi)) = (2 * Real.pi * Cp) / T := by
          field_simp [hTpos.ne']
        rw [heq]
        apply div_le_div_of_nonneg_right _ hTpos.le
        nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) hCp)
          (sub_nonneg.mpr hLsq)]
      calc
        Cp / (T / (2 * Real.pi)) +
            (Cr * L ^ 2 / T + left / (2 * Real.pi)) ≤
          (2 * Real.pi * Cp) * L ^ 2 / T +
            (Cr * L ^ 2 / T + left / (2 * Real.pi)) :=
          by
            simpa [add_comm] using
              add_le_add_right hpRate (Cr * L ^ 2 / T + left / (2 * Real.pi))
        _ = C * L ^ 2 / T + left / (2 * Real.pi) := by
          dsimp [C]
          ring
    _ = C * (1 + Real.log (A + 6)) ^ 2 / T +
        (((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
          2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
            Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
          x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
          (2 * Real.pi) := by rfl

/-- At one good height in every unit interval, the left truncation depth can
be chosen so that the complete finite explicit-formula error is
`O_x(log^2 A / T)`.  In contrast with the preceding theorem, no moving-left
contour term remains in the conclusion. -/
theorem
    exists_goodHeight_Icc_exists_truncation_norm_truncatedExplicitFormula_sub_chebyshevPsi0_le_log_sq_div
    {x : ℝ} (hx : 1 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 8 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1), goodHeight T ∧ ∃ N : ℕ,
        ‖(∑ p ∈ finiteTrivialZeroSum (2 * (N : ℝ)), -((x : ℂ) ^ p) / p) +
            ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
              ∑ ρ ∈ nontrivialZerosFinset T,
                -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
            (chebyshevPsi0 x : ℂ)‖ ≤
          C * (1 + Real.log (A + 6)) ^ 2 / T := by
  rcases
      exists_goodHeight_Icc_norm_truncatedExplicitFormula_sub_chebyshevPsi0_le_horizontal_add_left
        hx with ⟨C, hC, hselect⟩
  refine ⟨C + 1, by positivity, ?_⟩
  intro A hA
  rcases hselect A hA with ⟨T, hTmem, hgood, hbound⟩
  have hTpos : 0 < T := by linarith [hTmem.1]
  let L : ℝ := 1 + Real.log (A + 6)
  have hlog : 0 ≤ Real.log (A + 6) :=
    Real.log_nonneg (by linarith)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have heps : 0 < L ^ 2 / T := div_pos (sq_pos_of_pos hLpos) hTpos
  have hleft := tendsto_oddVerticalExplicitBound_atTop hx hTpos.le
  rcases (Metric.tendsto_atTop.mp hleft) (L ^ 2 / T) heps with ⟨N, hN⟩
  have hleftN := hN N le_rfl
  have hleftNonneg :
      0 ≤ (((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
        2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
          Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
        x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
        (2 * Real.pi) := by
    have hseries : 0 ≤ vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    have hlogN : 0 ≤ Real.log (2 * (N : ℝ) + T + 4) :=
      Real.log_nonneg (by
        have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith)
    positivity
  have hleftRate :
      (((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
        2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
          Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
        x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
        (2 * Real.pi) ≤ L ^ 2 / T := by
    change dist
      ((((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
        2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
          Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
        x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
        (2 * Real.pi)) 0 < L ^ 2 / T at hleftN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hleftNonneg] at hleftN
    exact hleftN.le
  refine ⟨T, hTmem, hgood, N, ?_⟩
  apply (hbound N).trans
  change C * L ^ 2 / T +
      (((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
        2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
          Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
        x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
        (2 * Real.pi) ≤ (C + 1) * L ^ 2 / T
  calc
    _ ≤ C * L ^ 2 / T + L ^ 2 / T := add_le_add_right hleftRate _
    _ = (C + 1) * L ^ 2 / T := by ring

/-- At a good height in every unit interval, the standard
multiplicity-aware explicit-formula approximation has quantitative
`O_x(log^2 A / T)` error.  Both the moving-left edge and the finite
trivial-zero truncation have been removed from the statement. -/
theorem
    exists_goodHeight_Icc_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_log_sq_div
    {x : ℝ} (hx : 1 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 8 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1), goodHeight T ∧
        ‖explicitFormulaApproxWithMultiplicity x T -
            (chebyshevPsi0 x : ℂ)‖ ≤
          C * (1 + Real.log (A + 6)) ^ 2 / T := by
  rcases
      exists_goodHeight_Icc_norm_truncatedExplicitFormula_sub_chebyshevPsi0_le_horizontal_add_left
        hx with ⟨C, hC, hselect⟩
  refine ⟨C + 2, by positivity, ?_⟩
  intro A hA
  rcases hselect A hA with ⟨T, hTmem, hgood, hbound⟩
  have hTpos : 0 < T := by linarith [hTmem.1]
  let L : ℝ := 1 + Real.log (A + 6)
  have hlog : 0 ≤ Real.log (A + 6) :=
    Real.log_nonneg (by linarith)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have heps : 0 < L ^ 2 / T := div_pos (sq_pos_of_pos hLpos) hTpos
  have hleft := tendsto_oddVerticalExplicitBound_atTop hx hTpos.le
  rcases (Metric.tendsto_atTop.mp hleft) (L ^ 2 / T) heps with
    ⟨Nleft, hNleft⟩
  have htrivial := ExplicitFormulaAux.tendsto_finiteTrivialZeroSum_residues hx
  rcases (Metric.tendsto_atTop.mp htrivial) (L ^ 2 / T) heps with
    ⟨Ntrivial, hNtrivial⟩
  let N : ℕ := max Nleft Ntrivial
  let finite : ℂ :=
    ∑ p ∈ finiteTrivialZeroSum (2 * (N : ℝ)), -((x : ℂ) ^ p) / p
  let zeroSum : ℂ :=
    ∑ ρ ∈ nontrivialZerosFinset T,
      -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  let mainTerm : ℂ :=
    (x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 + zeroSum
  let logTerm : ℂ :=
    ((-(1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)
  let left : ℝ :=
    (((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
      2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
        Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
      x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
      (2 * Real.pi)
  have hleftDist := hNleft N (le_max_left _ _)
  have hleftNonneg : 0 ≤ left := by
    have hseries : 0 ≤ vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    have hlogN : 0 ≤ Real.log (2 * (N : ℝ) + T + 4) :=
      Real.log_nonneg (by
        have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith)
    dsimp [left]
    positivity
  have hleftRate : left ≤ L ^ 2 / T := by
    change dist left 0 < L ^ 2 / T at hleftDist
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hleftNonneg] at hleftDist
    exact hleftDist.le
  have htrivialDist := hNtrivial N (le_max_right _ _)
  have htrivialRate : ‖logTerm - finite‖ ≤ L ^ 2 / T := by
    have hforward : ‖finite - logTerm‖ < L ^ 2 / T := by
      change dist finite logTerm < L ^ 2 / T at htrivialDist
      simpa [dist_eq_norm] using htrivialDist
    rw [norm_sub_rev]
    exact hforward.le
  have hfinite :
      ‖finite + mainTerm - (chebyshevPsi0 x : ℂ)‖ ≤
        C * L ^ 2 / T + left := by
    simpa [finite, mainTerm, zeroSum, left, L] using hbound N
  have hzeroSum :
      zeroSum = -finiteNontrivialZeroSumWithMultiplicity x T := by
    dsimp [zeroSum, finiteNontrivialZeroSumWithMultiplicity]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ρ _hρ
    ring
  have happ :
      explicitFormulaApproxWithMultiplicity x T = mainTerm + logTerm := by
    dsimp [explicitFormulaApproxWithMultiplicity, mainTerm, logTerm]
    rw [hzeroSum]
    push_cast
    ring
  refine ⟨T, hTmem, hgood, ?_⟩
  have hsplit :
      explicitFormulaApproxWithMultiplicity x T - (chebyshevPsi0 x : ℂ) =
        (finite + mainTerm - (chebyshevPsi0 x : ℂ)) +
          (logTerm - finite) := by
    rw [happ]
    ring
  rw [hsplit]
  calc
    _ ≤ ‖finite + mainTerm - (chebyshevPsi0 x : ℂ)‖ +
        ‖logTerm - finite‖ := norm_add_le _ _
    _ ≤ (C * L ^ 2 / T + left) + L ^ 2 / T :=
      add_le_add hfinite htrivialRate
    _ ≤ (C * L ^ 2 / T + L ^ 2 / T) + L ^ 2 / T := by
      gcongr
    _ = (C + 2) * L ^ 2 / T := by ring

/-- A single cofinal family closes the moving-rectangle assembly gap.  Along
strictly increasing good heights, the complete first-order contour remainder
vanishes and the multiplicity-weighted nontrivial-zero sums converge to the
classical `psi0` explicit-formula value. -/
theorem exists_cofinal_nontrivialZeroSum_tendsto
    {x : ℝ} (hx : 1 < x) :
    ∃ T : ℕ → ℝ, StrictMono T ∧ Tendsto T atTop atTop ∧
      (∀ n : ℕ,
        T n ∈ Set.Icc (2 * (n : ℝ) + 4) (2 * (n : ℝ) + 5) ∧
          0 < T n ∧ ExplicitFormulaAux.goodHeight (T n)) ∧
      (∀ n,
        (∫ w : ℝ in (-(T n / (2 * Real.pi)))..(T n / (2 * Real.pi)),
            explicitFormulaIntegrand x ((2 : ℂ) + 2 * Real.pi * w * I)) =
          (∑ p ∈ finiteTrivialZeroSum (2 * ((2 * n : ℕ) : ℝ)),
              -((x : ℂ) ^ p) / p) +
            ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
              ∑ ρ ∈ nontrivialZerosFinset (T n),
                -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
              firstOrderContourRemainder x
                (-(2 * ((2 * n : ℕ) : ℝ) + 1)) 2
                (T n / (2 * Real.pi))) ∧
      Tendsto
        (fun n : ℕ => firstOrderContourRemainder x
          (-(2 * ((2 * n : ℕ) : ℝ) + 1)) 2
          (T n / (2 * Real.pi)))
        atTop (nhds 0) ∧
      Tendsto
        (fun n : ℕ =>
          ∑ ρ ∈ nontrivialZerosFinset (T n),
            -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ)
        atTop
        (nhds ((chebyshevPsi0 x : ℂ) -
          (((-(1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)) -
          ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0))) := by
  classical
  rcases exists_tendsto_horizontal_central_explicitFormulaIntegrand_both_zero
      (show 1 ≤ x from hx.le) with
    ⟨T0, hT0spec, hT0top, hcentralTop0, hcentralBottom0⟩
  let e : ℕ → ℕ := fun n => 2 * n
  have hetop : Tendsto e atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    dsimp [e]
    omega
  let T : ℕ → ℝ := fun n => T0 (e n)
  have hTspec (n : ℕ) :
      T n ∈ Set.Icc (((e n : ℕ) : ℝ) + 4) (((e n : ℕ) : ℝ) + 5) ∧
        ExplicitFormulaAux.goodHeight (T n) := by
    exact ⟨(hT0spec (e n)).1, (hT0spec (e n)).2.1⟩
  have hTmono : StrictMono T := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hu := (hTspec n).1.2
    have hl := (hTspec (n + 1)).1.1
    dsimp [e] at hu hl
    norm_num [Nat.cast_add, Nat.cast_mul] at hu hl ⊢
    linarith
  have hTtop : Tendsto T atTop atTop := hT0top.comp hetop
  have hTpos (n : ℕ) : 0 < T n := by
    linarith [(hTspec n).1.1]
  have hcentralTop : Tendsto
      (fun n : ℕ => ∫ σ : ℝ in (-1)..2,
        explicitFormulaIntegrand x ((σ : ℂ) + I * T n))
      atTop (nhds 0) := by
    simpa [T] using hcentralTop0.comp hetop
  have hcentralBottom : Tendsto
      (fun n : ℕ => ∫ σ : ℝ in (-1)..2,
        explicitFormulaIntegrand x ((σ : ℂ) - I * T n))
      atTop (nhds 0) := by
    simpa [T] using hcentralBottom0.comp hetop
  let A : ℕ → ℝ := fun n => -(2 * ((e n : ℕ) : ℝ) + 1)
  let a : ℝ → ℝ := fun t => A (Function.invFun T t)
  have ha_eval (n : ℕ) : a (T n) = A n := by
    dsimp [a]
    rw [Function.leftInverse_invFun hTmono.injective]
  have ha : ∀ᶠ t : ℝ in atTop, a t ≤ -1 := by
    filter_upwards [] with t
    dsimp [a, A, e]
    have hn : 0 ≤ ((2 * Function.invFun T t : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hfarTop0 := tendsto_integral_farLeft_explicit_atTop
    (x := x) (ε := 1) hx one_pos a ha
  have hfarBottom0 := tendsto_integral_farLeft_explicit_neg_height_atTop
    (x := x) (ε := 1) hx one_pos a ha
  have hfarTop : Tendsto
      (fun n : ℕ => ∫ σ : ℝ in A n..(-1),
        explicitFormulaIntegrand x ((σ : ℂ) + I * T n))
      atTop (nhds 0) := by
    apply (hfarTop0.comp hTtop).congr'
    filter_upwards [] with n
    simp only [Function.comp_apply]
    rw [ha_eval]
    apply intervalIntegral.integral_congr
    intro σ _hσ
    rw [mul_comm (T n : ℂ) I]
  have hfarBottom : Tendsto
      (fun n : ℕ => ∫ σ : ℝ in A n..(-1),
        explicitFormulaIntegrand x ((σ : ℂ) - I * T n))
      atTop (nhds 0) := by
    apply (hfarBottom0.comp hTtop).congr'
    filter_upwards [] with n
    simp only [Function.comp_apply]
    rw [ha_eval]
    apply intervalIntegral.integral_congr
    intro σ _hσ
    rw [mul_comm (T n : ℂ) I]
  have hhorizontalTop : Tendsto
      (fun n : ℕ => ∫ σ : ℝ in A n..2,
        explicitFormulaIntegrand x ((σ : ℂ) + I * T n))
      atTop (nhds 0) := by
    simpa only [add_zero] using (hfarTop.add hcentralTop).congr' (by
      filter_upwards [] with n
      have hfarInt :=
        intervalIntegrable_explicitFormulaIntegrand_goodHeight_horizontal
          (x := x) (T := T n) (t := T n) (a := A n) (b := -1)
          (zero_lt_one.trans hx) (hTpos n) (abs_of_pos (hTpos n)) (hTspec n).2
      have hcentralInt :=
        intervalIntegrable_explicitFormulaIntegrand_goodHeight_horizontal
          (x := x) (T := T n) (t := T n) (a := -1) (b := 2)
          (zero_lt_one.trans hx) (hTpos n) (abs_of_pos (hTpos n)) (hTspec n).2
      exact intervalIntegral.integral_add_adjacent_intervals hfarInt hcentralInt)
  have hhorizontalBottom : Tendsto
      (fun n : ℕ => ∫ σ : ℝ in A n..2,
        explicitFormulaIntegrand x ((σ : ℂ) - I * T n))
      atTop (nhds 0) := by
    simpa only [add_zero] using (hfarBottom.add hcentralBottom).congr' (by
      filter_upwards [] with n
      have ht_abs : |-T n| = T n := by rw [abs_neg, abs_of_pos (hTpos n)]
      have hfarInt :=
        intervalIntegrable_explicitFormulaIntegrand_goodHeight_horizontal
          (x := x) (T := T n) (t := -T n) (a := A n) (b := -1)
          (zero_lt_one.trans hx) (hTpos n) ht_abs (hTspec n).2
      have hcentralInt :=
        intervalIntegrable_explicitFormulaIntegrand_goodHeight_horizontal
          (x := x) (T := T n) (t := -T n) (a := -1) (b := 2)
          (zero_lt_one.trans hx) (hTpos n) ht_abs (hTspec n).2
      simpa [sub_eq_add_neg] using
        intervalIntegral.integral_add_adjacent_intervals hfarInt hcentralInt)
  have hT0nonneg (m : ℕ) : 0 ≤ T0 m := by
    linarith [(hT0spec m).1.1]
  have hT0upper (m : ℕ) : T0 m ≤ (m : ℝ) + 4 + 1 := by
    linarith [(hT0spec m).1.2]
  have hleft0 := tendsto_integral_explicitFormulaIntegrand_odd_vertical_atTop
    (x := x) (K := 4) (T := T0) hx hT0nonneg hT0upper
  have hleft : Tendsto
      (fun n : ℕ => ∫ t : ℝ in (-(T n))..(T n),
        explicitFormulaIntegrand x ((A n : ℂ) + (t : ℂ) * I))
      atTop (nhds 0) := by
    apply (hleft0.comp hetop).congr'
    filter_upwards [] with n
    simp only [Function.comp_apply]
    dsimp [T, A, e]
  have hnum := (hhorizontalBottom.sub hhorizontalTop).sub (hleft.const_mul I)
  have hden : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hremainder : Tendsto
      (fun n : ℕ => firstOrderContourRemainder x (A n) 2
        (T n / (2 * Real.pi)))
      atTop (nhds 0) := by
    have hdiv := hnum.div_const (2 * Real.pi * I)
    simpa only [sub_zero, mul_zero, zero_div] using hdiv.congr' (by
      filter_upwards [] with n
      have hscale : 2 * Real.pi * (T n / (2 * Real.pi)) = T n := by
        field_simp
      simp only [firstOrderContourRemainder, hscale]
      have hbottomEq :
          (∫ σ : ℝ in A n..2,
              explicitFormulaIntegrand x ((σ : ℂ) - I * T n)) =
            ∫ σ : ℝ in A n..2,
              explicitFormulaIntegrand x
                ((σ : ℂ) + (((-T n : ℝ) : ℂ) * I)) := by
        apply intervalIntegral.integral_congr
        intro σ _hσ
        apply congrArg (explicitFormulaIntegrand x)
        push_cast
        ring
      have htopEq :
          (∫ σ : ℝ in A n..2,
              explicitFormulaIntegrand x ((σ : ℂ) + I * T n)) =
            ∫ σ : ℝ in A n..2,
              explicitFormulaIntegrand x
                ((σ : ℂ) + (((T n : ℝ) : ℂ) * I)) := by
        apply intervalIntegral.integral_congr
        intro σ _hσ
        apply congrArg (explicitFormulaIntegrand x)
        ring
      rw [hbottomEq, htopEq])
  have hWpos (n : ℕ) : 0 < T n / (2 * Real.pi) :=
    div_pos (hTpos n) (by positivity)
  have hformula (n : ℕ) :=
    movingLeft_scaledRightIntegral_eq_truncatedExplicitFormula
      (x := x) (c := 2) (W := T n / (2 * Real.pi)) (2 * n)
      (zero_lt_one.trans hx) (by norm_num) (hWpos n) (by
        have hscale : 2 * Real.pi * (T n / (2 * Real.pi)) = T n := by
          field_simp
        simpa [hscale] using (hTspec n).2)
  have hformula' (n : ℕ) :
      (∫ w : ℝ in (-(T n / (2 * Real.pi)))..(T n / (2 * Real.pi)),
          explicitFormulaIntegrand x ((2 : ℂ) + 2 * Real.pi * w * I)) =
        (∑ p ∈ finiteTrivialZeroSum (2 * ((2 * n : ℕ) : ℝ)),
            -((x : ℂ) ^ p) / p) +
          ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
            ∑ ρ ∈ nontrivialZerosFinset (T n),
              -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
            firstOrderContourRemainder x (A n) 2
              (T n / (2 * Real.pi)) := by
    have hscale : 2 * Real.pi * (T n / (2 * Real.pi)) = T n := by
      field_simp
    simpa [A, e, hscale] using hformula n
  have hWtop : Tendsto (fun n => T n / (2 * Real.pi)) atTop atTop :=
    hTtop.atTop_div_const (by positivity)
  have hright :=
    (tendsto_scaledRightIntegral_explicitFormulaIntegrand_atTop
      (x := x) (c := 2) (zero_lt_one.trans hx) (by norm_num)).comp hWtop
  have htrivial0 := ExplicitFormulaAux.tendsto_finiteTrivialZeroSum_residues hx
  have htrivial := htrivial0.comp hetop
  let mainTerm : ℂ := (x : ℂ) - deriv riemannZeta 0 / riemannZeta 0
  have hzeroSum := ((hright.sub htrivial).sub
    (tendsto_const_nhds : Tendsto (fun _n : ℕ => mainTerm) atTop (nhds mainTerm))).add
      hremainder
  refine ⟨T, hTmono, hTtop, (fun n => ?_), ?_, ?_, ?_⟩
  · have hIcc : T n ∈ Set.Icc (2 * (n : ℝ) + 4) (2 * (n : ℝ) + 5) := by
      simpa [e, Nat.cast_mul] using (hTspec n).1
    exact ⟨hIcc, hTpos n, (hTspec n).2⟩
  · intro n
    simpa [A, e] using hformula' n
  · simpa [A, e] using hremainder
  · simpa only [sub_eq_add_neg, add_zero] using hzeroSum.congr' (by
      filter_upwards [] with n
      have heq := hformula' n
      dsimp [mainTerm]
      linear_combination heq)

/-- The complete cofinal contour theorem, expressed directly through the
multiplicity-aware approximation used by the final explicit-formula target.

This is deliberately a sequential cofinal result.  It does not claim the
full real-height `atTop` limit; that still requires control of the weighted
zero contributions between consecutive selected heights. -/
theorem exists_cofinal_explicitFormulaApproxWithMultiplicity_tendsto
    {x : ℝ} (hx : 1 < x) :
    ∃ T : ℕ → ℝ, StrictMono T ∧ Tendsto T atTop atTop ∧
      (∀ n : ℕ,
        T n ∈ Set.Icc (2 * (n : ℝ) + 4) (2 * (n : ℝ) + 5) ∧
          ExplicitFormulaAux.goodHeight (T n)) ∧
      Tendsto
        (fun n : ℕ => explicitFormulaApproxWithMultiplicity x (T n))
        atTop (nhds (chebyshevPsi0 x : ℂ)) := by
  rcases exists_cofinal_nontrivialZeroSum_tendsto hx with
    ⟨T, hTmono, hTtop, hTspec, _hformula, _hremainder, hzeroSum⟩
  refine ⟨T, hTmono, hTtop, (fun n => ⟨(hTspec n).1, (hTspec n).2.2⟩), ?_⟩
  let mainTerm : ℂ := (x : ℂ) - deriv riemannZeta 0 / riemannZeta 0
  let trivialTerm : ℂ :=
    (((-(1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))
  have hsum := ((tendsto_const_nhds : Tendsto
      (fun _n : ℕ => mainTerm) atTop (nhds mainTerm)).add hzeroSum).add
    (tendsto_const_nhds : Tendsto
      (fun _n : ℕ => trivialTerm) atTop (nhds trivialTerm))
  have hlim :
      mainTerm +
          ((chebyshevPsi0 x : ℂ) -
            (((-(1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)) -
            ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0)) +
        trivialTerm = (chebyshevPsi0 x : ℂ) := by
    dsimp [mainTerm, trivialTerm]
    ring
  rw [hlim] at hsum
  apply hsum.congr'
  filter_upwards [] with n
  dsimp [mainTerm, trivialTerm, explicitFormulaApproxWithMultiplicity,
    finiteNontrivialZeroSumWithMultiplicity]
  push_cast
  have hneg :
      (∑ ρ ∈ nontrivialZerosFinset (T n),
          -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) =
        -(∑ ρ ∈ nontrivialZerosFinset (T n),
          (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ρ _hρ
    ring
  rw [hneg]
  ring

end ExplicitFormulaResidues
end PrimeNumberTheorem
