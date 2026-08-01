import PrimeNumberTheorem.ZeroDensityLayerBudgetGoodHeightDesmoothedCentralContour
import PrimeNumberTheorem.ZeroDensityLayerBudgetCubicExplicitFormula

/-!
# Actual cubic contour budgets

The third-order contour is estimated before normalized second differences.
Consequently the horizontal edges retain all three powers of the contour
height in the denominator.
-/

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open Complex MeasureTheory Set
open scoped Interval

/-- Exact norm factorization of the actual third-order zeta integrand. -/
theorem norm_thirdOrderExplicitFormulaIntegrand_eq
    {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖thirdOrderExplicitFormulaIntegrand x s‖ =
      ‖logDeriv riemannZeta s‖ * x ^ s.re / ‖s‖ ^ 3 := by
  rw [thirdOrderExplicitFormulaIntegrand_eq_neg_logDeriv_kernel]
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    norm_div, norm_neg, norm_pow]
  rw [logDeriv_apply, norm_div]
  ring

/-- A pointwise cubic contour bound retaining the full reciprocal cube. -/
theorem norm_thirdOrderExplicitFormulaIntegrand_le
    {x L c T : ℝ} {s : ℂ}
    (hx : 1 ≤ x) (hL : 0 ≤ L) (hT : 0 < T)
    (hre : s.re ≤ c) (hnorm : T ≤ ‖s‖)
    (hlog : ‖logDeriv riemannZeta s‖ ≤ L) :
    ‖thirdOrderExplicitFormulaIntegrand x s‖ ≤
      L * x ^ c / T ^ 3 := by
  rw [norm_thirdOrderExplicitFormulaIntegrand_eq (zero_lt_one.trans_le hx)]
  have hxpow : x ^ s.re ≤ x ^ c :=
    Real.rpow_le_rpow_of_exponent_le hx hre
  calc
    ‖logDeriv riemannZeta s‖ * x ^ s.re / ‖s‖ ^ 3 ≤
        (L * x ^ c) / ‖s‖ ^ 3 := by
      gcongr
    _ ≤ (L * x ^ c) / T ^ 3 := by
      gcongr

/-- Integrating a common logarithmic-derivative bound along one horizontal
edge preserves the cubic `T^-3` denominator. -/
theorem norm_integral_thirdOrder_horizontal_le
    {x a c t T L : ℝ}
    (hx : 1 ≤ x) (hac : a ≤ c) (hT : 0 < T)
    (ht : |t| = T)
    (hlog : ∀ sigma ∈ Set.uIcc a c,
      ‖logDeriv riemannZeta ((sigma : ℂ) + I * t)‖ ≤ L)
    (hL : 0 ≤ L) :
    ‖∫ sigma in a..c,
        thirdOrderExplicitFormulaIntegrand x ((sigma : ℂ) + I * t)‖ ≤
      (L * x ^ c / T ^ 3) * |c - a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro sigma hsigma
  have hsigma' : sigma ∈ Set.uIcc a c :=
    Set.uIoc_subset_uIcc hsigma
  have hsigmaBounds : a ≤ sigma ∧ sigma ≤ c := by
    simpa [Set.uIcc_of_le hac] using hsigma'
  have hre : (((sigma : ℂ) + I * t).re : ℝ) ≤ c := by
    simpa using hsigmaBounds.2
  have him :
      |t| ≤ ‖(sigma : ℂ) + I * t‖ := by
    simpa using Complex.abs_im_le_norm ((sigma : ℂ) + I * t)
  have hnorm : T ≤ ‖(sigma : ℂ) + I * t‖ := by
    rw [← ht]
    exact him
  exact norm_thirdOrderExplicitFormulaIntegrand_le
    hx hL hT hre hnorm (hlog sigma hsigma')

/-- At one actual good height in every unit interval, both signs of the
horizontal cubic contour obey one uniform `T^-3` budget throughout
`-1 ≤ sigma ≤ 2`. -/
theorem exists_goodHeight_Icc_norm_integral_thirdOrder_horizontal_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A x a c : ℝ),
        4 ≤ A →
        1 ≤ x →
        -1 ≤ a →
        a ≤ c →
        c ≤ 2 →
        ∃ T ∈ Set.Icc A (A + 1),
          ExplicitFormulaAux.goodHeight T ∧
          ∀ t : ℝ, |t| = T →
            ‖∫ sigma in a..c,
                thirdOrderExplicitFormulaIntegrand
                  x ((sigma : ℂ) + I * t)‖ ≤
              (C * (1 + Real.log (A + 6)) ^ 2 * x ^ c / T ^ 3) *
                |c - a| := by
  rcases exists_goodHeight_Icc_norm_logDeriv_central_band_le_log_sq with
    ⟨C, hC, hgood⟩
  refine ⟨C, hC, ?_⟩
  intro A x a c hA hx ha hac hc
  rcases hgood A hA with ⟨T, hTmem, hTgood, hlog⟩
  refine ⟨T, hTmem, hTgood, ?_⟩
  intro t ht
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hA
  have hTpos : 0 < T := hApos.trans_le hTmem.1
  apply norm_integral_thirdOrder_horizontal_le hx hac hTpos ht
  · intro sigma hsigma
    have hsigmaBounds : a ≤ sigma ∧ sigma ≤ c := by
      simpa [Set.uIcc_of_le hac] using hsigma
    exact hlog t ht sigma (ha.trans hsigmaBounds.1)
      (hsigmaBounds.2.trans hc)
  · positivity

/-- Right-line truncation has a strictly negative target-normalized exponent
under the joint contour window. -/
theorem cubicRightTruncationExponent_lt_zero
    {beta alpha : ℝ} (hcontour : 1 - beta < alpha)
    (halpha : 0 < alpha) :
    1 - beta - 2 * alpha < 0 := by
  linarith

/-- The direct cubic horizontal contour has an additional height power and
therefore an even stronger strict exponent. -/
theorem cubicHorizontalContourExponent_lt_zero
    {beta alpha : ℝ} (hcontour : 1 - beta < alpha)
    (halpha : 0 < alpha) :
    1 - beta - 3 * alpha < 0 := by
  linarith

end ExplicitFormulaResidues
end PrimeNumberTheorem
