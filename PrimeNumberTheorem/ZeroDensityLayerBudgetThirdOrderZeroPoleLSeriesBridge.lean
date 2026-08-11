import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderZeroPoleContourIdentity
import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderLSeriesBridge

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction BigOperators LSeries.notation

namespace PrimeNumberTheorem

/-- Negative-left-edge third-order explicit formula for the genuine second
smoothed Chebyshev function, with the zero-pole correction retained explicitly. -/
theorem exists_thirdOrderZeroPoleExplicitFormula_secondSmoothedPsi_error_le
    {x a c W : ℝ} (hx : 0 < x) (ha : a < 0)
    (hc : 1 < c) (hW : 0 < W)
    (hboundary : ∀ p ∈ uIcc a c ×ℂ
        uIcc (-(2 * Real.pi * W)) (2 * Real.pi * W),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ) (cubic : ℂ),
      0 ∈ poles ∧
      (∀ p ∈ poles, a < p.re ∧ p.re < c ∧
        -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 0 then residue 0
        else if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      cubic = -deriv riemannZeta 0 / riemannZeta 0 ∧
      ‖(∑ p ∈ poles, residue p) -
          ExplicitFormulaResidues.thirdOrderContourRemainder x a c W -
          (secondSmoothedChebyshevPsi x : ℂ)‖ ≤
        ∑' n : ℕ,
          vonMangoldt n * (x / n) ^ c /
            (8 * Real.pi ^ 3 * W ^ 2) := by
  have hc0 : 0 < c := one_pos.trans hc
  obtain ⟨poles, residue, cubic, h0mem, hpoles, hpolesType,
      hresidue, hcubic, hcontour⟩ :=
    ExplicitFormulaResidues.exists_scaledRightIntegral_eq_zeroPoleResidue_sum_sub_thirdOrderContourRemainder
      hx ha hc0 hW hboundary
  refine ⟨poles, residue, cubic, h0mem, hpoles, hpolesType,
    hresidue, hcubic, ?_⟩
  have hright :
      (∫ w : ℝ in -W..W,
        ExplicitFormulaResidues.thirdOrderExplicitFormulaIntegrand x
          ((c : ℂ) + 2 * Real.pi * w * Complex.I)) =
      ∫ w : ℝ in -W..W,
        (x : ℂ) ^ perronLine c w *
          (-deriv riemannZeta (perronLine c w) /
            riemannZeta (perronLine c w)) /
              (perronLine c w) ^ 3 := by
    apply intervalIntegral.integral_congr
    intro w _hw
    simpa [perronLine] using
      thirdOrderExplicitFormulaIntegrand_eq_negLogDerivPerron x
        (perronLine c w)
  have herror :=
    norm_truncated_neg_logDeriv_riemannZeta_thirdOrder_sub_secondSmoothedPsi_le
      hx hc hW
  rw [← hright, hcontour] at herror
  exact herror

end PrimeNumberTheorem
