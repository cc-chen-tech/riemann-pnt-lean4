import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderLSeriesBridge

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction BigOperators LSeries.notation

namespace PrimeNumberTheorem

example {x c W : ℝ} (hx : 0 < x) (hc : 1 < c) :
    (∫ w : ℝ in (-W)..W,
      (x : ℂ) ^ perronLine c w *
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (perronLine c w) /
          (perronLine c w) ^ 3) =
      ∑' n : ℕ, ∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              (perronLine c w) ^ 3 :=
  intervalIntegral_vonMangoldt_LSeries_thirdOrder_eq_tsum hx hc

example {x c W : ℝ} (hx : 0 < x) (hc : 1 < c) :
    (∫ w : ℝ in (-W)..W,
      (x : ℂ) ^ perronLine c w *
        (-deriv riemannZeta (perronLine c w) /
          riemannZeta (perronLine c w)) /
            (perronLine c w) ^ 3) =
      ∑' n : ℕ, ∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              (perronLine c w) ^ 3 :=
  intervalIntegral_neg_logDeriv_riemannZeta_thirdOrder_eq_vonMangoldt_tsum hx hc

example {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) (c w : ℝ) :
    (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              (perronLine c w) ^ 3 =
      (vonMangoldt n : ℂ) *
        (Complex.exp (perronLine c w * Real.log (x / n)) /
          (perronLine c w) ^ 3) :=
  thirdOrderPerronTerm_eq_kernel hx hn c w

example {x c W : ℝ} (hx : 0 < x) (hc : 0 < c) (hW : 0 < W) (n : ℕ) :
    ‖(∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (perronLine c w) n /
              (perronLine c w) ^ 3) -
        (vonMangoldt n : ℂ) *
          ((((max (Real.log (x / n)) 0) ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      vonMangoldt n * (x / n) ^ c /
        (8 * Real.pi ^ 3 * W ^ 2) :=
  norm_intervalIntegral_thirdOrderPerronTerm_sub_sq_le hx hc hW n

example {x c W : ℝ} (hx : 0 < x) (hc : 1 < c) (hW : 0 < W) :
    ‖(∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          (-deriv riemannZeta (perronLine c w) /
            riemannZeta (perronLine c w)) /
              (perronLine c w) ^ 3) -
        (secondSmoothedChebyshevPsi x : ℂ)‖ ≤
      ∑' n : ℕ,
        vonMangoldt n * (x / n) ^ c /
          (8 * Real.pi ^ 3 * W ^ 2) :=
  norm_truncated_neg_logDeriv_riemannZeta_thirdOrder_sub_secondSmoothedPsi_le
    hx hc hW

example (x : ℝ) (s : ℂ) :
    ExplicitFormulaResidues.thirdOrderExplicitFormulaIntegrand x s =
      (x : ℂ) ^ s *
        (-deriv riemannZeta s / riemannZeta s) / s ^ 3 :=
  thirdOrderExplicitFormulaIntegrand_eq_negLogDerivPerron x s

example {x a c W : ℝ} (hx : 0 < x) (ha : 0 < a) (hac : a < c)
    (hc : 1 < c) (hW : 0 < W)
    (hboundary : ∀ p ∈ uIcc a c ×ℂ
        uIcc (-(2 * Real.pi * W)) (2 * Real.pi * W),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles, a < p.re ∧ p.re < c ∧
        -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      ‖(∑ p ∈ poles, residue p) -
          ExplicitFormulaResidues.thirdOrderContourRemainder x a c W -
          (secondSmoothedChebyshevPsi x : ℂ)‖ ≤
        ∑' n : ℕ,
          vonMangoldt n * (x / n) ^ c /
            (8 * Real.pi ^ 3 * W ^ 2) :=
  exists_thirdOrderExplicitFormula_secondSmoothedPsi_error_le
    hx ha hac hc hW hboundary

end PrimeNumberTheorem
