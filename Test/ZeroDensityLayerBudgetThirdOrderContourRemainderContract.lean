import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderContourRemainder

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction BigOperators LSeries.notation

namespace PrimeNumberTheorem.ExplicitFormulaResidues

example (x : ℝ) (N : ℕ) (T : ℝ) :
    thirdOrderOddVerticalBound x N T =
      secondOrderOddVerticalBound x N T / (2 * (N : ℝ) + 1) := rfl

example {x σ b t K : ℝ} (hx : 1 ≤ x) (hσ : σ ≤ b) (ht : 0 < |t|)
    (hK : 0 ≤ K)
    (hlog : ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ K) :
    ‖thirdOrderExplicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
      K * x ^ b / |t| ^ 3 :=
  norm_thirdOrderExplicitFormulaIntegrand_horizontal_le_of_logDeriv_le_of_re_le
    hx hσ ht hK hlog

example {x T t : ℝ} {N : ℕ} (hx : 1 < x) (hT : 0 ≤ T)
    (ht : |t| ≤ T) :
    ‖thirdOrderExplicitFormulaIntegrand x
      (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      thirdOrderOddVerticalBound x N T :=
  norm_thirdOrderExplicitFormulaIntegrand_odd_vertical_le hx hT ht

example {x a c b t K : ℝ} (hx : 1 ≤ x) (hac : a ≤ c) (hc : c ≤ b)
    (ht : 0 < |t|) (hK : 0 ≤ K)
    (hlog : ∀ σ ∈ Set.uIoc a c,
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ K) :
    ‖∫ σ : ℝ in a..c,
        thirdOrderExplicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
      (K * x ^ b / |t| ^ 3) * (c - a) :=
  norm_integral_thirdOrderHorizontal_le_of_logDeriv
    hx hac hc ht hK hlog

example {x T : ℝ} {N : ℕ} (hx : 1 < x) (hT : 0 ≤ T) :
    ‖∫ t : ℝ in (-T)..T,
        thirdOrderExplicitFormulaIntegrand x
          (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      thirdOrderOddVerticalBound x N T * (2 * T) :=
  norm_integral_thirdOrderOddVertical_le hx hT

example (x a c W : ℝ) :
    ‖thirdOrderContourRemainder x a c W‖ ≤
      (‖∫ σ : ℝ in a..c,
          thirdOrderExplicitFormulaIntegrand x
            ((σ : ℂ) + (-(2 * Real.pi * W) : ℝ) * I)‖ +
        ‖∫ σ : ℝ in a..c,
          thirdOrderExplicitFormulaIntegrand x
            ((σ : ℂ) + (2 * Real.pi * W : ℝ) * I)‖ +
        ‖∫ t : ℝ in -(2 * Real.pi * W)..2 * Real.pi * W,
          thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)‖) /
        (2 * Real.pi) :=
  norm_thirdOrderContourRemainder_le_edges x a c W

example (x C A T c : ℝ) :
    thirdOrderGoodHeightContourRemainderMajorant x C A T c =
      (2 * ((C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 3) *
          (c + 1)) + thirdOrderOddVerticalBound x 0 T * (2 * T)) /
        (2 * Real.pi) := rfl

example {x c : ℝ} (hx : 1 < x) (hc : 1 < c) (hc2 : c ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ‖thirdOrderContourRemainder x (-1) c
              (T / (2 * Real.pi))‖ ≤
            thirdOrderGoodHeightContourRemainderMajorant x C A T c :=
  exists_goodHeight_Icc_norm_thirdOrderContourRemainder_le hx hc hc2

end PrimeNumberTheorem.ExplicitFormulaResidues
