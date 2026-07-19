import PrimeNumberTheorem.SmoothedErrorTransfer

open Complex Set
open scoped BigOperators Interval

example {x σ b t K : ℝ} (hx : 1 ≤ x) (hσ : σ ≤ b) (ht : 0 < |t|)
    (hK : 0 ≤ K)
    (hlog : ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ K) :
    ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderExplicitFormulaIntegrand
        x ((σ : ℂ) + I * t)‖ ≤ K * x ^ b / |t| ^ 2 :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderExplicitFormulaIntegrand_horizontal_le_of_logDeriv_le_of_re_le
    hx hσ ht hK hlog

example {x y a b : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (ha : -1 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        PrimeNumberTheorem.ExplicitFormulaAux.goodHeight T ∧
          ∀ t : ℝ, |t| = T →
            ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderHorizontalXDifference
                x y a b t‖ ≤
              ((C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2) +
                (C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2)) *
                (b - a) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_goodHeight_Icc_norm_secondOrderHorizontalXDifference_le
    hx hy ha hab hb

example (x y a c W : ℝ) :
    ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder y a c W -
        PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder x a c W‖ ≤
      (‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderHorizontalXDifference
            x y a c (-(2 * Real.pi * W))‖ +
          ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderHorizontalXDifference
            x y a c (2 * Real.pi * W)‖ +
          ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderLeftXDifference x y a W‖) /
        (2 * Real.pi) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderContourRemainder_sub_le_edgeDifferences
    x y a c W

example {x y ε c T : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hε : 0 < ε)
    (hc : 1 + ε ≤ c) (hT : 0 < T) :
    ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderHorizontalXDifference
        x y (1 + ε) c T‖ ≤
      (PrimeNumberTheorem.ExplicitFormulaResidues.vonMangoldtLSeriesNorm ε *
          y ^ c / T ^ 2) *
          (c - (1 + ε)) +
        (PrimeNumberTheorem.ExplicitFormulaResidues.vonMangoldtLSeriesNorm ε *
          x ^ c / T ^ 2) *
          (c - (1 + ε)) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderHorizontalXDifference_right_le
    hx hy hε hc hT

example {x y ε c T : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hε : 0 < ε)
    (hc : 1 + ε ≤ c) (hT : 0 < T) :
    ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderHorizontalXDifference
        x y (1 + ε) c (-T)‖ ≤
      (PrimeNumberTheorem.ExplicitFormulaResidues.vonMangoldtLSeriesNorm ε *
          y ^ c / T ^ 2) *
          (c - (1 + ε)) +
        (PrimeNumberTheorem.ExplicitFormulaResidues.vonMangoldtLSeriesNorm ε *
          x ^ c / T ^ 2) *
          (c - (1 + ε)) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderHorizontalXDifference_right_neg_height_le
    hx hy hε hc hT

example (approx : ℝ → ℝ → ℂ) (error : ℝ → ℝ → ℝ)
    {x h T : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hxError : ‖approx x T - (PrimeNumberTheorem.smoothedChebyshevPsi x : ℂ)‖ ≤
      error x T)
    (hyError : ‖approx (x + h) T -
      (PrimeNumberTheorem.smoothedChebyshevPsi (x + h) : ℂ)‖ ≤
        error (x + h) T) :
    PrimeNumberTheorem.chebyshevPsi x ≤
        ((approx (x + h) T).re - (approx x T).re +
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) ∧
      ((approx (x + h) T).re - (approx x T).re -
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) ≤
        PrimeNumberTheorem.chebyshevPsi (x + h) :=
  PrimeNumberTheorem.chebyshevPsi_bounds_of_smoothedApproximation
    approx error hx hh hxError hyError

example {x h a c W : ℝ} (hx : 0 < x) (hh : 0 < h) (ha : 0 < a)
    (hac : a < c) (hc : 1 < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
      ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (polesX polesY : Finset ℂ) (residueX residueY : ℂ → ℂ),
      ‖((∑ p ∈ polesX, residueX p) -
          PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
            x a c W) -
          (PrimeNumberTheorem.smoothedChebyshevPsi x : ℂ)‖ ≤
        PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError x c W ∧
      ‖((∑ p ∈ polesY, residueY p) -
          PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
            (x + h) a c W) -
          (PrimeNumberTheorem.smoothedChebyshevPsi (x + h) : ℂ)‖ ≤
        PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
          (x + h) c W ∧
      PrimeNumberTheorem.chebyshevPsi x ≤
          ((((∑ p ∈ polesY, residueY p) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  x a c W)).re +
            (PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError x c W +
              PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
                (x + h) c W)) /
              Real.log ((x + h) / x) ∧
        ((((∑ p ∈ polesY, residueY p) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  x a c W)).re -
            (PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError x c W +
              PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
                (x + h) c W)) /
              Real.log ((x + h) / x) ≤
          PrimeNumberTheorem.chebyshevPsi (x + h) := by
  rcases
      PrimeNumberTheorem.ExplicitFormulaResidues.exists_chebyshevPsi_bounds_of_secondOrderExplicitFormula
        hx hh ha hac hc hW hboundary with
    ⟨polesX, residueX, polesY, residueY, _hpolesX, _hclassX, _hresidueX,
      _hpolesY, _hclassY, _hresidueY, hxError, hyError, hbounds⟩
  exact ⟨polesX, polesY, residueX, residueY, hxError, hyError, hbounds⟩
