import PrimeNumberTheorem.SmoothedErrorTransfer
import PrimeNumberTheorem.SafeSecondOrderExplicitFormula

open Complex Set
open scoped BigOperators Interval

example {x T t : ℝ} {N : ℕ} (hx : 0 < x) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderExplicitFormulaIntegrand
        x (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound x N T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le_of_pos
    hx hT ht

example {x y W : ℝ} {N : ℕ} (hx : 0 < x) (hy : 0 < y) (hW : 0 ≤ W) :
    ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderLeftXDifference
        x y (-(2 * (N : ℝ) + 1)) W‖ ≤
      (PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
          y N (2 * Real.pi * W) +
        PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
          x N (2 * Real.pi * W)) *
        (2 * (2 * Real.pi * W)) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderLeftXDifference_odd_le_of_pos
    hx hy hW

example {x y T t : ℝ} {N : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y)
    (hT : 0 ≤ T) (ht : |t| ≤ T)
    (hsmall :
      (2 * (N : ℝ) + 1 + T) * (Real.log y - Real.log x) ≤ 1) :
    ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderExplicitFormulaIntegrand
          y (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I) -
        PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderExplicitFormulaIntegrand
          x (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      2 *
          PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
            x N T *
        (Real.log y - Real.log x) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderExplicitFormulaIntegrand_sub_odd_vertical_le_of_pos
    hx hy hxy hT ht hsmall

example {x T : ℝ} {N : ℕ} (hx : 0 < x) :
    IntervalIntegrable
      (fun t : ℝ =>
        PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderExplicitFormulaIntegrand
          x (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I))
      MeasureTheory.volume (-T) T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.intervalIntegrable_secondOrderExplicitFormulaIntegrand_odd_vertical_of_pos
    hx

example {x y W : ℝ} {N : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) (hW : 0 ≤ W)
    (hsmall :
      (2 * (N : ℝ) + 1 + 2 * Real.pi * W) *
        (Real.log y - Real.log x) ≤ 1) :
    ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderLeftXDifference
        x y (-(2 * (N : ℝ) + 1)) W‖ ≤
      (2 *
          PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
            x N (2 * Real.pi * W) *
          (Real.log y - Real.log x)) *
        (2 * (2 * Real.pi * W)) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderLeftXDifference_odd_increment_le_of_pos
    hx hy hxy hW hsmall

example {N : ℕ} {T c : ℝ} (hT : 0 < T) (hc : 1 < c)
    (hgood : PrimeNumberTheorem.ExplicitFormulaAux.goodHeight T) :
    ∀ p ∈
      ([[(-(2 * (N : ℝ) + 1)), c]] ×ℂ [[-T, T]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        -(2 * (N : ℝ) + 1) < p.re ∧ p.re < c ∧
          -T < p.im ∧ p.im < T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrder_poleCandidate_mem_interior_negativeOdd_rectangle_of_goodHeight
    hT hc hgood

example {x y c : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hc : 1 < c) (hc2 : c ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        PrimeNumberTheorem.ExplicitFormulaAux.goodHeight T ∧
          (∀ p ∈
            ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ),
            p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
              -1 < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T) ∧
          ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                y (-1) c (T / (2 * Real.pi)) -
              PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                x (-1) c (T / (2 * Real.pi))‖ ≤
            (2 *
                (((C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2) +
                    (C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2)) *
                  (c - (-1))) +
              (PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
                    y 0 T +
                  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
                    x 0 T) *
                (2 * T)) /
              (2 * Real.pi) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_goodHeight_Icc_norm_secondOrderContourRemainder_sub_neg_one_le
    hx hy hc hc2

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        PrimeNumberTheorem.ExplicitFormulaAux.goodHeight T ∧
          ∀ {x y c : ℝ}, 1 ≤ x → 1 ≤ y → 1 < c → c ≤ 2 →
            (∀ p ∈
              ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ),
              p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
                -1 < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T) ∧
            ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  y (-1) c (T / (2 * Real.pi)) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  x (-1) c (T / (2 * Real.pi))‖ ≤
              (2 *
                  (((C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2) +
                      (C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2)) *
                    (c - (-1))) +
                (PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
                      y 0 T +
                    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
                      x 0 T) *
                  (2 * T)) /
                (2 * Real.pi) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_uniform_goodHeight_Icc_norm_secondOrderContourRemainder_sub_neg_one_le

example {x T t : ℝ} {N : ℕ} (hx : 1 < x) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderExplicitFormulaIntegrand
        x (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound x N T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le
    hx hT ht

example {x y W : ℝ} {N : ℕ} (hx : 1 < x) (hy : 1 < y) (hW : 0 ≤ W) :
    ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderLeftXDifference
        x y (-(2 * (N : ℝ) + 1)) W‖ ≤
      (PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
          y N (2 * Real.pi * W) +
        PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
          x N (2 * Real.pi * W)) *
        (2 * (2 * Real.pi * W)) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderLeftXDifference_odd_le
    hx hy hW

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

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        PrimeNumberTheorem.ExplicitFormulaAux.goodHeight T ∧
          ∀ {x y a b : ℝ}, 1 ≤ x → 1 ≤ y → -1 ≤ a → a ≤ b → b ≤ 2 →
            ∀ t : ℝ, |t| = T →
              ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderHorizontalXDifference
                  x y a b t‖ ≤
                ((C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2) +
                  (C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2)) *
                  (b - a) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_uniform_goodHeight_Icc_norm_secondOrderHorizontalXDifference_le

example {x y σ b t K : ℝ}
    (hx : 1 ≤ x) (hy : 0 < y) (hσ : σ ≤ b) (ht : 0 < |t|)
    (hK : 0 ≤ K)
    (hlogDeriv :
      ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K)
    (hlog : 0 ≤ Real.log y - Real.log x)
    (hsmall :
      ‖((σ : ℂ) + (t : ℂ) * I)‖ *
          (Real.log y - Real.log x) ≤ 1) :
    ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderExplicitFormulaIntegrand
          y ((σ : ℂ) + (t : ℂ) * I) -
        PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderExplicitFormulaIntegrand
          x ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      2 * K * x ^ b * (Real.log y - Real.log x) / |t| :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderExplicitFormulaIntegrand_sub_horizontal_le
    hx hy hσ ht hK hlogDeriv hlog hsmall

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        PrimeNumberTheorem.ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h a b : ℝ},
            1 ≤ x → 0 ≤ h → -1 ≤ a → a ≤ b → b ≤ 2 →
            (T + 2) * Real.log ((x + h) / x) ≤ 1 →
            ∀ t : ℝ, |t| = T →
              ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderHorizontalXDifference
                  x (x + h) a b t‖ ≤
                (2 * C * x ^ (2 : ℝ) *
                    Real.log ((x + h) / x) *
                    (1 + Real.log (A + 6)) ^ 2 / T) *
                  (b - a) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_uniform_goodHeight_Icc_norm_secondOrderHorizontalXDifference_increment_le

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        PrimeNumberTheorem.ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (T + 2) * Real.log ((x + h) / x) ≤ 1 →
            let c := 1 + 1 / Real.log (x + h)
            (∀ p ∈
              ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ),
              p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
                -1 < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T) ∧
            ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  (x + h) (-1) c (T / (2 * Real.pi)) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  x (-1) c (T / (2 * Real.pi))‖ ≤
              PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementContourBudget
                C x h A T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_uniform_goodHeight_Icc_norm_secondOrderContourRemainder_increment_le

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        PrimeNumberTheorem.ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (T + 2) * Real.log ((x + h) / x) ≤ 1 →
            let c := 1 + 1 / Real.log (x + h)
            (∀ p ∈
              ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ),
              p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
                -1 < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T) ∧
            ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  (x + h) (-1) c (T / (2 * Real.pi)) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  x (-1) c (T / (2 * Real.pi))‖ /
                Real.log ((x + h) / x) ≤
              (2 *
                    ((2 * C * x ^ (2 : ℝ) *
                          (1 + Real.log (A + 6)) ^ 2 / T) *
                      ((1 + 1 / Real.log (x + h)) - (-1))) +
                  (2 *
                      PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
                        x 0 T) *
                    (2 * T)) /
                (2 * Real.pi) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_uniform_goodHeight_Icc_norm_secondOrderContourRemainder_increment_div_log_le

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

example {x c W : ℝ} (hx : 0 < x) (hc : 1 < c) (hW : 0 < W) :
    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError x c W =
      (x ^ c / (2 * Real.pi ^ 2 * W)) *
        PrimeNumberTheorem.ExplicitFormulaResidues.vonMangoldtLSeriesNorm
          (c - 1) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError_eq_vonMangoldtLSeriesNorm
    hx hc hW

example {x ε W : ℝ} (hx : 0 < x) (hε : 0 < ε) (hW : 0 < W) :
    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
        x (1 + ε) W ≤
      (x ^ (1 + ε) / (2 * Real.pi ^ 2 * W)) *
        ((2 / ε) * (1 + 2 / ε)) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError_le_explicit
    hx hε hW

example {x h ε W : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hε : 0 < ε) (hW : 0 < W) :
    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
          x (1 + ε) W +
        PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
          (x + h) (1 + ε) W ≤
      (x ^ (1 + ε) / (2 * Real.pi ^ 2 * W) +
          (x + h) ^ (1 + ε) / (2 * Real.pi ^ 2 * W)) *
        ((2 / ε) * (1 + 2 / ε)) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError_add_le_explicit
    hx hh hε hW

example {x W : ℝ} (hx : 1 < x) (hW : 0 < W) :
    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
        x (1 + 1 / Real.log x) W ≤
      (Real.exp 1 * x / (2 * Real.pi ^ 2 * W)) *
        (4 * (1 + Real.log x) ^ 2) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError_moving_line_le
    hx hW

example {x h W : ℝ} (hx : 1 < x) (hh : 0 < h) (hW : 0 < W) :
    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
          x (1 + 1 / Real.log (x + h)) W +
        PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
          (x + h) (1 + 1 / Real.log (x + h)) W ≤
      (2 * (Real.exp 1 * (x + h) /
          (2 * Real.pi ^ 2 * W))) *
        (4 * (1 + Real.log (x + h)) ^ 2) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError_add_moving_line_le
    hx hh hW

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

example {x0 x1 y0 y1 : ℝ} (hx0 : x0 < 0) (hx1 : 0 < x1)
    (hy0 : y0 < 0) (hy1 : 0 < y1) :
    MathlibAux.boundaryRectIntegral (fun z : ℂ => z⁻¹ / z)
        x0 x1 y0 y1 = 0 :=
  MathlibAux.boundaryRectIntegral_inv_sq_zero_of_mem hx0 hx1 hy0 hy1

example {x a c W : ℝ} (hx : 0 < x) (ha : a < 0) (hc : 0 < c)
    (hW : 0 < W)
    (hboundary : ∀ p ∈ ([[a, c]] ×ℂ [[-W, W]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈ ([[a, c]] ×ℂ [[-W, W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      residue 0 =
        deriv (fun z : ℂ =>
          -logDeriv riemannZeta z * (x : ℂ) ^ z) 0 ∧
      (∀ p ∈ poles, p ≠ 0 → residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 2) ∧
      MathlibAux.boundaryRectIntegral
          (PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderExplicitFormulaIntegrand x)
          a c (-W) W =
        (2 * Real.pi * Complex.I) * ∑ p ∈ poles, residue p :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_boundaryRectIntegral_secondOrderExplicitFormulaIntegrand_crossing_zero
    hx ha hc hW hboundary

example {x a c W : ℝ} (hx : 0 < x) (ha : a < 0) (hc : 0 < c)
    (hW : 0 < W)
    (hboundary : ∀ p ∈
      ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      residue 0 =
        deriv (fun z : ℂ =>
          -logDeriv riemannZeta z * (x : ℂ) ^ z) 0 ∧
      (∀ p ∈ poles, p ≠ 0 → residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) *
          (x : ℂ) ^ p / p ^ 2) ∧
      (∫ w : ℝ in (-W)..W,
          PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderExplicitFormulaIntegrand
            x ((c : ℂ) + 2 * Real.pi * w * Complex.I)) =
        (∑ p ∈ poles, residue p) -
          PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
            x a c W :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_scaledRightIntegral_eq_residue_sum_sub_secondOrderContourRemainder_crossing_zero
    hx ha hc hW hboundary

example {x a c W : ℝ} (hx : 0 < x) (ha : a < 0) (hc : 1 < c)
    (hW : 0 < W)
    (hboundary : ∀ p ∈
      ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      residue 0 =
        deriv (fun z : ℂ =>
          -logDeriv riemannZeta z * (x : ℂ) ^ z) 0 ∧
      (∀ p ∈ poles, p ≠ 0 → residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) *
          (x : ℂ) ^ p / p ^ 2) ∧
      ‖((∑ p ∈ poles, residue p) -
          PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
            x a c W) -
          (PrimeNumberTheorem.smoothedChebyshevPsi x : ℂ)‖ ≤
        ∑' n : ℕ,
          PrimeNumberTheorem.vonMangoldt n * (x / n) ^ c /
            (2 * Real.pi ^ 2 * W) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_norm_residue_sum_sub_contourRemainder_sub_smoothedPsi_le_crossing_zero
    hx ha hc hW hboundary

example {x h a c W : ℝ} (hx : 0 < x) (hh : 0 < h) (ha : a < 0)
    (hc : 1 < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
      ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (polesX polesY : Finset ℂ) (residueX residueY : ℂ → ℂ),
      residueX 0 =
        deriv (fun z : ℂ =>
          -logDeriv riemannZeta z * (x : ℂ) ^ z) 0 ∧
      residueY 0 =
        deriv (fun z : ℂ =>
          -logDeriv riemannZeta z * ((x + h : ℝ) : ℂ) ^ z) 0 ∧
      ‖((∑ p ∈ polesX, residueX p) -
          PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
            x a c W) -
          (PrimeNumberTheorem.smoothedChebyshevPsi x : ℂ)‖ ≤
        PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
          x c W ∧
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
            (PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
                x c W +
              PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
                (x + h) c W)) /
              Real.log ((x + h) / x) ∧
        ((((∑ p ∈ polesY, residueY p) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  x a c W)).re -
            (PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
                x c W +
              PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
                (x + h) c W)) /
              Real.log ((x + h) / x) ≤
          PrimeNumberTheorem.chebyshevPsi (x + h) := by
  rcases
      PrimeNumberTheorem.ExplicitFormulaResidues.exists_chebyshevPsi_bounds_of_secondOrderExplicitFormula_crossing_zero
        hx hh ha hc hW hboundary with
    ⟨polesX, residueX, polesY, residueY,
      _hpolesX, _hclassX, _hcompleteX, hzeroX, _hresidueX,
      _hpolesY, _hclassY, _hcompleteY, hzeroY, _hresidueY,
      hxError, hyError, hbounds⟩
  exact
    ⟨polesX, polesY, residueX, residueY,
      hzeroX, hzeroY, hxError, hyError, hbounds⟩

example {x h a W : ℝ} (hx : 1 < x) (hh : 0 < h) (ha : a < 0)
    (hW : 0 < W)
    (hboundary : ∀ p ∈
      ([[a, 1 + 1 / Real.log (x + h)]] ×ℂ
          [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < 1 + 1 / Real.log (x + h) ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (polesX polesY : Finset ℂ) (residueX residueY : ℂ → ℂ),
      residueX 0 =
        deriv (fun z : ℂ =>
          -logDeriv riemannZeta z * (x : ℂ) ^ z) 0 ∧
      residueY 0 =
        deriv (fun z : ℂ =>
          -logDeriv riemannZeta z * ((x + h : ℝ) : ℂ) ^ z) 0 ∧
      PrimeNumberTheorem.chebyshevPsi x ≤
          ((((∑ p ∈ polesY, residueY p) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  (x + h) a (1 + 1 / Real.log (x + h)) W) -
              ((∑ p ∈ polesX, residueX p) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  x a (1 + 1 / Real.log (x + h)) W)).re +
            PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderMovingEndpointPerronBudget
              x h W) /
              Real.log ((x + h) / x) ∧
        ((((∑ p ∈ polesY, residueY p) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  (x + h) a (1 + 1 / Real.log (x + h)) W) -
              ((∑ p ∈ polesX, residueX p) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  x a (1 + 1 / Real.log (x + h)) W)).re -
            PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderMovingEndpointPerronBudget
              x h W) /
              Real.log ((x + h) / x) ≤
          PrimeNumberTheorem.chebyshevPsi (x + h) := by
  rcases
      PrimeNumberTheorem.ExplicitFormulaResidues.exists_chebyshevPsi_bounds_of_secondOrderExplicitFormula_crossing_zero_moving_line
        hx hh ha hW hboundary with
    ⟨polesX, residueX, polesY, residueY,
      _hpolesX, _hclassX, _hcompleteX, hzeroX, _hresidueX,
      _hpolesY, _hclassY, _hcompleteY, hzeroY, _hresidueY, hbounds⟩
  exact
    ⟨polesX, polesY, residueX, residueY,
      hzeroX, hzeroY, hbounds⟩

example {x y : ℝ} {p : ℂ}
    (hx : 0 < x) (hy : 0 < y) (hp : p ≠ 0)
    (hlog : 0 ≤ Real.log y - Real.log x)
    (hsmall : ‖p‖ * (Real.log y - Real.log x) ≤ 1) :
    ‖((y : ℂ) ^ p - (x : ℂ) ^ p) / p ^ 2‖ ≤
      2 * x ^ p.re * (Real.log y - Real.log x) / ‖p‖ :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderRieszFactor_sub_le
    hx hy hp hlog hsmall

example {x h : ℝ} {p : ℂ}
    (hx : 0 < x) (hh : 0 ≤ h) (hp : p ≠ 0)
    (hsmall : ‖p‖ * Real.log ((x + h) / x) ≤ 1) :
    ‖(((x + h : ℝ) : ℂ) ^ p - (x : ℂ) ^ p) / p ^ 2‖ ≤
      2 * x ^ p.re * Real.log ((x + h) / x) / ‖p‖ :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderRieszFactor_increment_le
    hx hh hp hsmall

example {x h T : ℝ} {ρ : ℂ}
    (hx : 0 < x) (hh : 0 ≤ h)
    (hρ : ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T)
    (hsmall :
      (T + 1) * Real.log ((x + h) / x) ≤ 1) :
    ‖(((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2‖ ≤
      2 * x ^ ρ.re * Real.log ((x + h) / x) / ‖ρ‖ :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderRieszFactor_increment_le_of_mem_nontrivialZerosFinset
    hx hh hρ hsmall

example {x h T : ℝ}
    (hx : 1 ≤ x) (hh : 0 ≤ h)
    (hsmall :
      (T + 1) * Real.log ((x + h) / x) ≤ 1) :
    ‖∑ ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T,
        -(analyticOrderNatAt riemannZeta ρ : ℂ) *
          ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2)‖ ≤
      2 * x * Real.log ((x + h) / x) *
        PrimeNumberTheorem.ExplicitFormulaAux.globalReciprocalZeroMultiplicity T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderRieszZeroSumWithMultiplicity_increment_le
    hx hh hsmall

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h T : ℝ,
      1 ≤ x → 0 ≤ h → 4 ≤ T →
      (T + 1) * Real.log ((x + h) / x) ≤ 1 →
      ‖∑ ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T,
          -(analyticOrderNatAt riemannZeta ρ : ℂ) *
            ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2)‖ ≤
        2 * C * x * Real.log ((x + h) / x) *
          (1 + Real.log (T + 6)) ^ 2 :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_C_norm_secondOrderRieszZeroSumWithMultiplicity_increment_le_log_sq

example {poles : Finset ℂ} {c T : ℝ}
    (hT : 0 < T) (hc : 1 < c)
    (hgood : PrimeNumberTheorem.ExplicitFormulaAux.goodHeight T)
    (hpoles : ∀ p ∈ poles,
      -1 < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T)
    (hclass : ∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0)
    (hcomplete : ∀ p, p ∈
        ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ) →
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles) :
    (poles.erase 0).erase 1 =
      PrimeNumberTheorem.nontrivialZerosFinset T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.erase_zero_one_poles_eq_nontrivialZerosFinset
    hT hc hgood hpoles hclass hcomplete

example {poles : Finset ℂ} {T h : ℝ} (f : ℂ → ℂ)
    (hone : (1 : ℂ) ∈ poles)
    (hsupport : (poles.erase 0).erase 1 =
      PrimeNumberTheorem.nontrivialZerosFinset T) :
    (∑ p ∈ poles.erase 0, if p = 1 then (h : ℂ) else f p) =
      (h : ℂ) +
        ∑ ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T, f ρ :=
  PrimeNumberTheorem.ExplicitFormulaResidues.sum_erase_zero_ite_one_eq_main_add_nontrivialZeroSum
    f hone hsupport

example {x h T : ℝ}
    (hx : 1 ≤ x) (hh : 0 ≤ h)
    (hsmall : (T + 1) * Real.log ((x + h) / x) ≤ 1) :
    ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderNontrivialZeroIncrement
        x h T‖ ≤
      2 * x * Real.log ((x + h) / x) *
        PrimeNumberTheorem.ExplicitFormulaAux.globalReciprocalZeroMultiplicity T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_secondOrderNontrivialZeroIncrement_le
    hx hh hsmall

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h T : ℝ,
      1 ≤ x → 0 ≤ h → 4 ≤ T →
      (T + 1) * Real.log ((x + h) / x) ≤ 1 →
      ‖PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderNontrivialZeroIncrement
          x h T‖ ≤
        2 * C * x * Real.log ((x + h) / x) *
          (1 + Real.log (T + 6)) ^ 2 :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_C_norm_secondOrderNontrivialZeroIncrement_le_log_sq

example {x h : ℝ} (hx : 0 < x) (hy : 0 < x + h) :
    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOriginDerivativeIncrement
        x h =
      -(Real.log (2 * Real.pi) : ℂ) *
        (Real.log ((x + h) / x) : ℂ) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOriginDerivativeIncrement_eq
    hx hy

example {x h T : ℝ} :
    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderMovingEndpointPerronBudget
        x h (T / (2 * Real.pi)) =
      8 * Real.exp 1 * (x + h) * (1 + Real.log (x + h)) ^ 2 /
        (Real.pi * T) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderMovingEndpointPerronBudget_div_two_pi_eq

example {C x h A T : ℝ}
    (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1)) :
    0 ≤
      PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightContourBudget
        C x h A T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightContourBudget_nonneg
    hC hx hh hA hT

example {C x h A T : ℝ}
    (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1)) :
    0 ≤
      PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementContourBudget
        C x h A T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementContourBudget_nonneg
    hC hx hh hA hT

example (C x h A T : ℝ) :
    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementContourBudget
        C x h A T =
      (2 *
            ((2 * C * x ^ (2 : ℝ) * Real.log ((x + h) / x) *
                  (1 + Real.log (A + 6)) ^ 2 / T) *
              ((1 + 1 / Real.log (x + h)) - (-1))) +
          (2 *
              PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
                x 0 T *
              Real.log ((x + h) / x)) *
            (2 * T)) /
        (2 * Real.pi) := rfl

example {C x h A T : ℝ} (hx : 0 < x) (hh : 0 < h) :
    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementContourBudget
          C x h A T /
        Real.log ((x + h) / x) =
      (2 *
            ((2 * C * x ^ (2 : ℝ) *
                  (1 + Real.log (A + 6)) ^ 2 / T) *
              ((1 + 1 / Real.log (x + h)) - (-1))) +
          (2 *
              PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
                x 0 T) *
            (2 * T)) /
        (2 * Real.pi) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementContourBudget_div_log_eq
    hx hh

example {C x h A T : ℝ} (hx : 0 < x) (hh : 0 < h) :
    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementTotalBudget
          C x h A T /
        Real.log ((x + h) / x) =
      (2 *
            ((2 * C * x ^ (2 : ℝ) *
                  (1 + Real.log (A + 6)) ^ 2 / T) *
              ((1 + 1 / Real.log (x + h)) - (-1))) +
          (2 *
              PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
                x 0 T) *
            (2 * T)) /
          (2 * Real.pi) +
        PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderMovingEndpointPerronBudget
            x h (T / (2 * Real.pi)) /
          Real.log ((x + h) / x) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementTotalBudget_div_log_eq
    hx hh

example {x h T : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hT : 0 < T)
    (hsmall : (T + 2) * Real.log ((x + h) / x) ≤ 1) :
    2 *
          PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
            x 0 T *
        Real.log ((x + h) / x) ≤
      PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
          (x + h) 0 T +
        PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
          x 0 T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderIncrementLeftVerticalScalar_le_separateEndpoints
    hx hh hT hsmall

example {C x h A T : ℝ}
    (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1))
    (hsmall : (T + 2) * Real.log ((x + h) / x) ≤ 1) :
    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementContourBudget
        C x h A T ≤
      PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightContourBudget
        C x h A T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementContourBudget_le
    hC hx hh hA hT hsmall

example {C x h A T : ℝ}
    (hC : 0 < C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1))
    (hsmall : (T + 2) * Real.log ((x + h) / x) ≤ 1) :
    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementContourBudget
        C x h A T <
      PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightContourBudget
        C x h A T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementContourBudget_lt
    hC hx hh hA hT hsmall

example {C x h A T : ℝ}
    (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1)) :
    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightContourBudget
        C x h A T ≤
      6 * C * (x + h) ^ (2 : ℝ) *
          (1 + Real.log (A + 6)) ^ 2 / (Real.pi * T ^ 2) +
        (PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
              (x + h) 0 T +
            PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
              x 0 T) *
          T / Real.pi :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightContourBudget_le_explicit
    hC hx hh hA hT

example {C x h A T : ℝ}
    (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1)) :
    0 ≤
      PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget
        C x h A T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget_nonneg
    hC hx hh hA hT

example {C x h A T : ℝ}
    (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1)) :
    0 ≤
      PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementTotalBudget
        C x h A T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementTotalBudget_nonneg
    hC hx hh hA hT

example {C x h A T : ℝ}
    (hC : 0 < C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1))
    (hsmall : (T + 2) * Real.log ((x + h) / x) ≤ 1) :
    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementTotalBudget
        C x h A T <
      PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget
        C x h A T :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightIncrementTotalBudget_lt
    hC hx hh hA hT hsmall

example {C x h A T : ℝ}
    (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1)) :
    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget
        C x h A T ≤
      6 * C * (x + h) ^ (2 : ℝ) *
          (1 + Real.log (A + 6)) ^ 2 / (Real.pi * T ^ 2) +
        (PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
              (x + h) 0 T +
            PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOddVerticalBound
              x 0 T) *
          T / Real.pi +
        8 * Real.exp 1 * (x + h) * (1 + Real.log (x + h)) ^ 2 /
          (Real.pi * T) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget_le_explicit
    hC hx hh hA hT

example {x h : ℝ} (hx : Real.exp 1 ≤ x) (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        PrimeNumberTheorem.ExplicitFormulaAux.goodHeight T ∧
          ∃ (polesX polesY : Finset ℂ) (residueX residueY : ℂ → ℂ),
            polesX = polesY ∧
            (∑ p ∈ polesY, residueY p) -
                (∑ p ∈ polesX, residueX p) =
              (deriv (fun z : ℂ =>
                  -logDeriv riemannZeta z *
                    ((x + h : ℝ) : ℂ) ^ z) 0 -
                deriv (fun z : ℂ =>
                  -logDeriv riemannZeta z * (x : ℂ) ^ z) 0) +
                (∑ p ∈ polesX.erase 0,
                  (if p = 1 then (h : ℂ)
                  else -(analyticOrderNatAt riemannZeta p : ℂ) *
                    (((x + h : ℝ) : ℂ) ^ p - (x : ℂ) ^ p) / p ^ 2)) ∧
            PrimeNumberTheorem.chebyshevPsi x ≤
                (((∑ p ∈ polesY, residueY p) -
                    (∑ p ∈ polesX, residueX p)).re +
                  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget
                    C x h A T) /
                    Real.log ((x + h) / x) ∧
              (((∑ p ∈ polesY, residueY p) -
                    (∑ p ∈ polesX, residueX p)).re -
                  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget
                    C x h A T) /
                    Real.log ((x + h) / x) ≤
                PrimeNumberTheorem.chebyshevPsi (x + h) := by
  rcases
      PrimeNumberTheorem.ExplicitFormulaResidues.exists_C_forall_goodHeight_chebyshevPsi_bounds_crossing_zero_moving_line_neg_one
        hx hh with
    ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with
    ⟨T, hT, hgood, polesX, residueX, polesY, residueY,
      _hpolesX, _hclassX, _hcompleteX, _hzeroX, _hresidueX,
      _hpolesY, _hclassY, _hcompleteY, _hzeroY, _hresidueY,
      hpolesEq, hsumDiff, hbounds⟩
  exact
    ⟨T, hT, hgood, polesX, polesY, residueX, residueY,
      hpolesEq, hsumDiff, hbounds⟩

example {x h : ℝ} (hx : Real.exp 1 ≤ x) (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        PrimeNumberTheorem.ExplicitFormulaAux.goodHeight T ∧
          PrimeNumberTheorem.chebyshevPsi x ≤
              ((PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOriginDerivativeIncrement
                    x h + (h : ℂ) +
                  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderNontrivialZeroIncrement
                    x h T).re +
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget
                  C x h A T) /
                  Real.log ((x + h) / x) ∧
            ((PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderOriginDerivativeIncrement
                    x h + (h : ℂ) +
                  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderNontrivialZeroIncrement
                    x h T).re -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget
                  C x h A T) /
                  Real.log ((x + h) / x) ≤
              PrimeNumberTheorem.chebyshevPsi (x + h) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_C_forall_goodHeight_chebyshevPsi_bounds_standard_zero_sum
    hx hh

example {x h : ℝ} (hx : Real.exp 1 ≤ x) (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        PrimeNumberTheorem.ExplicitFormulaAux.goodHeight T ∧
          PrimeNumberTheorem.chebyshevPsi x ≤
              ((-(Real.log (2 * Real.pi) : ℂ) *
                    (Real.log ((x + h) / x) : ℂ) +
                  (h : ℂ) +
                  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderNontrivialZeroIncrement
                    x h T).re +
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget
                  C x h A T) /
                  Real.log ((x + h) / x) ∧
            ((-(Real.log (2 * Real.pi) : ℂ) *
                    (Real.log ((x + h) / x) : ℂ) +
                  (h : ℂ) +
                  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderNontrivialZeroIncrement
                    x h T).re -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget
                  C x h A T) /
                  Real.log ((x + h) / x) ≤
              PrimeNumberTheorem.chebyshevPsi (x + h) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_C_forall_goodHeight_chebyshevPsi_bounds_explicit_origin_zero_sum
    hx hh

example {x h : ℝ} (hx : Real.exp 1 ≤ x) (hh : 0 < h) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      (A + 2) * Real.log ((x + h) / x) ≤ 1 →
        ∃ T ∈ Set.Icc A (A + 1),
          PrimeNumberTheorem.ExplicitFormulaAux.goodHeight T ∧
            PrimeNumberTheorem.chebyshevPsi x ≤
                (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) +
                    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget
                      C x h A T +
                    2 * D * x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ∧
              (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) -
                    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget
                      C x h A T -
                    2 * D * x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ≤
                PrimeNumberTheorem.chebyshevPsi (x + h) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_C_D_forall_goodHeight_chebyshevPsi_bounds_scalar_log_sq
    hx hh

example {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    h / Real.log ((x + h) / x) ∈ Set.Icc x (x + h) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.smoothingIncrementDivLog_mem_Icc
    hx hh

example {x h : ℝ} (hx : Real.exp 1 ≤ x) (hh : 0 < h) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      (A + 2) * Real.log ((x + h) / x) ≤ 1 →
        ∃ T ∈ Set.Icc A (A + 1),
          PrimeNumberTheorem.ExplicitFormulaAux.goodHeight T ∧
            PrimeNumberTheorem.chebyshevPsi x - x ≤
                h - Real.log (2 * Real.pi) +
                  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget
                      C x h A T /
                    Real.log ((x + h) / x) +
                  2 * D * x * (1 + Real.log (T + 6)) ^ 2 ∧
              x - Real.log (2 * Real.pi) -
                    PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget
                        C x h A T /
                      Real.log ((x + h) / x) -
                    2 * D * x * (1 + Real.log (T + 6)) ^ 2 ≤
                PrimeNumberTheorem.chebyshevPsi (x + h) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_C_D_forall_goodHeight_chebyshevPsi_endpoint_error_log_sq
    hx hh

example {x A : ℝ} (hx : 0 < x) (hA : 4 ≤ A) :
    0 <
      PrimeNumberTheorem.ExplicitFormulaResidues.canonicalSecondOrderSmoothingWidth
        x A :=
  PrimeNumberTheorem.ExplicitFormulaResidues.canonicalSecondOrderSmoothingWidth_pos
    hx hA

example {x A : ℝ} (hx : 0 < x) :
    Real.log
        ((x +
            PrimeNumberTheorem.ExplicitFormulaResidues.canonicalSecondOrderSmoothingWidth
              x A) / x) =
      1 / (A + 2) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.canonicalSecondOrderSmoothingWidth_log_eq
    hx

example {x A : ℝ} (hx : 0 < x) (hA : 4 ≤ A) :
    (A + 2) *
        Real.log
          ((x +
              PrimeNumberTheorem.ExplicitFormulaResidues.canonicalSecondOrderSmoothingWidth
                x A) / x) ≤ 1 :=
  PrimeNumberTheorem.ExplicitFormulaResidues.canonicalSecondOrderSmoothingWidth_small
    hx hA

example {x h A : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hA : 4 ≤ A)
    (hsmall : (A + 2) * Real.log ((x + h) / x) ≤ 1) :
    h ≤
      PrimeNumberTheorem.ExplicitFormulaResidues.canonicalSecondOrderSmoothingWidth
        x A :=
  PrimeNumberTheorem.ExplicitFormulaResidues.le_canonicalSecondOrderSmoothingWidth_of_small
    hx hh hA hsmall

example {x A : ℝ} (hx : Real.exp 1 ≤ x) (hA : 4 ≤ A) :
    ∃ C D T : ℝ,
      0 ≤ C ∧ 0 ≤ D ∧ T ∈ Set.Icc A (A + 1) ∧
        PrimeNumberTheorem.ExplicitFormulaAux.goodHeight T ∧
          PrimeNumberTheorem.chebyshevPsi x - x ≤
              PrimeNumberTheorem.ExplicitFormulaResidues.canonicalSecondOrderSmoothingWidth
                    x A -
                Real.log (2 * Real.pi) +
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget
                    C x
                    (PrimeNumberTheorem.ExplicitFormulaResidues.canonicalSecondOrderSmoothingWidth
                      x A) A T /
                  Real.log
                    ((x +
                        PrimeNumberTheorem.ExplicitFormulaResidues.canonicalSecondOrderSmoothingWidth
                          x A) / x) +
                2 * D * x * (1 + Real.log (T + 6)) ^ 2 ∧
            x - Real.log (2 * Real.pi) -
                  PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderSelectedHeightTotalBudget
                      C x
                      (PrimeNumberTheorem.ExplicitFormulaResidues.canonicalSecondOrderSmoothingWidth
                        x A) A T /
                    Real.log
                      ((x +
                          PrimeNumberTheorem.ExplicitFormulaResidues.canonicalSecondOrderSmoothingWidth
                            x A) / x) -
                  2 * D * x * (1 + Real.log (T + 6)) ^ 2 ≤
              PrimeNumberTheorem.chebyshevPsi
                (x +
                  PrimeNumberTheorem.ExplicitFormulaResidues.canonicalSecondOrderSmoothingWidth
                    x A) :=
  PrimeNumberTheorem.ExplicitFormulaResidues.exists_C_D_goodHeight_chebyshevPsi_canonical_smoothing_error
    hx hA

namespace PrimeNumberTheorem.ExplicitFormulaResidues

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
          ∃ (polesX : Finset ℂ) (residueX : ℂ → ℂ)
              (polesY : Finset ℂ) (residueY : ℂ → ℂ),
            (∀ p ∈ polesX,
              -1 < p.re ∧
                p.re < 1 + 1 / Real.log (x + h) ∧
                -T < p.im ∧ p.im < T) ∧
            (∀ p ∈ polesX, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
            (∀ p, p ∈
                ([[(-1 : ℝ), 1 + 1 / Real.log (x + h)]] ×ℂ
                  [[-T, T]] : Set ℂ) →
              p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ polesX) ∧
            residueX 0 =
              deriv (fun z : ℂ =>
                -logDeriv riemannZeta z * (x : ℂ) ^ z) 0 ∧
            (∀ p ∈ polesX, p ≠ 0 → residueX p =
              if p = 1 then (x : ℂ)
              else -(analyticOrderNatAt riemannZeta p : ℂ) *
                (x : ℂ) ^ p / p ^ 2) ∧
            (∀ p ∈ polesY,
              -1 < p.re ∧
                p.re < 1 + 1 / Real.log (x + h) ∧
                -T < p.im ∧ p.im < T) ∧
            (∀ p ∈ polesY, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
            (∀ p, p ∈
                ([[(-1 : ℝ), 1 + 1 / Real.log (x + h)]] ×ℂ
                  [[-T, T]] : Set ℂ) →
              p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ polesY) ∧
            residueY 0 =
              deriv (fun z : ℂ =>
                -logDeriv riemannZeta z * ((x + h : ℝ) : ℂ) ^ z) 0 ∧
            (∀ p ∈ polesY, p ≠ 0 → residueY p =
              if p = 1 then ((x + h : ℝ) : ℂ)
              else -(analyticOrderNatAt riemannZeta p : ℂ) *
                ((x + h : ℝ) : ℂ) ^ p / p ^ 2) ∧
            polesX = polesY ∧
            (∑ p ∈ polesY, residueY p) -
                (∑ p ∈ polesX, residueX p) =
              (deriv (fun z : ℂ =>
                  -logDeriv riemannZeta z *
                    ((x + h : ℝ) : ℂ) ^ z) 0 -
                deriv (fun z : ℂ =>
                  -logDeriv riemannZeta z * (x : ℂ) ^ z) 0) +
                (∑ p ∈ polesX.erase 0,
                  (if p = 1 then (h : ℂ)
                  else -(analyticOrderNatAt riemannZeta p : ℂ) *
                    (((x + h : ℝ) : ℂ) ^ p - (x : ℂ) ^ p) / p ^ 2)) ∧
            chebyshevPsi x ≤
                (((∑ p ∈ polesY, residueY p) -
                    (∑ p ∈ polesX, residueX p)).re +
                  secondOrderSelectedHeightTotalBudget C x h A T) /
                    Real.log ((x + h) / x) ∧
              (((∑ p ∈ polesY, residueY p) -
                    (∑ p ∈ polesX, residueX p)).re -
                  secondOrderSelectedHeightTotalBudget C x h A T) /
                    Real.log ((x + h) / x) ≤
                chebyshevPsi (x + h) :=
  exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_crossing_zero_moving_line_neg_one

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
          chebyshevPsi x ≤
              ((secondOrderOriginDerivativeIncrement x h + (h : ℂ) +
                    secondOrderNontrivialZeroIncrement x h T).re +
                secondOrderSelectedHeightTotalBudget C x h A T) /
                  Real.log ((x + h) / x) ∧
            ((secondOrderOriginDerivativeIncrement x h + (h : ℂ) +
                    secondOrderNontrivialZeroIncrement x h T).re -
                secondOrderSelectedHeightTotalBudget C x h A T) /
                  Real.log ((x + h) / x) ≤
              chebyshevPsi (x + h) :=
  exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_standard_zero_sum

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
          chebyshevPsi x ≤
              ((-(Real.log (2 * Real.pi) : ℂ) *
                    (Real.log ((x + h) / x) : ℂ) +
                  (h : ℂ) +
                  secondOrderNontrivialZeroIncrement x h T).re +
                secondOrderSelectedHeightTotalBudget C x h A T) /
                  Real.log ((x + h) / x) ∧
            ((-(Real.log (2 * Real.pi) : ℂ) *
                    (Real.log ((x + h) / x) : ℂ) +
                  (h : ℂ) +
                  secondOrderNontrivialZeroIncrement x h T).re -
                secondOrderSelectedHeightTotalBudget C x h A T) /
                  Real.log ((x + h) / x) ≤
              chebyshevPsi (x + h) :=
  exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_explicit_origin_zero_sum

example :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 2) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x ≤
                (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) +
                    secondOrderSelectedHeightTotalBudget C x h A T +
                    2 * D * x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ∧
              (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) -
                    secondOrderSelectedHeightTotalBudget C x h A T -
                    2 * D * x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ≤
                chebyshevPsi (x + h) :=
  exists_uniform_C_D_forall_goodHeight_chebyshevPsi_bounds_scalar_log_sq

example :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 2) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x - x ≤
                h - Real.log (2 * Real.pi) +
                  secondOrderSelectedHeightTotalBudget C x h A T /
                    Real.log ((x + h) / x) +
                  2 * D * x * (1 + Real.log (T + 6)) ^ 2 ∧
              x - Real.log (2 * Real.pi) -
                    secondOrderSelectedHeightTotalBudget C x h A T /
                      Real.log ((x + h) / x) -
                    2 * D * x * (1 + Real.log (T + 6)) ^ 2 ≤
                chebyshevPsi (x + h) :=
  exists_uniform_C_D_forall_goodHeight_chebyshevPsi_endpoint_error_log_sq

example :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x : ℝ}, Real.exp 1 ≤ x →
          chebyshevPsi x - x ≤
              canonicalSecondOrderSmoothingWidth x A -
                Real.log (2 * Real.pi) +
                secondOrderSelectedHeightTotalBudget C x
                    (canonicalSecondOrderSmoothingWidth x A) A T /
                  Real.log
                    ((x + canonicalSecondOrderSmoothingWidth x A) / x) +
                2 * D * x * (1 + Real.log (T + 6)) ^ 2 ∧
            x - Real.log (2 * Real.pi) -
                  secondOrderSelectedHeightTotalBudget C x
                      (canonicalSecondOrderSmoothingWidth x A) A T /
                    Real.log
                      ((x + canonicalSecondOrderSmoothingWidth x A) / x) -
                  2 * D * x * (1 + Real.log (T + 6)) ^ 2 ≤
              chebyshevPsi
                (x + canonicalSecondOrderSmoothingWidth x A) :=
  exists_uniform_C_D_forall_goodHeight_chebyshevPsi_canonical_smoothing_error

example (hRH : RiemannHypothesis.Statement)
    {x h T : ℝ} {ρ : ℂ}
    (hx : 0 < x) (hh : 0 ≤ h)
    (hρ : ρ ∈ nontrivialZerosFinset T)
    (hsmall : (T + 1) * Real.log ((x + h) / x) ≤ 1) :
    ‖(((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2‖ ≤
      2 * Real.sqrt x * Real.log ((x + h) / x) / ‖ρ‖ :=
  norm_secondOrderRieszFactor_increment_le_of_mem_nontrivialZerosFinset_of_RH
    hRH hx hh hρ hsmall

example (hRH : RiemannHypothesis.Statement)
    {x h T : ℝ}
    (hx : 1 ≤ x) (hh : 0 ≤ h)
    (hsmall : (T + 1) * Real.log ((x + h) / x) ≤ 1) :
    ‖∑ ρ ∈ nontrivialZerosFinset T,
        -(analyticOrderNatAt riemannZeta ρ : ℂ) *
          ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2)‖ ≤
      2 * Real.sqrt x * Real.log ((x + h) / x) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T :=
  norm_secondOrderRieszZeroSumWithMultiplicity_increment_le_of_RH
    hRH hx hh hsmall

example (hRH : RiemannHypothesis.Statement) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h T : ℝ,
      1 ≤ x → 0 ≤ h → 4 ≤ T →
      (T + 1) * Real.log ((x + h) / x) ≤ 1 →
      ‖∑ ρ ∈ nontrivialZerosFinset T,
          -(analyticOrderNatAt riemannZeta ρ : ℂ) *
            ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2)‖ ≤
        2 * C * Real.sqrt x * Real.log ((x + h) / x) *
          (1 + Real.log (T + 6)) ^ 2 :=
  exists_C_norm_secondOrderRieszZeroSumWithMultiplicity_increment_le_sqrt_mul_log_sq_of_RH
    hRH

example (hRH : RiemannHypothesis.Statement)
    {x h T : ℝ}
    (hx : 1 ≤ x) (hh : 0 ≤ h)
    (hsmall : (T + 1) * Real.log ((x + h) / x) ≤ 1) :
    ‖secondOrderNontrivialZeroIncrement x h T‖ ≤
      2 * Real.sqrt x * Real.log ((x + h) / x) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T :=
  norm_secondOrderNontrivialZeroIncrement_le_of_RH hRH hx hh hsmall

example (hRH : RiemannHypothesis.Statement) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h T : ℝ,
      1 ≤ x → 0 ≤ h → 4 ≤ T →
      (T + 1) * Real.log ((x + h) / x) ≤ 1 →
      ‖secondOrderNontrivialZeroIncrement x h T‖ ≤
        2 * C * Real.sqrt x * Real.log ((x + h) / x) *
          (1 + Real.log (T + 6)) ^ 2 :=
  exists_C_norm_secondOrderNontrivialZeroIncrement_le_sqrt_mul_log_sq_of_RH
    hRH

example (hRH : RiemannHypothesis.Statement) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 2) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x ≤
                (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) +
                    secondOrderSelectedHeightTotalBudget C x h A T +
                    2 * D * Real.sqrt x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ∧
              (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) -
                    secondOrderSelectedHeightTotalBudget C x h A T -
                    2 * D * Real.sqrt x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ≤
                chebyshevPsi (x + h) :=
  exists_uniform_C_D_forall_goodHeight_chebyshevPsi_bounds_scalar_sqrt_log_sq_of_RH
    hRH

example (hRH : RiemannHypothesis.Statement) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 2) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x - x ≤
                h - Real.log (2 * Real.pi) +
                  secondOrderSelectedHeightTotalBudget C x h A T /
                    Real.log ((x + h) / x) +
                  2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 ∧
              x - Real.log (2 * Real.pi) -
                    secondOrderSelectedHeightTotalBudget C x h A T /
                      Real.log ((x + h) / x) -
                    2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 ≤
                chebyshevPsi (x + h) :=
  exists_uniform_C_D_forall_goodHeight_chebyshevPsi_endpoint_error_sqrt_log_sq_of_RH
    hRH

example (hRH : RiemannHypothesis.Statement) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x : ℝ}, Real.exp 1 ≤ x →
          chebyshevPsi x - x ≤
              canonicalSecondOrderSmoothingWidth x A -
                Real.log (2 * Real.pi) +
                secondOrderSelectedHeightTotalBudget C x
                    (canonicalSecondOrderSmoothingWidth x A) A T /
                  Real.log
                    ((x + canonicalSecondOrderSmoothingWidth x A) / x) +
                2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 ∧
            x - Real.log (2 * Real.pi) -
                  secondOrderSelectedHeightTotalBudget C x
                      (canonicalSecondOrderSmoothingWidth x A) A T /
                    Real.log
                      ((x + canonicalSecondOrderSmoothingWidth x A) / x) -
                  2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 ≤
              chebyshevPsi
                (x + canonicalSecondOrderSmoothingWidth x A) :=
  exists_uniform_C_D_forall_goodHeight_chebyshevPsi_canonical_smoothing_error_sqrt_log_sq_of_RH
    hRH

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (T + 2) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x ≤
                ((-(Real.log (2 * Real.pi) : ℂ) *
                      (Real.log ((x + h) / x) : ℂ) +
                    (h : ℂ) +
                    secondOrderNontrivialZeroIncrement x h T).re +
                  secondOrderSelectedHeightIncrementTotalBudget C x h A T) /
                    Real.log ((x + h) / x) ∧
              ((-(Real.log (2 * Real.pi) : ℂ) *
                      (Real.log ((x + h) / x) : ℂ) +
                    (h : ℂ) +
                    secondOrderNontrivialZeroIncrement x h T).re -
                  secondOrderSelectedHeightIncrementTotalBudget C x h A T) /
                    Real.log ((x + h) / x) ≤
                chebyshevPsi (x + h) :=
  exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_explicit_origin_zero_sum_increment

example :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 3) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x ≤
                (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) +
                    secondOrderSelectedHeightIncrementTotalBudget C x h A T +
                    2 * D * x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ∧
              (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) -
                    secondOrderSelectedHeightIncrementTotalBudget C x h A T -
                    2 * D * x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ≤
                chebyshevPsi (x + h) :=
  exists_uniform_C_D_forall_goodHeight_chebyshevPsi_bounds_scalar_log_sq_increment

example (hRH : RiemannHypothesis.Statement) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 3) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x ≤
                (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) +
                    secondOrderSelectedHeightIncrementTotalBudget C x h A T +
                    2 * D * Real.sqrt x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ∧
              (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) -
                    secondOrderSelectedHeightIncrementTotalBudget C x h A T -
                    2 * D * Real.sqrt x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ≤
                chebyshevPsi (x + h) :=
  exists_uniform_C_D_forall_goodHeight_chebyshevPsi_bounds_scalar_sqrt_log_sq_increment_of_RH
    hRH

example :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 3) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x - x ≤
                h - Real.log (2 * Real.pi) +
                  secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                    Real.log ((x + h) / x) +
                  2 * D * x * (1 + Real.log (T + 6)) ^ 2 ∧
              x - Real.log (2 * Real.pi) -
                    secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                      Real.log ((x + h) / x) -
                    2 * D * x * (1 + Real.log (T + 6)) ^ 2 ≤
                chebyshevPsi (x + h) :=
  exists_uniform_C_D_forall_goodHeight_chebyshevPsi_endpoint_error_log_sq_increment

example :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 3) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x - x ≤
                h - Real.log (2 * Real.pi) +
                  ((2 *
                        ((2 * C * x ^ (2 : ℝ) *
                              (1 + Real.log (A + 6)) ^ 2 / T) *
                          ((1 + 1 / Real.log (x + h)) - (-1))) +
                      (2 * secondOrderOddVerticalBound x 0 T) * (2 * T)) /
                      (2 * Real.pi) +
                    secondOrderMovingEndpointPerronBudget
                        x h (T / (2 * Real.pi)) /
                      Real.log ((x + h) / x)) +
                  2 * D * x * (1 + Real.log (T + 6)) ^ 2 ∧
              x - Real.log (2 * Real.pi) -
                    ((2 *
                          ((2 * C * x ^ (2 : ℝ) *
                                (1 + Real.log (A + 6)) ^ 2 / T) *
                            ((1 + 1 / Real.log (x + h)) - (-1))) +
                        (2 * secondOrderOddVerticalBound x 0 T) * (2 * T)) /
                        (2 * Real.pi) +
                      secondOrderMovingEndpointPerronBudget
                          x h (T / (2 * Real.pi)) /
                        Real.log ((x + h) / x)) -
                    2 * D * x * (1 + Real.log (T + 6)) ^ 2 ≤
                chebyshevPsi (x + h) :=
  exists_uniform_C_D_forall_goodHeight_chebyshevPsi_endpoint_error_log_sq_increment_explicit_contour

example (hRH : RiemannHypothesis.Statement) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 3) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x - x ≤
                h - Real.log (2 * Real.pi) +
                  secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                    Real.log ((x + h) / x) +
                  2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 ∧
              x - Real.log (2 * Real.pi) -
                    secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                      Real.log ((x + h) / x) -
                    2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 ≤
                chebyshevPsi (x + h) :=
  exists_uniform_C_D_forall_goodHeight_chebyshevPsi_endpoint_error_sqrt_log_sq_increment_of_RH
    hRH

example {C D x h A T : ℝ}
    (hC : 0 < C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1))
    (hsmall : (T + 2) * Real.log ((x + h) / x) ≤ 1) :
    h - Real.log (2 * Real.pi) +
          secondOrderSelectedHeightIncrementTotalBudget C x h A T /
            Real.log ((x + h) / x) +
          2 * D * x * (1 + Real.log (T + 6)) ^ 2 <
        h - Real.log (2 * Real.pi) +
          secondOrderSelectedHeightTotalBudget C x h A T /
            Real.log ((x + h) / x) +
          2 * D * x * (1 + Real.log (T + 6)) ^ 2 ∧
      x - Real.log (2 * Real.pi) -
          secondOrderSelectedHeightTotalBudget C x h A T /
            Real.log ((x + h) / x) -
          2 * D * x * (1 + Real.log (T + 6)) ^ 2 <
        x - Real.log (2 * Real.pi) -
          secondOrderSelectedHeightIncrementTotalBudget C x h A T /
            Real.log ((x + h) / x) -
          2 * D * x * (1 + Real.log (T + 6)) ^ 2 :=
  secondOrderSelectedHeightIncrement_endpoint_bounds_strictly_improve
    hC hx hh hA hT hsmall

end PrimeNumberTheorem.ExplicitFormulaResidues

example :
    MathlibAux.boundaryRectIntegral
        (fun z : ℂ =>
          z⁻¹ / z * 3 +
            ((fun _ : ℂ => 0) z +
              ∑ p ∈ ({1} : Finset ℂ), (z - p)⁻¹ * (fun _ : ℂ => 5) p))
        (-1) 2 (-1) 1 =
      (2 * Real.pi * Complex.I) *
        ∑ p ∈ ({1} : Finset ℂ), (fun _ : ℂ => 5) p := by
  apply
    MathlibAux.boundaryRectIntegral_eq_double_pole_add_finite_simple_pole_residue_sum
      (g := fun _ : ℂ => 0) (3 : ℂ) ({1} : Finset ℂ) (fun _ : ℂ => 5)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact differentiableOn_const 0
  · intro p hp
    simp at hp
    subst p
    norm_num
