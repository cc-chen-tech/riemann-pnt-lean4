import PrimeNumberTheorem.ZeroDensityLayerBudgetDyadicSquareMultiplicityCapacity

open Complex Filter Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem

noncomputable section

-- Five public definitions.

example (sigma tau : ℝ) (n : ℕ) : Finset ℂ :=
  actualCarlsonDyadicZeroStrip sigma tau n

example (sigma tau : ℝ) (n : ℕ) : ℝ :=
  actualCarlsonDyadicStripLinearMultiplicityCapacity sigma tau n

example (sigma tau : ℝ) (n : ℕ) : ℝ :=
  actualCarlsonDyadicStripLinearReciprocalSquareCapacity sigma tau n

example (sigma tau : ℝ) (n : ℕ) : ℝ :=
  actualCarlsonDyadicStripSquareReciprocalCapacity sigma tau n

example (sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) : ℝ :=
  actualCarlsonDyadicStripSquareReciprocalCapacityExcluding sigma tau n S

-- Sixteen public theorems.

example {α : Type*} [DecidableEq α] (S : Finset α)
    (m w : α → ℝ) (M : ℝ)
    (hm0 : ∀ a ∈ S, 0 ≤ m a) (hw0 : ∀ a ∈ S, 0 ≤ w a)
    (hmM : ∀ a ∈ S, m a ≤ M) :
    (∑ a ∈ S, (m a) ^ 2 * w a) ≤
      M * ∑ a ∈ S, m a * w a :=
  squareMultiplicityCapacity_le_max_mul_linearMultiplicityCapacity
    S m w M hm0 hw0 hmM

example {α : Type*} [DecidableEq α] (R S : Finset α)
    (m w : α → ℝ) (hw0 : ∀ a ∈ R, 0 ≤ w a) :
    (∑ a ∈ R \ S, (m a) ^ 2 * w a) ≤
      ∑ a ∈ R, (m a) ^ 2 * w a :=
  squareMultiplicityCapacity_sdiff_le R S m w hw0

example :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ rho : ℂ,
      RiemannHypothesis.IsNontrivialZero rho → 4 ≤ |rho.im| →
        (analyticOrderNatAt riemannZeta rho : ℝ) ≤
          B * (1 + Real.log (|rho.im| + 6)) :=
  ExplicitFormulaAux.exists_analyticOrderNatAt_riemannZeta_le_log_im_of_nontrivialZero

example (sigma tau : ℝ) (n : ℕ) :
    actualCarlsonDyadicZeroStrip sigma tau n ⊆
      actualCarlsonDyadicZeroShell sigma n :=
  actualCarlsonDyadicZeroStrip_subset_shell sigma tau n

example (sigma tau : ℝ) (n : ℕ) :
    0 ≤ actualCarlsonDyadicStripLinearMultiplicityCapacity sigma tau n :=
  actualCarlsonDyadicStripLinearMultiplicityCapacity_nonneg sigma tau n

example (sigma tau : ℝ) (n : ℕ) :
    0 ≤ actualCarlsonDyadicStripLinearReciprocalSquareCapacity sigma tau n :=
  actualCarlsonDyadicStripLinearReciprocalSquareCapacity_nonneg sigma tau n

example (sigma tau : ℝ) (n : ℕ) :
    0 ≤ actualCarlsonDyadicStripSquareReciprocalCapacity sigma tau n :=
  actualCarlsonDyadicStripSquareReciprocalCapacity_nonneg sigma tau n

example (sigma tau : ℝ) (n : ℕ) :
    actualCarlsonDyadicStripLinearMultiplicityCapacity sigma tau n ≤
      actualCarlsonDyadicCount sigma (n + 1) :=
  actualCarlsonDyadicStripLinearMultiplicityCapacity_le_count sigma tau n

example (sigma tau : ℝ) (n : ℕ) :
    actualCarlsonDyadicStripLinearReciprocalSquareCapacity sigma tau n ≤
      actualCarlsonDyadicCount sigma (n + 1) / ((2 : ℝ) ^ n) ^ 2 :=
  actualCarlsonDyadicStripLinearReciprocalSquareCapacity_le_count_div_sq
    sigma tau n

example :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ sigma tau : ℝ, ∀ n : ℕ,
      4 ≤ (2 : ℝ) ^ n → ∀ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n,
        (analyticOrderNatAt riemannZeta rho : ℝ) ≤
          B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) :=
  exists_actualCarlsonDyadicStrip_maxMultiplicity_le_log

example :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ sigma tau : ℝ, ∀ n : ℕ,
      4 ≤ (2 : ℝ) ^ n →
        actualCarlsonDyadicStripSquareReciprocalCapacity sigma tau n ≤
          (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6))) *
            (actualCarlsonDyadicCount sigma (n + 1) / ((2 : ℝ) ^ n) ^ 2) :=
  exists_actualCarlsonDyadicStripSquareReciprocalCapacity_le_count

example :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ sigma tau : ℝ, ∀ n : ℕ,
      4 ≤ (2 : ℝ) ^ n → ∀ S : Finset ℂ,
        actualCarlsonDyadicStripSquareReciprocalCapacityExcluding sigma tau n S ≤
          (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6))) *
            (actualCarlsonDyadicCount sigma (n + 1) / ((2 : ℝ) ^ n) ^ 2) :=
  exists_actualCarlsonDyadicStripSquareReciprocalCapacityExcluding_le_count

example (sigma : ℝ) :
    pntCarlsonClassicalDensityExponent sigma ≤ 1 :=
  pntCarlsonClassicalDensityExponent_le_one sigma

example (sigma : ℝ) :
    pntCarlsonClassicalDensityExponent sigma - 2 ≤ -1 :=
  pntCarlsonClassicalDensityExponent_sub_two_le_neg_one sigma

example (sigma : ℝ) :
    pntCarlsonClassicalDensityExponent sigma - 2 < 0 :=
  pntCarlsonClassicalDensityExponent_sub_two_lt_zero sigma

example :
    pntCarlsonClassicalDensityExponent (1 / 2 : ℝ) = 1 :=
  pntCarlsonClassicalDensityExponent_half_eq_one

end

end PrimeNumberTheorem
