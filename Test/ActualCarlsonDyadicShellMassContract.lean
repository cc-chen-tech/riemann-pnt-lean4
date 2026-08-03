import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonDyadicShellMass

namespace PrimeNumberTheorem

open Filter

noncomputable section

-- Seven public definitions.

example (sigma : ℝ) : ℝ :=
  pntCarlsonClassicalDensityExponent sigma

example (sigma : ℝ) : ℝ :=
  pntCarlsonDyadicReciprocalRatio sigma

example (C sigma : ℝ) (n : ℕ) : ℝ :=
  pntCarlsonDyadicLogFourthMajorant C sigma n

example (count : ℕ → ℝ) (n : ℕ) : ℝ :=
  pntDyadicReciprocalWeightedCount count n

example (sigma : ℝ) (n : ℕ) : ℝ :=
  actualCarlsonDyadicCount sigma n

example (sigma : ℝ) (n : ℕ) : Finset ℂ :=
  actualCarlsonDyadicZeroShell sigma n

example (sigma : ℝ) (n : ℕ) : ℝ :=
  actualCarlsonDyadicShellMultiplicityMass sigma n

-- Seventeen public theorems.

example {sigma : ℝ} (hhalf : 1 / 2 < sigma) :
    pntCarlsonClassicalDensityExponent sigma < 1 :=
  pntCarlsonClassicalDensityExponent_lt_one hhalf

example (sigma : ℝ) :
    0 < pntCarlsonDyadicReciprocalRatio sigma :=
  pntCarlsonDyadicReciprocalRatio_pos sigma

example {sigma : ℝ} (hhalf : 1 / 2 < sigma) :
    pntCarlsonDyadicReciprocalRatio sigma < 1 :=
  pntCarlsonDyadicReciprocalRatio_lt_one hhalf

example {C sigma : ℝ} (hhalf : 1 / 2 < sigma) :
    Summable (pntCarlsonDyadicLogFourthMajorant C sigma) :=
  summable_pntCarlsonDyadicLogFourthMajorant hhalf

example {count : ℕ → ℝ} (hcount : ∀ n, 0 ≤ count n) (n : ℕ) :
    0 ≤ pntDyadicReciprocalWeightedCount count n :=
  pntDyadicReciprocalWeightedCount_nonneg hcount n

example {count : ℕ → ℝ} {C sigma : ℝ}
    (hcount : ∀ n, 0 ≤ count n)
    (hbound :
      ∀ᶠ n : ℕ in atTop,
        pntDyadicReciprocalWeightedCount count n ≤
          pntCarlsonDyadicLogFourthMajorant C sigma n)
    (hhalf : 1 / 2 < sigma) :
    Summable (pntDyadicReciprocalWeightedCount count) :=
  summable_pntDyadicReciprocalWeightedCount_of_eventually_le
    hcount hbound hhalf

example (sigma : ℝ) (n : ℕ) :
    0 ≤ actualCarlsonDyadicCount sigma n :=
  actualCarlsonDyadicCount_nonneg sigma n

example (q : ℝ) (n : ℕ) :
    (((2 : ℝ) ^ n) ^ q) / (2 : ℝ) ^ n =
      Real.exp ((q - 1) * Real.log 2) ^ n :=
  dyadic_rpow_div_eq_carlsonDyadicReciprocalRatio q n

example (C sigma : ℝ) (n : ℕ) :
    (C * ‖
        (((2 : ℝ) ^ n) ^
            pntCarlsonClassicalDensityExponent sigma) *
          (Real.log ((2 : ℝ) ^ n)) ^ 4‖) /
        (2 : ℝ) ^ n =
      pntCarlsonDyadicLogFourthMajorant
        (C * (Real.log 2) ^ 4) sigma n :=
  carlsonDyadicModel_div_eq_logFourthMajorant C sigma n

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma) :
    ∀ᶠ n : ℕ in atTop,
      pntDyadicReciprocalWeightedCount
          (actualCarlsonDyadicCount sigma) n ≤
        pntCarlsonDyadicLogFourthMajorant
          (certificate.C * (Real.log 2) ^ 4) sigma n :=
  certificate.eventually_actualCarlsonDyadicReciprocalCount_le

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    (hhalf : 1 / 2 < sigma) :
    Summable
      (pntDyadicReciprocalWeightedCount
        (actualCarlsonDyadicCount sigma)) :=
  certificate.summable_actualCarlsonDyadicReciprocalCount hhalf

example {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    Summable
      (pntDyadicReciprocalWeightedCount
        (actualCarlsonDyadicCount sigma)) :=
  exists_summable_actualCarlsonDyadicReciprocalCount hhalf hone

example {sigma : ℝ} {n : ℕ} {rho : ℂ}
    (hrho : rho ∈ actualCarlsonDyadicZeroShell sigma n) :
    (2 : ℝ) ^ n < rho.im :=
  actualCarlsonDyadicZeroShell_im_gt hrho

example (sigma : ℝ) (n : ℕ) :
    0 ≤ actualCarlsonDyadicShellMultiplicityMass sigma n :=
  actualCarlsonDyadicShellMultiplicityMass_nonneg sigma n

example (sigma : ℝ) (n : ℕ) :
    actualCarlsonDyadicShellMultiplicityMass sigma n ≤
      actualCarlsonDyadicCount sigma (n + 1) / (2 : ℝ) ^ n :=
  actualCarlsonDyadicShellMultiplicityMass_le_count_div sigma n

example (sigma : ℝ) (n : ℕ) :
    actualCarlsonDyadicCount sigma (n + 1) / (2 : ℝ) ^ n =
      2 * pntDyadicReciprocalWeightedCount
        (actualCarlsonDyadicCount sigma) (n + 1) :=
  actualCarlsonDyadicCount_div_lower_eq_two_mul_weighted_succ sigma n

example {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    Summable (actualCarlsonDyadicShellMultiplicityMass sigma) :=
  summable_actualCarlsonDyadicShellMultiplicityMass hhalf hone

end

end PrimeNumberTheorem
