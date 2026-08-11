import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCarlsonCertificateSummability

namespace PrimeNumberTheorem

open Filter

example {H : ℝ} (hH6 : 6 ≤ H) (hlogOne : 1 ≤ Real.log H) :
    1 + Real.log (H + 6) ≤ 3 * Real.log H :=
  one_add_log_add_six_le_three_mul_log hH6 hlogOne

example (q : ℝ) (n : ℕ) :
    (((2 : ℝ) ^ (n + 1)) ^ q) / (((2 : ℝ) ^ n) ^ 6) =
      64 * pntDyadicReciprocalDensityRatio (q - 5) ^ (n + 1) :=
  dyadic_succ_rpow_div_sixth_eq_actualCubicCarlsonRatio q n

example (n : ℕ) :
    Real.log ((2 : ℝ) ^ (n + 1)) ^ 5 =
      (Real.log 2) ^ 5 * (((n + 1 : ℕ) : ℝ) ^ 5) :=
  log_dyadic_succ_pow_five n

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {B x tau : ℝ} (hB : 0 ≤ B) (hx : 1 ≤ x) :
    ∀ᶠ n : ℕ in atTop,
      actualCubicCarlsonCertificateBlockMajorant certificate B x tau n ≤
        actualCubicCarlsonDyadicLogFifthMajorant
          (192 * B * certificate.C * x ^ (2 * tau) * (Real.log 2) ^ 5)
          sigma n :=
  certificate.eventually_actualCubicCertificateBlock_le_logFifth hB hx

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {x tau : ℝ} (hx : 1 ≤ x) (S : Finset ℂ) :
    Summable (fun n =>
      actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S) :=
  certificate.summable_actualCubicDyadicStripSquareCapacityExcluding hx S

end PrimeNumberTheorem
