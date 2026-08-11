import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCarlsonCertificateBlock

namespace PrimeNumberTheorem

open Filter

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    (B x tau : ℝ) (n : ℕ) :
    actualCubicCarlsonCertificateBlockMajorant certificate B x tau n =
      (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
        (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
          ((certificate.C *
              (((2 : ℝ) ^ (n + 1)) ^
                  pntCarlsonClassicalDensityExponent sigma *
                Real.log ((2 : ℝ) ^ (n + 1)) ^ 4)) /
            ((2 : ℝ) ^ n) ^ 2)) := rfl

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {B x tau : ℝ} (hB : 0 ≤ B) (hx : 1 ≤ x) :
    ∀ᶠ n : ℕ in atTop,
      actualCubicDyadicCountMajorant B x sigma tau n ≤
        actualCubicCarlsonCertificateBlockMajorant certificate B x tau n :=
  certificate.eventually_actualCubicDyadicCountMajorant_le hB hx

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {x tau : ℝ} (hx : 1 ≤ x) (S : Finset ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ n : ℕ in atTop,
        4 ≤ (2 : ℝ) ^ n →
          actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
            actualCubicCarlsonCertificateBlockMajorant certificate B x tau n :=
  actualCubicDyadicStripSquareCapacityExcluding_le_certificateBlock
    certificate hx S

example (sigma : ℝ) :
    pntCarlsonClassicalDensityExponent sigma - 6 ≤ -5 :=
  actualCubicCarlsonCertificatePolynomialExponent_le_neg_five sigma

end PrimeNumberTheorem
