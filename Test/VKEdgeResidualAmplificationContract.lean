import PrimeNumberTheorem.VKEdgeResidualAmplification

open MeasureTheory Set
open PrimeNumberTheorem VKEdgePiOverTwo

#check cosineZeroPair
#check intervalIntegral_cosineZeroPair_sq
#check integral_Icc_cosineZeroPair_sq_le

example
    {m gamma phase a b : ℝ} (hgamma : gamma ≠ 0) :
    (∫ y in a..b, cosineZeroPair m gamma phase y ^ 2) =
      2 * m ^ 2 * (b - a) +
        m ^ 2 / gamma *
          (Real.sin (2 * gamma * b - 2 * phase) -
            Real.sin (2 * gamma * a - 2 * phase)) :=
  intervalIntegral_cosineZeroPair_sq hgamma

example
    {m gamma phase a b : ℝ}
    (hab : a ≤ b) (hgamma : gamma ≠ 0) :
    (∫ y in Icc a b, cosineZeroPair m gamma phase y ^ 2) ≤
      2 * m ^ 2 * (b - a) + 2 * m ^ 2 / |gamma| :=
  integral_Icc_cosineZeroPair_sq_le hab hgamma
