import PrimeNumberTheorem.VKEdgePiOverTwoFinitePoleContour

open Complex Polynomial

open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo

#check localizedGaussianWeight_self
#check localizedGaussianWeight_targetPreservingPoleFilter_self
#check localizedGaussianWeight_targetPreservingPoleFilter_eq_zero
#check localizedZeroResidueSum_targetPreservingPoleFilter_eq_multiplicity

example {zeros offsets : Finset ℂ} {w : ℂ} (m : ℝ)
    (hw : w ∈ zeros)
    (hoffsets :
      ∀ rho ∈ zeros, rho ≠ w → rho - w ∈ offsets) :
    localizedZeroResidueSum
        (targetPreservingPoleFilter offsets) w m zeros =
      (analyticOrderNatAt riemannZeta w : ℂ) :=
  localizedZeroResidueSum_targetPreservingPoleFilter_eq_multiplicity
    m hw hoffsets
