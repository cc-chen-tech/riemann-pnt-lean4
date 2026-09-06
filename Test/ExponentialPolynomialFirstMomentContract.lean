import MathlibAux.ExponentialPolynomialFirstMoment

open Complex

namespace MathlibAux

#check norm_intervalIntegral_exponentialPolynomial_sub_distinguished_le

example {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (i0 : ι)
    (hi0 : i0 ∈ s) (hcoeff : coeff i0 = 1) (hfreq0 : freq i0 = 0)
    (hfreq : ∀ i ∈ s.erase i0, freq i ≠ 0) (a b : ℝ) :
    ‖∫ t in a..b,
        (exponentialPolynomial s coeff freq t - 1)‖ ≤
      ∑ i ∈ s.erase i0, 2 * ‖coeff i‖ / |freq i| :=
  norm_intervalIntegral_exponentialPolynomial_sub_distinguished_le
    s coeff freq i0 hi0 hcoeff hfreq0 hfreq

#print axioms norm_intervalIntegral_exponentialPolynomial_sub_distinguished_le

end MathlibAux
