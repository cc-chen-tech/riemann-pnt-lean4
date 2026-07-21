import MathlibAux.GcdLcmQuadratic

namespace Test.GcdLcmQuadraticContract

#check MathlibAux.sum_reciprocal_lcm_quadratic_eq_totient_squares

example (a : ℕ → ℝ) (M : ℕ) :
    (∑ r ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 M,
        a r * a s * (Nat.lcm r s : ℝ)⁻¹) =
      ∑ d ∈ Finset.Icc 1 M, (Nat.totient d : ℝ) *
        (∑ r ∈ (Finset.Icc 1 M).filter (fun r => d ∣ r),
          a r * (r : ℝ)⁻¹) ^ 2 :=
  MathlibAux.sum_reciprocal_lcm_quadratic_eq_totient_squares a M

#print axioms MathlibAux.sum_reciprocal_lcm_quadratic_eq_totient_squares

end Test.GcdLcmQuadraticContract
