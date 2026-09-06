import MathlibAux.HalfWeightedMultiplicity

open scoped BigOperators

namespace MathlibAux

variable {alpha : Type*} [DecidableEq alpha]

example (zeros boundary : Finset alpha) (multiplicity : alpha → ℕ) :
    2 * halfWeightedMultiplicityMass zeros boundary multiplicity =
      2 * fullMultiplicityMass zeros multiplicity -
        boundaryMultiplicityMass zeros boundary multiplicity :=
  two_mul_halfWeightedMultiplicityMass_eq zeros boundary multiplicity

example {zeros larger boundary : Finset alpha} {m n : alpha → ℕ}
    (hzeros : zeros ⊆ larger)
    (hm : ∀ x ∈ zeros, m x ≤ n x) :
    halfWeightedMultiplicityMass zeros boundary m ≤
      halfWeightedMultiplicityMass larger boundary n :=
  halfWeightedMultiplicityMass_mono hzeros hm

example (vZeros productZeros boundary : Finset alpha)
    (vMultiplicity productMultiplicity : alpha → ℕ)
    (hboundary :
      boundaryMultiplicityMass vZeros boundary vMultiplicity ≤
        boundaryMultiplicityMass productZeros boundary productMultiplicity) :
    -2 * fullMultiplicityMass productZeros productMultiplicity +
        boundaryMultiplicityMass vZeros boundary vMultiplicity ≤
      -2 * halfWeightedMultiplicityMass
        productZeros boundary productMultiplicity :=
  neg_two_mul_full_add_boundary_le_neg_two_mul_halfWeighted
    vZeros productZeros boundary vMultiplicity productMultiplicity hboundary

#print axioms two_mul_halfWeightedMultiplicityMass_eq
#print axioms halfWeightedMultiplicityMass_mono
#print axioms neg_two_mul_full_add_boundary_le_neg_two_mul_halfWeighted

end MathlibAux
