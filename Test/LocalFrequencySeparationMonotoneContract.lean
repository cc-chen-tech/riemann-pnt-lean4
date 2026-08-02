import MathlibAux.LocalFrequencySeparationMonotone

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-!
# Contract for local frequency separation monotonicity
-/

#check localFrequencySeparation_mono_of_subset

example {ι : Type*} [DecidableEq ι] {S R : Finset ι} {omega : ι → ℝ} {n : ι}
    (hSR : S ⊆ R) (hS : S.Nontrivial) :
    localFrequencySeparation R omega n ≤
      localFrequencySeparation S omega n :=
  localFrequencySeparation_mono_of_subset hSR hS

end DirichletPolynomial
end PrimeNumberTheorem
