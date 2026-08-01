import PrimeNumberTheorem.VKEdgeHighZeroGaussianEnergy

open Complex Filter
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Actual-zeta dyadic unit-bucket Gaussian capacity

This file is the unconditional actual-zeta component available for the E2
route.  Its `k`-th block consists of the existing unit ordinate buckets with
indices in `[2^k, 2^(k+1))`; the upper endpoint is represented as
`2^(k+1) - 1` in `Finset.Icc`.  The bound is a whole-Gram Schur estimate, so
it retains all cross-bucket interactions without a spacing assumption.

It deliberately does not claim the target-normalized right-higher,
`S`-relative energy bound.  That statement additionally needs a proved
comparison from the E0 coefficient/weight geometry to these unweighted
actual-zeta bucket masses.
-/

/-- Gaussian interaction energy of the actual-zeta unit-ordinate buckets in
the dyadic index block `[2^k, 2^(k+1))`. -/
noncomputable def zeroOrdinateDyadicGaussianEnergy (k : ℕ) (m : ℝ) : ℝ :=
  zeroOrdinateBucketGaussianEnergy (2 ^ k) (2 ^ (k + 1) - 1) m

/-- Whole-Gram Gaussian Schur capacity for one actual-zeta dyadic
unit-bucket block.  The right side retains the quantitative square mass of
each unit bucket; no Gram, tail, or Sharp hypothesis is assumed. -/
theorem zeroOrdinateDyadicGaussianEnergy_le
    (k : ℕ) {m : ℝ} (hm : 1 ≤ m) :
    zeroOrdinateDyadicGaussianEnergy k m ≤
      MathlibAux.gaussianBucketSchurConstant *
        ∑ n ∈ Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1),
          zeroOrdinateUnitBucketCoefficientMass n ^ 2 := by
  exact zeroOrdinateBucketGaussianEnergy_le
    (2 ^ k) (2 ^ (k + 1) - 1) hm

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
