import HardyTheorem.SelbergSqrtZetaSignedRationalCollected
import MathlibAux.FiberwiseNormSq

/-!
# Energy of rationally collected signed Selberg coefficients

Collecting raw signed triples by their positive rational key can enlarge a
single coefficient through collisions.  Fiberwise Cauchy--Schwarz controls
the resulting square energy by the exact fiber multiplicities and raw square
energies.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- The square energy of the rationally collected signed coefficients is
controlled by the exact raw rational-fiber multiplicity budget. -/
theorem sum_normSq_selbergSqrtZetaSignedRationalCoeff_le_fiber_budget
    (N X : ℕ) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) ≤
      ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        ((selbergSqrtZetaSignedRationalFiber N X q).card : ℝ) *
          ∑ p ∈ selbergSqrtZetaSignedRationalFiber N X q,
            Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) := by
  apply MathlibAux.sum_normSq_fiber_le_sum_card_mul_normSq
      (selbergSqrtZetaSignedPhaseSupport N X)
      (selbergSqrtZetaSignedRationalSupport N X)
      selbergSqrtZetaSignedRationalKey
      (selbergSqrtZetaSignedPhaseCoeff X)
  intro p hp
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

end HardyTheorem
