import HardyTheorem.SelbergSqrtZetaSignedRationalEnergy

open HardyTheorem

#check sum_normSq_selbergSqrtZetaSignedRationalCoeff_le_fiber_budget

example (N X : ℕ) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) ≤
      ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        ((selbergSqrtZetaSignedRationalFiber N X q).card : ℝ) *
          ∑ p ∈ selbergSqrtZetaSignedRationalFiber N X q,
            Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) :=
  sum_normSq_selbergSqrtZetaSignedRationalCoeff_le_fiber_budget N X

#print axioms sum_normSq_selbergSqrtZetaSignedRationalCoeff_le_fiber_budget
