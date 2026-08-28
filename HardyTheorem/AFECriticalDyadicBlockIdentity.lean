import HardyTheorem.AFECriticalDyadicBlock

/-!
# Exact owner-pair form of a dyadic AFE block coefficient

The coefficient used in the levelwise energy estimate is rewritten by first
restricting the zeta index to one owner block and only then forming its
product with the mollifier support.  This is the finite arithmetic core of
the moving-prefix polynomial identity.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem
namespace AFE

/-- Positive zeta indices in the ambient prefix which belong to owner `q` at
dyadic level `j`. -/
def dyadicOwnerSupport (K j q : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (2 ^ K)).filter (fun n => n / 2 ^ j = q)

/-- The previously collected block coefficient is exactly the coefficient
obtained from the product of the owner support and the mollifier support. -/
theorem dyadicMollifiedBlockCoeff_eq_ownerPairs
    (K j X k q : ℕ) :
    dyadicMollifiedBlockCoeff K j X k q =
      ∑ p ∈ ((dyadicOwnerSupport K j q).product (Finset.Icc 1 X)).filter
          (fun p => p.1 * p.2 = k),
        (selbergMoebiusCoeff X p.2 : ℂ) := by
  unfold dyadicMollifiedBlockCoeff dyadicMollifiedFactorPairs
    dyadicOwnerSupport
  apply Finset.sum_congr
  · ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpOuter, howner⟩
      rcases Finset.mem_filter.mp hpOuter with ⟨hpProd, hprod⟩
      rcases Finset.mem_product.mp hpProd with ⟨hpN, hpD⟩
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hpN, howner⟩, hpD⟩,
        hprod⟩
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpProd, hprod⟩
      rcases Finset.mem_product.mp hpProd with ⟨hpN, hpD⟩
      rcases Finset.mem_filter.mp hpN with ⟨hpIco, howner⟩
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hpIco, hpD⟩, hprod⟩,
        howner⟩
  · intro p hp
    rfl

end AFE
end HardyTheorem
