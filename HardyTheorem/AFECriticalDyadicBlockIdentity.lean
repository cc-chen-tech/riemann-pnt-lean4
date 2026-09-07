import HardyTheorem.AFECriticalDyadicLevelGaussian

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

/-- The ordinary critical-line Dirichlet sum over one dyadic owner block. -/
noncomputable def dyadicOwnerDirichletPolynomial
    (K j q : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ dyadicOwnerSupport K j q,
    1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)

private theorem dyadicOwnerDirichletPolynomial_mul_mollifier_eq_doubleSum
    (K j q X : ℕ) (t : ℝ) :
    dyadicOwnerDirichletPolynomial K j q t *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) =
      ∑ n ∈ dyadicOwnerSupport K j q, ∑ d ∈ Finset.Icc 1 X,
        (selbergMoebiusCoeff X d : ℂ) *
          (1 / (((n * d : ℕ) : ℂ)) ^ ((1 / 2 : ℂ) + I * t)) := by
  unfold dyadicOwnerDirichletPolynomial selbergMoebiusMollifier
    selbergMollifier
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  simp only [one_div, mul_inv_rev]
  ring

private theorem dyadicOwnerDoubleSum_eq_collected
    (K j q X : ℕ) (s : ℂ) :
    (∑ n ∈ dyadicOwnerSupport K j q, ∑ d ∈ Finset.Icc 1 X,
        (selbergMoebiusCoeff X d : ℂ) *
          (1 / (((n * d : ℕ) : ℂ)) ^ s)) =
      ∑ k ∈ Finset.Icc 1 (2 ^ K * X),
        dyadicMollifiedBlockCoeff K j X k q *
          (1 / (k : ℂ) ^ s) := by
  classical
  let P := (dyadicOwnerSupport K j q).product (Finset.Icc 1 X)
  let T := Finset.Icc 1 (2 ^ K * X)
  let key : ℕ × ℕ → ℕ := fun p => p.1 * p.2
  let term : ℕ × ℕ → ℂ := fun p =>
    (selbergMoebiusCoeff X p.2 : ℂ) * (1 / (key p : ℂ) ^ s)
  have hmaps : ∀ p ∈ P, key p ∈ T := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hpN, hpD⟩
    have hpN' := (Finset.mem_filter.mp hpN).1
    rcases Finset.mem_Ico.mp hpN' with ⟨hp1, hpK⟩
    rcases Finset.mem_Icc.mp hpD with ⟨hp2, hpX⟩
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hp1 hp2,
      Nat.mul_le_mul (Nat.le_of_lt hpK) hpX⟩
  calc
    (∑ n ∈ dyadicOwnerSupport K j q, ∑ d ∈ Finset.Icc 1 X,
        (selbergMoebiusCoeff X d : ℂ) *
          (1 / (((n * d : ℕ) : ℂ)) ^ s)) = ∑ p ∈ P, term p := by
      symm
      simpa [P, term, key] using
        (Finset.sum_product (dyadicOwnerSupport K j q) (Finset.Icc 1 X)
          term)
    _ = ∑ k ∈ T, ∑ p ∈ P.filter (fun p => key p = k), term p := by
      exact (Finset.sum_fiberwise_of_maps_to hmaps term).symm
    _ = ∑ k ∈ Finset.Icc 1 (2 ^ K * X),
        dyadicMollifiedBlockCoeff K j X k q *
          (1 / (k : ℂ) ^ s) := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (∑ p ∈ P.filter (fun p => key p = k), term p) =
            ∑ p ∈ P.filter (fun p => key p = k),
              (selbergMoebiusCoeff X p.2 : ℂ) *
                (1 / (k : ℂ) ^ s) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hkey : p.1 * p.2 = k := by
            simpa only [key] using (Finset.mem_filter.mp hp).2
          dsimp only [term, key]
          rw [hkey]
        _ = (∑ p ∈ P.filter (fun p => key p = k),
              (selbergMoebiusCoeff X p.2 : ℂ)) *
                (1 / (k : ℂ) ^ s) := by
          rw [Finset.sum_mul]
        _ = dyadicMollifiedBlockCoeff K j X k q *
                (1 / (k : ℂ) ^ s) := by
          rw [dyadicMollifiedBlockCoeff_eq_ownerPairs]

private theorem inv_nat_cpow_half_eq_inv_sqrt_block (n : ℕ) :
    ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ = ((Real.sqrt n : ℝ) : ℂ)⁻¹ := by
  congr 1
  calc
    (n : ℂ) ^ (1 / 2 : ℂ) =
        (((n : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
      exact (Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ n) (1 / 2)).symm
    _ = ((Real.sqrt n : ℝ) : ℂ) := by rw [Real.sqrt_eq_rpow]

/-- Exact moving-block identity: the raw owner Dirichlet sum times the
Selberg mollifier is the collected logarithmic-frequency block polynomial
used in the Gaussian level estimate. -/
theorem dyadicOwnerDirichletPolynomial_mul_mollifier_eq_blockPolynomial
    (K j q X : ℕ) (t : ℝ) :
    dyadicOwnerDirichletPolynomial K j q t *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) =
      dyadicMollifiedCriticalBlockPolynomial K j X q t := by
  rw [dyadicOwnerDirichletPolynomial_mul_mollifier_eq_doubleSum,
    dyadicOwnerDoubleSum_eq_collected]
  unfold dyadicMollifiedCriticalBlockPolynomial MathlibAux.exponentialPolynomial
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : k ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hk).1
  rw [inv_nat_cpow_criticalLine_eq_exp hk0 t,
    inv_nat_cpow_half_eq_inv_sqrt_block]
  unfold dyadicMollifiedCriticalBlockCoeff
  push_cast
  ring

end AFE
end HardyTheorem
