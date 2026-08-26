import HardyTheorem.SelbergSqrtZetaInverseMajorant

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# Selberg's S13 estimate: the fixed-product coefficient bound

The first exact step in Selberg's estimate (S13) groups a pair `(d, d₁)` by
its product `D = d d₁`.  The absolute mass on every divisor antidiagonal is
at most one.  This is the finite coefficient statement behind the later
Euler-product estimate.
-/

/-- Absolute square-root-zeta coefficient mass on the divisor pairs of `D`. -/
noncomputable def selbergS13DivisorPairMass (D : ℕ) : ℝ :=
  ∑ p ∈ D.divisorsAntidiagonal,
    |selbergSqrtZetaCoeff p.1 * selbergSqrtZetaCoeff p.2|

theorem selbergS13DivisorPairMass_nonneg (D : ℕ) :
    0 ≤ selbergS13DivisorPairMass D := by
  unfold selbergS13DivisorPairMass
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- For a fixed product `D`, the total absolute coefficient mass is at most
one.  The proof is exactly `|α| ≤ α'` followed by `α' * α' = ζ`. -/
theorem selbergS13DivisorPairMass_le_one (D : ℕ) :
    selbergS13DivisorPairMass D ≤ 1 := by
  unfold selbergS13DivisorPairMass
  calc
    (∑ p ∈ D.divisorsAntidiagonal,
        |selbergSqrtZetaCoeff p.1 * selbergSqrtZetaCoeff p.2|) ≤
        ∑ p ∈ D.divisorsAntidiagonal,
          selbergSqrtZetaInverseCoeff p.1 *
            selbergSqrtZetaInverseCoeff p.2 := by
      apply Finset.sum_le_sum
      intro p _hp
      rw [abs_mul]
      exact mul_le_mul
        (abs_selbergSqrtZetaCoeff_le_inverseCoeff p.1)
        (abs_selbergSqrtZetaCoeff_le_inverseCoeff p.2)
        (abs_nonneg _)
        (selbergSqrtZetaInverseCoeff_nonneg p.1)
    _ = (selbergSqrtZetaInverseCoeff *
          selbergSqrtZetaInverseCoeff) D := by
      rw [ArithmeticFunction.mul_apply]
    _ = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) D := by
      rw [selbergSqrtZetaInverseCoeff_mul_self]
    _ ≤ 1 := by
      by_cases hD : D = 0
      · subst D
        simp
      · simp [ArithmeticFunction.natCoe_apply,
          ArithmeticFunction.zeta_apply_ne hD]

/-- A natural number is supported on the prime set of `rho`. -/
def selbergS13SupportedBy (rho n : ℕ) : Prop :=
  n.primeFactors ⊆ rho.primeFactors

/-- The fixed-product mass restricted to pairs whose coordinates use only
primes dividing `rho`. -/
noncomputable def selbergS13RestrictedDivisorPairMass
    (rho D : ℕ) : ℝ :=
  by
    classical
    exact
      ∑ p ∈ D.divisorsAntidiagonal.filter fun p =>
          selbergS13SupportedBy rho p.1 ∧ selbergS13SupportedBy rho p.2,
        |selbergSqrtZetaCoeff p.1 * selbergSqrtZetaCoeff p.2|

theorem selbergS13RestrictedDivisorPairMass_nonneg (rho D : ℕ) :
    0 ≤ selbergS13RestrictedDivisorPairMass rho D := by
  classical
  unfold selbergS13RestrictedDivisorPairMass
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem selbergS13RestrictedDivisorPairMass_le_one (rho D : ℕ) :
    selbergS13RestrictedDivisorPairMass rho D ≤ 1 := by
  classical
  calc
    selbergS13RestrictedDivisorPairMass rho D ≤
        selbergS13DivisorPairMass D := by
      unfold selbergS13RestrictedDivisorPairMass selbergS13DivisorPairMass
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro p _hp _hnot
        exact abs_nonneg _
    _ ≤ 1 := selbergS13DivisorPairMass_le_one D

/-- Admissible products `D`: positive, bounded, divisible by `rho`, and
supported on the prime set of `rho`. -/
noncomputable def selbergS13AdmissibleProducts (rho B : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 B).filter fun D =>
    rho ∣ D ∧ selbergS13SupportedBy rho D

/-- The finite grouped version of the left side of (S13). -/
noncomputable def selbergS13FiniteGroupedMass (rho B : ℕ) : ℝ :=
  ∑ D ∈ selbergS13AdmissibleProducts rho B,
    selbergS13RestrictedDivisorPairMass rho D / (D : ℝ)

/-- After grouping by `D = d d₁`, the coefficient mass disappears and only
the reciprocal sum over admissible products remains. -/
theorem selbergS13FiniteGroupedMass_le_reciprocalSum (rho B : ℕ) :
    selbergS13FiniteGroupedMass rho B ≤
      ∑ D ∈ selbergS13AdmissibleProducts rho B,
        (D : ℝ)⁻¹ := by
  classical
  unfold selbergS13FiniteGroupedMass
  apply Finset.sum_le_sum
  intro D hD
  have hDnat : 0 < D :=
    lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp
        (Finset.mem_filter.mp
          (show D ∈ (Finset.Icc 1 B).filter fun D =>
            rho ∣ D ∧ selbergS13SupportedBy rho D by
              simpa [selbergS13AdmissibleProducts] using hD)).1).1
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast hDnat
  rw [div_eq_mul_inv]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right
      (selbergS13RestrictedDivisorPairMass_le_one rho D)
      (le_of_lt (inv_pos.mpr hDpos))

end HardyTheorem
