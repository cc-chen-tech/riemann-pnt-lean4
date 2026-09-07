import PrimeNumberTheorem.MWKFCubicAFEProgressionPoisson

open Complex Set
open scoped FourierTransform

namespace PrimeNumberTheorem.MWKFCubic

#check cubicAFEProgressionLattice
#check cubicAFEProgressionLatticeIndex
#check cubicAFEProgressionLattice_index
#check cubicAFEProgressionLattice_toNat_mem
#check tsum_cubicAFEProgressionCutoff_eq_lattice
#check cubicAFEShiftFiberCutoff_poisson

-- Hand-computed lattice points, including negative points and a negative
-- lattice coordinate for a valid positive progression term.
private theorem gcdA_three_five : Nat.gcdA 3 5 = 2 := by
  norm_num [Nat.gcdA, Nat.xgcd, Nat.xgcdAux, Nat.strongRec_eq]

private theorem gcdA_one_one : Nat.gcdA 1 1 = 1 := by
  norm_num [Nat.gcdA, Nat.xgcd, Nat.xgcdAux, Nat.strongRec_eq]

example : cubicAFEProgressionLattice 6 10 (-1) 0 = 2 := by
  norm_num [cubicAFEProgressionLattice, Nat.gcd, gcdA_three_five]
example : cubicAFEProgressionLattice 6 10 (-1) (-1) = -3 := by
  norm_num [cubicAFEProgressionLattice, Nat.gcd, gcdA_three_five]
example : cubicAFEProgressionLatticeIndex 6 10 (-1) 7 = 1 := by
  norm_num [cubicAFEProgressionLatticeIndex, Nat.gcd, gcdA_three_five]
example : cubicAFEProgressionLattice 6 10 (-8) (-2) = 6 := by
  norm_num [cubicAFEProgressionLattice, Nat.gcd, gcdA_three_five]
example : cubicAFEProgressionLatticeIndex 6 10 (-8) 6 = -2 := by
  norm_num [cubicAFEProgressionLatticeIndex, Nat.gcd, gcdA_three_five]

-- No unit condition on delta; modulus one remains included.
example : cubicAFEProgressionLattice 6 10 5 2 = 0 := by
  norm_num [cubicAFEProgressionLattice, Nat.gcd, gcdA_three_five]
example : cubicAFEProgressionLattice 6 10 5 3 = 5 := by
  norm_num [cubicAFEProgressionLattice, Nat.gcd, gcdA_three_five]
-- Mathlib's Bezout coefficient for (1,1) is 1, not the residue representative 0.
example : cubicAFEProgressionLattice 7 7 (-5) 6 = 11 := by
  norm_num [cubicAFEProgressionLattice, Nat.gcd, gcdA_one_one]

-- Forbidden positive first index with a nonpositive second index must
-- contribute zero for the real cutoff kernel.
example (W : CubicTestWeight) (T X V t : ℝ) (χ : CubicProgressionCutoff 6 10 (-8)) :
    cubicAFEProgressionCutoffSummand W T X V χ t 1 = 0 := by
  apply cubicAFEProgressionCutoffSummand_eq_zero_of_not_domain
  norm_num [cubicAFEProgressionDomain, Nat.gcd]

example (W : CubicTestWeight) (T X V t : ℝ) (χ : CubicProgressionCutoff 6 10 (-1)) :
    cubicAFEProgressionCutoffSummand W T X V χ t (-3) = 0 := by
  apply cubicAFEProgressionCutoffSummand_eq_zero_of_not_domain
  norm_num [cubicAFEProgressionDomain, Nat.gcd]

-- The progression-to-lattice equality cannot assume summability or an
-- unproved bijection: its only non-geometric input is e>0.
#check (@tsum_cubicAFEProgressionCutoff_eq_lattice :
  ∀ (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ}, 0 < e →
    ∀ {δ : ℤ} (χ : CubicProgressionCutoff d e δ) (t : ℝ),
      (∑' m : cubicAFEProgression d e δ, cubicAFEProgressionCutoffSummand W T X V χ t m.val) =
        ∑' j : ℤ, cubicAFEProgressionCutoffSummand W T X V χ t
          (cubicAFEProgressionLattice d e δ j : ℝ))

-- End-to-end local Poisson starts with the ORIGINAL full AFE summand,
-- not a substituted function on the real lattice.
#check (@cubicAFEShiftFiberCutoff_poisson :
  ∀ (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ}, 0 < d → 0 < e →
    ∀ {δ : ℤ} (χ : CubicProgressionCutoff d e δ) (t : ℝ), 1 / 2 < X →
      (∑' p : cubicAFEShiftFiber d e δ,
        (χ (p.val.1 + 1 : ℕ) : ℂ) * cubicAFECombinedSummandFinite W T X V d e t p.val) =
        (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' h : ℤ,
          𝓕 (cubicAFEProgressionCutoffSummand W T X V χ t)
            ((h : ℝ) / ((e / Nat.gcd d e : ℕ) : ℝ)) *
            Complex.exp (-2 * (Real.pi : ℂ) * I * (h : ℂ) * (δ : ℂ) *
              (Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e) : ℂ) /
                ((e / Nat.gcd d e : ℕ) : ℂ)))

end PrimeNumberTheorem.MWKFCubic
