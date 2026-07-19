import ZeroFreeRegion.VinogradovKorobov.VinogradovWeightedBounds
import ZeroFreeRegion.VinogradovKorobov.VinogradovSymmetry

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Difference of two unrestricted integer power sums at degree `m`. -/
def vinogradovPowerSumDifferenceInt {s : ℕ}
    (x y : Fin s → ℤ) (m : ℕ) : ℤ :=
  (∑ i, x i ^ m) - ∑ i, y i ^ m

/-- The degree-zero power-sum difference vanishes because the two tuples have
the same length. -/
@[simp] theorem vinogradovPowerSumDifferenceInt_zero {s : ℕ}
    (x y : Fin s → ℤ) :
    vinogradovPowerSumDifferenceInt x y 0 = 0 := by
  simp [vinogradovPowerSumDifferenceInt]

/-- Exact triangular binomial expansion after a common affine substitution.
The outer degree `n` couples only to inner power-sum differences of degrees at
most `n`; the degree-`m` contribution carries the scale factor `q^m`. -/
theorem vinogradovPowerSumDifferenceInt_affine {s : ℕ}
    (ξ q : ℤ) (x y : Fin s → ℤ) (n : ℕ) :
    vinogradovPowerSumDifferenceInt
        (fun i ↦ ξ + q * x i) (fun i ↦ ξ + q * y i) n =
      ∑ m ∈ Finset.range (n + 1),
        (n.choose m : ℤ) * ξ ^ (n - m) * q ^ m *
          vinogradovPowerSumDifferenceInt x y m := by
  unfold vinogradovPowerSumDifferenceInt
  simp_rw [show ∀ z : ℤ, ξ + q * z = q * z + ξ by intro z; ring,
    add_pow, mul_pow]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_range] at hm
  calc
    (∑ i, (q ^ m * x i ^ m * ξ ^ (n - m) * (n.choose m : ℤ) -
        q ^ m * y i ^ m * ξ ^ (n - m) * (n.choose m : ℤ))) =
      ∑ i, ((n.choose m : ℤ) * ξ ^ (n - m) * q ^ m) *
        (x i ^ m - y i ^ m) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (n.choose m : ℤ) * ξ ^ (n - m) * q ^ m *
        ∑ i, (x i ^ m - y i ^ m) := by
          rw [Finset.mul_sum]

/-- Integer version of the degree-weighted Vinogradov congruence system. -/
def IsVinogradovWeightedSolutionInt (p a k s : ℕ)
    (x y : Fin s → ℤ) : Prop :=
  ∀ j : Fin k,
    vinogradovPowerSumInt x j ≡ vinogradovPowerSumInt y j
      [ZMOD (p : ℤ) ^ ((j.val + 1) * a)]

/-- The weighted integer system is equivalently the vanishing, degree by
degree, of the corresponding power-sum differences. -/
theorem isVinogradovWeightedSolutionInt_iff_modEq
    (p a k s : ℕ) (x y : Fin s → ℤ) :
    IsVinogradovWeightedSolutionInt p a k s x y ↔
      ∀ j : Fin k,
        vinogradovPowerSumDifferenceInt x y (j.val + 1) ≡ 0
          [ZMOD (p : ℤ) ^ ((j.val + 1) * a)] := by
  constructor
  · intro h j
    simpa [vinogradovPowerSumDifferenceInt, vinogradovPowerSumInt] using
      (h j).sub (Int.ModEq.refl (vinogradovPowerSumInt y j))
  · intro h j
    have hj := (h j).add_right (vinogradovPowerSumInt y j)
    simpa [vinogradovPowerSumDifferenceInt, vinogradovPowerSumInt] using hj

/-- After putting both tuples in the same affine residue class, the weighted
system is exactly the triangular family of binomial congruences. -/
theorem isVinogradovWeightedSolutionInt_affine_iff_triangular
    (p a k s : ℕ) (ξ q : ℤ) (x y : Fin s → ℤ) :
    IsVinogradovWeightedSolutionInt p a k s
        (fun i ↦ ξ + q * x i) (fun i ↦ ξ + q * y i) ↔
      ∀ j : Fin k,
        (∑ m ∈ Finset.range (j.val + 2),
          ((j.val + 1).choose m : ℤ) * ξ ^ (j.val + 1 - m) * q ^ m *
            vinogradovPowerSumDifferenceInt x y m) ≡ 0
          [ZMOD (p : ℤ) ^ ((j.val + 1) * a)] := by
  rw [isVinogradovWeightedSolutionInt_iff_modEq]
  constructor <;> intro h j
  · simpa [vinogradovPowerSumDifferenceInt_affine] using h j
  · simpa [vinogradovPowerSumDifferenceInt_affine] using h j

/-- Direct affine rescaling is false for the degree-weighted system.  The
outer tuples `(1, 1)` and `(3, 3)` solve the degree-one congruence modulo `4`
and the degree-two congruence modulo `16`, but after removing the common
residue `1` and dividing by `2`, the tuples `(0, 0)` and `(1, 1)` fail the
degree-two congruence modulo `4`. -/
theorem weightedAffineRescale_counterexample :
    IsVinogradovWeightedSolutionInt 2 2 2 2
        (fun _ ↦ 1) (fun _ ↦ 3) ∧
      ¬ IsVinogradovWeightedSolutionInt 2 1 2 2
        (fun _ ↦ 0) (fun _ ↦ 1) := by
  constructor
  · intro j
    fin_cases j <;>
      norm_num [vinogradovPowerSumInt, Int.ModEq]
  · intro h
    have hdegreeTwo := h (1 : Fin 2)
    norm_num [vinogradovPowerSumInt, Int.ModEq] at hdegreeTwo

end

end ZeroFreeRegion.VinogradovKorobov
