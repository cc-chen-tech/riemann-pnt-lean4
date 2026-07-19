import ZeroFreeRegion.VinogradovKorobov.VinogradovLifting

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The degree-`j+1` equation in the weighted Vinogradov system is reduced
modulo `p^((j+1)*a)`.  The increasing modulus is what records the critical
weight `1 + ... + k`, rather than merely the number `k` of equations. -/
def vinogradovWeightedModulus (p a : ℕ) {k : ℕ} (j : Fin k) : ℕ :=
  p ^ ((j.val + 1) * a)

/-- The positive degrees indexed by `Fin k` sum to the triangular critical
weight. -/
theorem sum_vinogradovWeightedDegrees (k : ℕ) :
    (∑ j : Fin k, (j.val + 1)) = k * (k + 1) / 2 := by
  change (∑ j : Fin k, (fun q : ℕ ↦ q + 1) j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun q : ℕ ↦ q + 1) k]
  calc
    _ = (∑ i ∈ Finset.range k, (i + 1)) + 0 := by simp
    _ = ∑ i ∈ Finset.range (k + 1), i :=
      (Finset.sum_range_succ' (fun i : ℕ ↦ i) k).symm
    _ = k * (k + 1) / 2 := by
      rw [Finset.sum_range_id]
      simp [Nat.mul_comm]

/-- The exponents of all degree-dependent moduli add up to `a` times the
critical weight. -/
theorem sum_vinogradovWeightedExponents (a k : ℕ) :
    (∑ j : Fin k, (j.val + 1) * a) =
      a * (k * (k + 1) / 2) := by
  rw [← Finset.sum_mul, sum_vinogradovWeightedDegrees]
  exact Nat.mul_comm _ _

/-- The product of the degree-dependent moduli has exactly the critical
weight exponent. -/
theorem prod_vinogradovWeightedModulus (p a k : ℕ) :
    (∏ j : Fin k, vinogradovWeightedModulus p a j) =
      p ^ (a * (k * (k + 1) / 2)) := by
  calc
    (∏ j : Fin k, vinogradovWeightedModulus p a j) =
        p ^ (∑ j : Fin k, (j.val + 1) * a) := by
      simpa [vinogradovWeightedModulus] using
        (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin k))
          (fun j : Fin k ↦ (j.val + 1) * a) p)
    _ = p ^ (a * (k * (k + 1) / 2)) := by
      rw [sum_vinogradovWeightedExponents]

/-- The `j`-th tuple power sum in its degree-dependent residue ring. -/
def vinogradovWeightedPowerSumMod (p a : ℕ) {k s X : ℕ}
    (x : Fin s → Fin X) (j : Fin k) :
    ZMod (vinogradovWeightedModulus p a j) :=
  vinogradovPowerSumMod (vinogradovWeightedModulus p a j) x j

/-- A pair of tuples satisfies the degree-weighted Vinogradov congruences. -/
def IsVinogradovWeightedSolutionMod (p a k s X : ℕ)
    (x y : Fin s → Fin X) : Prop :=
  ∀ j : Fin k,
    vinogradovWeightedPowerSumMod p a x j =
      vinogradovWeightedPowerSumMod p a y j

/-- Number of ordered solutions to the degree-weighted modular system. -/
noncomputable def vinogradovWeightedSolutionCountMod
    (p a k s X : ℕ) : ℕ := by
  classical
  exact ∑ x : Fin s → Fin X,
    (Finset.univ.filter fun y : Fin s → Fin X ↦
      IsVinogradovWeightedSolutionMod p a k s X x y).card

/-- Casting an ordinary power sum into its degree-dependent residue ring gives
the weighted modular power sum. -/
theorem natCast_vinogradovPowerSumNat_weighted
    (p a : ℕ) {k s X : ℕ} (x : Fin s → Fin X) (j : Fin k) :
    (vinogradovPowerSumNat x j :
        ZMod (vinogradovWeightedModulus p a j)) =
      vinogradovWeightedPowerSumMod p a x j := by
  exact natCast_vinogradovPowerSumNat
    (vinogradovWeightedModulus p a j) x j

/-- Every ordinary integer Vinogradov solution satisfies all weighted
congruences. -/
theorem IsVinogradovSolutionNat.toWeightedMod
    (p a k s X : ℕ) {x y : Fin s → Fin X}
    (h : IsVinogradovSolutionNat k s X x y) :
    IsVinogradovWeightedSolutionMod p a k s X x y := by
  intro j
  rw [← natCast_vinogradovPowerSumNat_weighted,
    ← natCast_vinogradovPowerSumNat_weighted, h j]

/-- Weighted congruences lift back to integer equalities when neither side of
any degree equation reaches its corresponding modulus. -/
theorem IsVinogradovWeightedSolutionMod.toNat_of_lt
    (p a k s X : ℕ) {x y : Fin s → Fin X}
    (h : IsVinogradovWeightedSolutionMod p a k s X x y)
    (hx : ∀ j : Fin k,
      vinogradovPowerSumNat x j < vinogradovWeightedModulus p a j)
    (hy : ∀ j : Fin k,
      vinogradovPowerSumNat y j < vinogradovWeightedModulus p a j) :
    IsVinogradovSolutionNat k s X x y := by
  intro j
  apply nat_eq_of_cast_zmod_eq_of_lt
    (vinogradovWeightedModulus p a j) _ _ (hx j) (hy j)
  simpa only [natCast_vinogradovPowerSumNat_weighted] using h j

/-- Under the degree-by-degree no-wrap condition, the weighted modular system
is equivalent to the ordinary integer Vinogradov system. -/
theorem isVinogradovWeightedSolutionMod_iff_nat_of_scale
    (p a k s X : ℕ)
    (hscale : ∀ j : Fin k,
      s * X ^ (j.val + 1) < vinogradovWeightedModulus p a j)
    (x y : Fin s → Fin X) :
    IsVinogradovWeightedSolutionMod p a k s X x y ↔
      IsVinogradovSolutionNat k s X x y := by
  constructor
  · intro h
    apply h.toNat_of_lt p a k s X
    · intro j
      exact (vinogradovPowerSumNat_le x j).trans_lt (hscale j)
    · intro j
      exact (vinogradovPowerSumNat_le y j).trans_lt (hscale j)
  · exact fun h ↦ h.toWeightedMod p a k s X

/-- In the no-wrap range, weighted modular counting computes the ordinary
Vinogradov mean value exactly. -/
theorem vinogradovWeightedSolutionCountMod_eq_nat_of_scale
    (p a k s X : ℕ)
    (hscale : ∀ j : Fin k,
      s * X ^ (j.val + 1) < vinogradovWeightedModulus p a j) :
    vinogradovWeightedSolutionCountMod p a k s X =
      vinogradovSolutionCountNat k s X := by
  classical
  unfold vinogradovWeightedSolutionCountMod vinogradovSolutionCountNat
  apply Finset.sum_congr rfl
  intro x hx
  apply congrArg Finset.card
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isVinogradovWeightedSolutionMod_iff_nat_of_scale
    p a k s X hscale x y

end

end ZeroFreeRegion.VinogradovKorobov
