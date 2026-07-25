import ZeroFreeRegion.VinogradovKorobov.FordDoubleHolder
import ZeroFreeRegion.VinogradovKorobov.VinogradovLifting

open scoped BigOperators NNReal

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance fordPowerSumFiberPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Vector of the first `k` positive integer power sums of an ordered
`r`-tuple from `{1, ..., X}`. -/
def vinogradovPowerSumVectorNat
    (k r X : ℕ) (x : Fin r → Fin X) : Fin k → ℕ :=
  fun j ↦ vinogradovPowerSumNat x j

/-- Finite set of power-sum vectors attained by ordered `r`-tuples from
`{1, ..., X}`. -/
noncomputable def vinogradovPowerSumVectorSupport
    (k r X : ℕ) : Finset (Fin k → ℕ) :=
  Finset.univ.image (vinogradovPowerSumVectorNat k r X)

/-- Multiplicity of one attained power-sum vector.  This is Ford's `n(c)`. -/
noncomputable def vinogradovPowerSumMultiplicity
    (k r X : ℕ) (c : Fin k → ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin r → Fin X ↦
    vinogradovPowerSumVectorNat k r X x = c).card

/-- Equality of complete power-sum vectors is exactly the integer Vinogradov
solution predicate. -/
theorem isVinogradovSolutionNat_iff_powerSumVector_eq
    (k r X : ℕ) (x y : Fin r → Fin X) :
    IsVinogradovSolutionNat k r X x y ↔
      vinogradovPowerSumVectorNat k r X x =
        vinogradovPowerSumVectorNat k r X y := by
  constructor
  · intro h
    funext j
    exact h j
  · intro h j
    exact congrFun h j

/-- The total multiplicity of all attained power-sum vectors is the number
`X^r` of ordered input tuples. -/
theorem sum_vinogradovPowerSumMultiplicity_eq
    (k r X : ℕ) :
    ∑ c ∈ vinogradovPowerSumVectorSupport k r X,
      vinogradovPowerSumMultiplicity k r X c = X ^ r := by
  classical
  simpa [vinogradovPowerSumVectorSupport,
    vinogradovPowerSumMultiplicity] using
    (Finset.card_eq_sum_card_image
      (vinogradovPowerSumVectorNat k r X)
      (Finset.univ : Finset (Fin r → Fin X))).symm

/-- The square sum of Ford's multiplicities is the complete Vinogradov mean
value `J_{r,k}(X)`, represented by its exact integer solution count. -/
theorem sum_sq_vinogradovPowerSumMultiplicity_eq_solutionCountNat
    (k r X : ℕ) :
    ∑ c ∈ vinogradovPowerSumVectorSupport k r X,
      vinogradovPowerSumMultiplicity k r X c ^ 2 =
        vinogradovSolutionCountNat k r X := by
  classical
  let support := vinogradovPowerSumVectorSupport k r X
  let vector := vinogradovPowerSumVectorNat k r X
  let multiplicity := vinogradovPowerSumMultiplicity k r X
  have hmaps :
      ∀ x ∈ (Finset.univ : Finset (Fin r → Fin X)),
        vector x ∈ support := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hgroup :=
    Finset.sum_fiberwise_of_maps_to hmaps
      (fun x : Fin r → Fin X ↦ multiplicity (vector x))
  calc
    ∑ c ∈ vinogradovPowerSumVectorSupport k r X,
        vinogradovPowerSumMultiplicity k r X c ^ 2 =
        ∑ c ∈ support,
          ∑ x ∈ (Finset.univ : Finset (Fin r → Fin X)) with
            vector x = c, multiplicity (vector x) := by
      apply Finset.sum_congr rfl
      intro c hc
      have hconst :
          ∀ x ∈ (Finset.univ.filter fun x : Fin r → Fin X ↦
            vector x = c),
            multiplicity (vector x) = multiplicity c := by
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      rw [Finset.sum_const_nat hconst]
      simp only [vector, multiplicity,
        vinogradovPowerSumMultiplicity]
      rw [pow_two]
    _ = ∑ x : Fin r → Fin X, multiplicity (vector x) := hgroup
    _ = vinogradovSolutionCountNat k r X := by
      unfold vinogradovSolutionCountNat
      apply Finset.sum_congr rfl
      intro x hx
      unfold multiplicity vinogradovPowerSumMultiplicity vector
      apply congrArg Finset.card
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [eq_comm] using
        (isVinogradovSolutionNat_iff_powerSumVector_eq
          k r X x y).symm

/-- Ford's equation (5.3) after the two multiplicity sums are identified:
the total mass is `X^r`, while its square mass is the complete integer
Vinogradov mean value.  The final amplitude moment is deliberately left
abstract for the later incomplete-system estimate. -/
theorem nnnorm_fordPowerSumWeightedAmplitude_pow_le
    (k r s X : ℕ) (hs : 1 ≤ s)
    (amplitude : (Fin k → ℕ) → ℂ) :
    ‖∑ c ∈ vinogradovPowerSumVectorSupport k r X,
        (vinogradovPowerSumMultiplicity k r X c : ℂ) * amplitude c‖₊ ^
          (2 * s) ≤
      (X ^ r : ℝ≥0) ^ (2 * (s - 1)) *
        (vinogradovSolutionCountNat k r X : ℝ≥0) *
          ∑ c ∈ vinogradovPowerSumVectorSupport k r X,
            ‖amplitude c‖₊ ^ (2 * s) := by
  have hmass :
      ∑ c ∈ vinogradovPowerSumVectorSupport k r X,
        (vinogradovPowerSumMultiplicity k r X c : ℝ≥0) =
          (X ^ r : ℝ≥0) := by
    exact_mod_cast sum_vinogradovPowerSumMultiplicity_eq k r X
  have hsq :
      ∑ c ∈ vinogradovPowerSumVectorSupport k r X,
        (vinogradovPowerSumMultiplicity k r X c : ℝ≥0) ^ 2 =
          (vinogradovSolutionCountNat k r X : ℝ≥0) := by
    exact_mod_cast
      sum_sq_vinogradovPowerSumMultiplicity_eq_solutionCountNat k r X
  simpa only [hmass, hsq] using
    (nnnorm_sum_natCast_mul_pow_le_fordDoubleHolder
      (vinogradovPowerSumVectorSupport k r X)
      (vinogradovPowerSumMultiplicity k r X) amplitude s hs)

end

end ZeroFreeRegion.VinogradovKorobov
