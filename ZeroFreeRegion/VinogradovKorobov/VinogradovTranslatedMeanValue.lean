import ZeroFreeRegion.VinogradovKorobov.VinogradovLowDegreePsi
import ZeroFreeRegion.VinogradovKorobov.VinogradovMainEstimate
import ZeroFreeRegion.VinogradovKorobov.VinogradovPrimePowerMultiBlock

open scoped Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

private instance primePower_neZero
    (p n : ℕ) [Fact p.Prime] : NeZero (p ^ n) :=
  ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

/-- One-based integer representatives of a tuple in `{1, ..., X}`. -/
def vinogradovFinTupleInt {s X : ℕ} (x : Fin s → Fin X) : Fin s → ℤ :=
  fun i ↦ (((x i).val + 1 : ℕ) : ℤ)

/-- Finite tuple pairs satisfying the translated-spaced polynomial system
before the far-scale elimination.  This is the counting surface to which the
algebraic transition can be applied pointwise. -/
noncomputable def vinogradovTranslatedSpacedSolutionPairSet
    (p c k r a b γ s X : ℕ) [Fact p.Prime]
    (ω : ℤ) (ψ : Fin r → Polynomial ℤ) :
    Finset ((Fin s → Fin X) × (Fin s → Fin X)) := by
  classical
  exact Finset.univ.filter fun xy ↦
      IsVinogradovPolynomialCongruenceSystem p ((k - r + 1) * b)
        (fun row ↦
          vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
            (vinogradovSpacedPolynomial p c k
              (vinogradovBinomialPoint k r row) (ψ row)))
        (fun i ↦ (p : ℤ) ^ a * vinogradovFinTupleInt xy.1 i)
        (fun i ↦ (p : ℤ) ^ a * vinogradovFinTupleInt xy.2 i)

/-- Membership unfolds to the translated-spaced congruence system on the
one-based integer representatives of the two tuples. -/
theorem mem_vinogradovTranslatedSpacedSolutionPairSet_iff
    (p c k r a b γ s X : ℕ) [Fact p.Prime]
    (ω : ℤ) (ψ : Fin r → Polynomial ℤ)
    (x y : Fin s → Fin X) :
    (x, y) ∈ vinogradovTranslatedSpacedSolutionPairSet
        p c k r a b γ s X ω ψ ↔
      IsVinogradovPolynomialCongruenceSystem p ((k - r + 1) * b)
        (fun row ↦
          vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
            (vinogradovSpacedPolynomial p c k
              (vinogradovBinomialPoint k r row) (ψ row)))
        (fun i ↦ (p : ℤ) ^ a * vinogradovFinTupleInt x i)
        (fun i ↦ (p : ℤ) ^ a * vinogradovFinTupleInt y i) := by
  classical
  simp [vinogradovTranslatedSpacedSolutionPairSet]

/-- Every translated-spaced solution pair is a solution of the ordinary
degree-`r` Vinogradov system modulo the residual far scale.  This is the
set-level bridge from the algebraic elimination to finite mean values. -/
theorem vinogradovTranslatedSpacedSolutionPairSet_subset_farScale
    (p c k r a b γ s X : ℕ) [Fact p.Prime]
    (hc : 0 < c) (hrk : r ≤ k) (hkp : k < p)
    (hambient : 0 < (k - r + 1) * b)
    (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (ψ : Fin r → Polynomial ℤ) :
    vinogradovTranslatedSpacedSolutionPairSet
        p c k r a b γ s X ω ψ ⊆
      vinogradovSolutionPairSetMod
        (p ^ vinogradovFarScale k r a b γ) r s X := by
  classical
  intro xy hxy
  rcases xy with ⟨x, y⟩
  rw [mem_vinogradovSolutionPairSetMod_iff]
  apply (isVinogradovSolutionMod_iff_powerSumInt_modEq
    (p ^ vinogradovFarScale k r a b γ) r s X x y).mpr
  have hsystem :=
    (mem_vinogradovTranslatedSpacedSolutionPairSet_iff
      p c k r a b γ s X ω ψ x y).mp hxy
  have hfar :=
    vinogradovUnscaledTranslatedSpacedSystem_to_farScale_via_unitTwist
      p c k r a b γ hc hrk hkp hambient hγa hbudget htail
        ω hω ψ (vinogradovFinTupleInt x) (vinogradovFinTupleInt y)
        hsystem
  intro i
  have hi := (hfar i).add_right
    (vinogradovPowerSumInt (vinogradovFinTupleInt y) i)
  simpa only [vinogradovPowerSumDifferenceInt, vinogradovPowerSumInt,
    sub_add_cancel, zero_add] using hi

/-- The translated-spaced solution count is bounded by the ordinary modular
Vinogradov solution count at the far scale. -/
theorem card_vinogradovTranslatedSpacedSolutionPairSet_le_solutionCount
    (p c k r a b γ s X : ℕ) [Fact p.Prime]
    (hc : 0 < c) (hrk : r ≤ k) (hkp : k < p)
    (hambient : 0 < (k - r + 1) * b)
    (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (ψ : Fin r → Polynomial ℤ) :
    (vinogradovTranslatedSpacedSolutionPairSet
        p c k r a b γ s X ω ψ).card ≤
      vinogradovSolutionCountMod
        (p ^ vinogradovFarScale k r a b γ) r s X := by
  classical
  calc
    (vinogradovTranslatedSpacedSolutionPairSet
        p c k r a b γ s X ω ψ).card ≤
        (vinogradovSolutionPairSetMod
          (p ^ vinogradovFarScale k r a b γ) r s X).card :=
      Finset.card_le_card
        (vinogradovTranslatedSpacedSolutionPairSet_subset_farScale
          p c k r a b γ s X hc hrk hkp hambient hγa hbudget htail
            ω hω ψ)
    _ = vinogradovSolutionCountMod
          (p ^ vinogradovFarScale k r a b γ) r s X :=
      card_vinogradovSolutionPairSetMod _ _ _ _

/-- The same counting transition stated directly against the normalized
finite Fourier moment at the far scale. -/
theorem card_vinogradovTranslatedSpacedSolutionPairSet_le_normalizedMoment
    (p c k r a b γ s X : ℕ) [Fact p.Prime]
    (hc : 0 < c) (hrk : r ≤ k) (hkp : k < p)
    (hambient : 0 < (k - r + 1) * b)
    (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (ψ : Fin r → Polynomial ℤ) :
    ((vinogradovTranslatedSpacedSolutionPairSet
        p c k r a b γ s X ω ψ).card : ℝ) ≤
      ‖normalizedVinogradovMomentMod
        (p ^ vinogradovFarScale k r a b γ) r s X‖ := by
  rw [normalizedVinogradovMomentMod_eq_solutionCount]
  exact_mod_cast
    card_vinogradovTranslatedSpacedSolutionPairSet_le_solutionCount
      p c k r a b γ s X hc hrk hkp hambient hγa hbudget htail
        ω hω ψ

/-- Any proved degree-`r` Vinogradov mean-value estimate now bounds the
translated-spaced solution set, provided the far-scale modulus is large
enough to lift the modular moment without wraparound.  The mean-value
estimate remains an explicit input; this theorem is the verified bridge to
it, not a proof of the VMVT main conjecture. -/
theorem card_vinogradovTranslatedSpacedSolutionPairSet_le_of_meanValueEstimate
    (p c k r a b γ s X : ℕ) [Fact p.Prime] {ε C : ℝ}
    (hc : 0 < c) (hrk : r ≤ k) (hkp : k < p)
    (hambient : 0 < (k - r + 1) * b)
    (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (ψ : Fin r → Polynomial ℤ)
    (hest : VinogradovMeanValueEstimate r s ε C)
    (hX : 1 ≤ X)
    (hscale : s * X ^ r < p ^ vinogradovFarScale k r a b γ) :
    ((vinogradovTranslatedSpacedSolutionPairSet
        p c k r a b γ s X ω ψ).card : ℝ) ≤
      C * Real.rpow (X : ℝ) ε *
        ((X : ℝ) ^ s +
          (X : ℝ) ^ (2 * s - vinogradovCriticalWeight r)) := by
  exact (card_vinogradovTranslatedSpacedSolutionPairSet_le_normalizedMoment
    p c k r a b γ s X hc hrk hkp hambient hγa hbudget htail
      ω hω ψ).trans
    (norm_normalizedVinogradovMomentMod_le_of_meanValueEstimate
      (p ^ vinogradovFarScale k r a b γ) r s X hest hX hscale)

/-- At an integral prime-power far scale, the translated-spaced count feeds
directly into the existing multiblock rank stratification.  The first term is
the branch where every selected block is singular; the second is the union of
the first nonsingular strata.  This is an explicit finite counting bound, not
yet the efficient-congruencing iteration needed for the full VMVT. -/
theorem card_vinogradovTranslatedSpacedSolutionPairSet_le_primePowerStrata
    (p c k r a b γ q blocks n : ℕ) [Fact p.Prime]
    (hc : 0 < c) (hr : 0 < r) (hrk : r ≤ k) (hkp : k < p)
    (hambient : 0 < (k - r + 1) * b)
    (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hfar : vinogradovFarScale k r a b γ = n + 1)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (ψ : Fin r → Polynomial ℤ) :
    (vinogradovTranslatedSpacedSolutionPairSet p c k r a b γ
        (blocks * r + q) (p ^ (n + 1)) ω ψ).card ≤
      ((p ^ r - p.descFactorial r) ^ blocks * p ^ q *
          p ^ (blocks * r + q)) *
        (p ^ (2 * (blocks * r + q))) ^ n +
      ((p ^ r) ^ blocks -
          (p ^ r - p.descFactorial r) ^ blocks) *
        (p ^ q * p ^ (blocks * r + q) *
          (p ^ (r + 2 * ((blocks - 1) * r + q))) ^ n) := by
  calc
    (vinogradovTranslatedSpacedSolutionPairSet p c k r a b γ
        (blocks * r + q) (p ^ (n + 1)) ω ψ).card ≤
      vinogradovSolutionCountMod
        (p ^ vinogradovFarScale k r a b γ) r
          (blocks * r + q) (p ^ (n + 1)) :=
      card_vinogradovTranslatedSpacedSolutionPairSet_le_solutionCount
        p c k r a b γ (blocks * r + q) (p ^ (n + 1))
          hc hrk hkp hambient hγa hbudget htail ω hω ψ
    _ = vinogradovSolutionCountMod
        (p ^ (n + 1)) r (blocks * r + q) (p ^ (n + 1)) := by
      rw [hfar]
    _ ≤ ((p ^ r - p.descFactorial r) ^ blocks * p ^ q *
            p ^ (blocks * r + q)) *
          (p ^ (2 * (blocks * r + q))) ^ n +
        ((p ^ r) ^ blocks -
            (p ^ r - p.descFactorial r) ^ blocks) *
          (p ^ q * p ^ (blocks * r + q) *
            (p ^ (r + 2 * ((blocks - 1) * r + q))) ^ n) :=
      vinogradovPrimePowerMultiBlockSolutionCount_le_strata
        p r q blocks n hr (hrk.trans_lt hkp)

/-- In the diagonal range `s ≤ r`, the far-scale bridge closes
unconditionally with the elementary `s! X^s` Vinogradov bound.  This supplies
an exact finite endpoint for later conditioning recurrences. -/
theorem card_vinogradovTranslatedSpacedSolutionPairSet_le_diagonal
    (p c k r a b γ s X : ℕ) [Fact p.Prime]
    (hc : 0 < c) (hrk : r ≤ k) (hkp : k < p)
    (hambient : 0 < (k - r + 1) * b)
    (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (ψ : Fin r → Polynomial ℤ)
    (hsr : s ≤ r) (hX : 1 ≤ X)
    (hscale : s * X ^ r < p ^ vinogradovFarScale k r a b γ) :
    (vinogradovTranslatedSpacedSolutionPairSet
        p c k r a b γ s X ω ψ).card ≤
      s.factorial * X ^ s := by
  calc
    (vinogradovTranslatedSpacedSolutionPairSet
        p c k r a b γ s X ω ψ).card ≤
      vinogradovSolutionCountMod
        (p ^ vinogradovFarScale k r a b γ) r s X :=
      card_vinogradovTranslatedSpacedSolutionPairSet_le_solutionCount
        p c k r a b γ s X hc hrk hkp hambient hγa hbudget htail
          ω hω ψ
    _ = vinogradovSolutionCountNat r s X :=
      vinogradovSolutionCountMod_eq_nat_of_topScale
        (p ^ vinogradovFarScale k r a b γ) r s X hX hscale
    _ ≤ s.factorial * X ^ s :=
      vinogradovSolutionCountNat_le_diagonal r s X hsr

end

end ZeroFreeRegion.VinogradovKorobov
