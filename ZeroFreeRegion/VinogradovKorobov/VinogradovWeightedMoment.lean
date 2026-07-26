import ZeroFreeRegion.VinogradovKorobov.VinogradovWeighted

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance weightedPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- A coefficient vector for the weighted system: the coefficient of degree
`j+1` lives in its own ring modulo `p^((j+1)*a)`. -/
abbrev VinogradovWeightedCoefficient (p a k : ℕ) :=
  (j : Fin k) → ZMod (vinogradovWeightedModulus p a j)

instance vinogradovWeightedModulus_neZero
    (p a : ℕ) [Fact p.Prime] {k : ℕ} (j : Fin k) :
    NeZero (vinogradovWeightedModulus p a j) :=
  ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

/-- The weighted coefficient space has the critical-weight cardinality. -/
theorem card_vinogradovWeightedCoefficient
    (p a k : ℕ) [Fact p.Prime] :
    Fintype.card (VinogradovWeightedCoefficient p a k) =
      p ^ (a * (k * (k + 1) / 2)) := by
  rw [Fintype.card_pi]
  simp only [ZMod.card]
  exact prod_vinogradovWeightedModulus p a k

/-- One term of the weighted complete Weyl sum.  It is the product of the
degree-wise additive characters because the coefficient rings have different
moduli. -/
noncomputable def vinogradovWeightedPhaseTerm
    (p a : ℕ) [Fact p.Prime] {k X : ℕ}
    (c : VinogradovWeightedCoefficient p a k) (m : Fin X) : ℂ :=
  ∏ j : Fin k,
    ZMod.stdAddChar
      (c j * (((m.val + 1 : ℕ) :
        ZMod (vinogradovWeightedModulus p a j)) ^ (j.val + 1)))

/-- Every weighted phase term has unit norm. -/
theorem norm_vinogradovWeightedPhaseTerm
    (p a : ℕ) [Fact p.Prime] {k X : ℕ}
    (c : VinogradovWeightedCoefficient p a k) (m : Fin X) :
    ‖vinogradovWeightedPhaseTerm p a c m‖ = 1 := by
  simp [vinogradovWeightedPhaseTerm]

/-- Complete Weyl sum for a degree-weighted coefficient vector. -/
noncomputable def vinogradovWeightedWeylSum
    (p a k X : ℕ) [Fact p.Prime]
    (c : VinogradovWeightedCoefficient p a k) : ℂ :=
  ∑ m : Fin X, vinogradovWeightedPhaseTerm p a c m

/-- A weighted complete Weyl sum has the trivial norm bound `X`. -/
theorem norm_vinogradovWeightedWeylSum_le
    (p a k X : ℕ) [Fact p.Prime]
    (c : VinogradovWeightedCoefficient p a k) :
    ‖vinogradovWeightedWeylSum p a k X c‖ ≤ X := by
  unfold vinogradovWeightedWeylSum
  calc
    ‖∑ m : Fin X, vinogradovWeightedPhaseTerm p a c m‖ ≤
        ∑ m : Fin X, ‖vinogradovWeightedPhaseTerm p a c m‖ :=
      norm_sum_le _ _
    _ = X := by simp [norm_vinogradovWeightedPhaseTerm]

/-- Product of weighted phase terms along an ordered tuple. -/
noncomputable def vinogradovWeightedTuplePhase
    (p a : ℕ) [Fact p.Prime] {k s X : ℕ}
    (c : VinogradovWeightedCoefficient p a k)
    (x : Fin s → Fin X) : ℂ :=
  ∏ i : Fin s, vinogradovWeightedPhaseTerm p a c (x i)

/-- Expanding the `s`-th power of the weighted Weyl sum gives one tuple phase
for each ordered `s`-tuple. -/
theorem vinogradovWeightedWeylSum_pow
    (p a k s X : ℕ) [Fact p.Prime]
    (c : VinogradovWeightedCoefficient p a k) :
    vinogradovWeightedWeylSum p a k X c ^ s =
      ∑ x : Fin s → Fin X,
        vinogradovWeightedTuplePhase p a c x := by
  classical
  rw [vinogradovWeightedWeylSum, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro x
  rfl

/-- Reordering the tuple and degree products identifies the accumulated phase
with the degree-wise weighted power sums. -/
theorem vinogradovWeightedTuplePhase_eq_prod_powerSum
    (p a : ℕ) [Fact p.Prime] {k s X : ℕ}
    (c : VinogradovWeightedCoefficient p a k)
    (x : Fin s → Fin X) :
    vinogradovWeightedTuplePhase p a c x =
      ∏ j : Fin k,
        ZMod.stdAddChar
          (c j * vinogradovWeightedPowerSumMod p a x j) := by
  classical
  unfold vinogradovWeightedTuplePhase vinogradovWeightedPhaseTerm
  rw [Finset.prod_comm]
  apply Fintype.prod_congr
  intro j
  calc
    (∏ i : Fin s,
        ZMod.stdAddChar
          (c j * (((x i).val + 1 : ℕ) :
            ZMod (vinogradovWeightedModulus p a j)) ^ (j.val + 1))) =
        ZMod.stdAddChar
          (∑ i : Fin s,
            c j * (((x i).val + 1 : ℕ) :
              ZMod (vinogradovWeightedModulus p a j)) ^ (j.val + 1)) := by
      simpa using
        (prod_stdAddChar_eq_sum (vinogradovWeightedModulus p a j)
          (Finset.univ : Finset (Fin s))
          (fun i ↦ c j * (((x i).val + 1 : ℕ) :
            ZMod (vinogradovWeightedModulus p a j)) ^ (j.val + 1)))
    _ = ZMod.stdAddChar
          (c j * vinogradovWeightedPowerSumMod p a x j) := by
      congr 1
      simp [vinogradovWeightedPowerSumMod, vinogradovPowerSumMod,
        Finset.mul_sum]

/-- Pairing a tuple phase with the conjugate of another tuple phase produces
the character of every weighted power-sum difference. -/
theorem vinogradovWeightedTuplePhase_mul_star_eq_prod_difference
    (p a : ℕ) [Fact p.Prime] {k s X : ℕ}
    (c : VinogradovWeightedCoefficient p a k)
    (x y : Fin s → Fin X) :
    vinogradovWeightedTuplePhase p a c x *
        (starRingEnd ℂ) (vinogradovWeightedTuplePhase p a c y) =
      ∏ j : Fin k,
        ZMod.stdAddChar
          (c j * (vinogradovWeightedPowerSumMod p a x j -
            vinogradovWeightedPowerSumMod p a y j)) := by
  classical
  rw [vinogradovWeightedTuplePhase_eq_prod_powerSum,
    vinogradovWeightedTuplePhase_eq_prod_powerSum, map_prod,
    ← Finset.prod_mul_distrib]
  apply Fintype.prod_congr
  intro j
  rw [conj_stdAddChar, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- A complete sum over the dependent weighted coefficient type factors into
one orthogonality sum for each degree. -/
theorem sum_vinogradovWeightedCoefficient_pairing
    (p a k : ℕ) [Fact p.Prime]
    (d : (j : Fin k) → ZMod (vinogradovWeightedModulus p a j)) :
    (∑ c : VinogradovWeightedCoefficient p a k,
        ∏ j : Fin k, ZMod.stdAddChar (c j * d j)) =
      ∏ j : Fin k,
        ∑ r : ZMod (vinogradovWeightedModulus p a j),
          ZMod.stdAddChar (r * d j) := by
  classical
  exact (Fintype.prod_sum
    (fun j (r : ZMod (vinogradovWeightedModulus p a j)) ↦
      ZMod.stdAddChar (r * d j))).symm

/-- Product of degree-wise normalized character averages detecting all
weighted Vinogradov congruences. -/
noncomputable def vinogradovWeightedSolutionSelector
    (p a k s X : ℕ) [Fact p.Prime]
    (x y : Fin s → Fin X) : ℂ :=
  ∏ j : Fin k,
    ((vinogradovWeightedModulus p a j : ℂ)⁻¹ *
      ∑ c : ZMod (vinogradovWeightedModulus p a j),
        ZMod.stdAddChar
          (c * (vinogradovWeightedPowerSumMod p a x j -
            vinogradovWeightedPowerSumMod p a y j)))

/-- The normalized weighted coefficient average of a tuple pair is exactly
the weighted modular solution selector. -/
theorem normalized_sum_weightedTuplePair_eq_selector
    (p a k s X : ℕ) [Fact p.Prime]
    (x y : Fin s → Fin X) :
    (∏ j : Fin k,
        (vinogradovWeightedModulus p a j : ℂ)⁻¹) *
        ∑ c : VinogradovWeightedCoefficient p a k,
          (vinogradovWeightedTuplePhase p a c x *
            (starRingEnd ℂ) (vinogradovWeightedTuplePhase p a c y)) =
      vinogradovWeightedSolutionSelector p a k s X x y := by
  simp_rw [vinogradovWeightedTuplePhase_mul_star_eq_prod_difference]
  rw [sum_vinogradovWeightedCoefficient_pairing]
  simp [vinogradovWeightedSolutionSelector, Finset.prod_mul_distrib]

/-- The weighted Fourier selector is one precisely on weighted modular
solutions, and zero otherwise. -/
theorem vinogradovWeightedSolutionSelector_eq_indicator
    (p a k s X : ℕ) [Fact p.Prime]
    (x y : Fin s → Fin X) :
    vinogradovWeightedSolutionSelector p a k s X x y =
      if IsVinogradovWeightedSolutionMod p a k s X x y then 1 else 0 := by
  classical
  simp only [vinogradovWeightedSolutionSelector,
    normalized_sum_stdAddChar_mul]
  by_cases h : IsVinogradovWeightedSolutionMod p a k s X x y
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro j hj
    rw [if_pos]
    exact sub_eq_zero.mpr (h j)
  · rw [if_neg h]
    simp only [IsVinogradovWeightedSolutionMod, not_forall] at h
    obtain ⟨j, hj⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [if_neg]
    exact sub_ne_zero.mpr hj

/-- Summing the weighted selector over both tuples counts exactly the weighted
modular solutions. -/
theorem sum_vinogradovWeightedSolutionSelector_eq_count
    (p a k s X : ℕ) [Fact p.Prime] :
    ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
      vinogradovWeightedSolutionSelector p a k s X x y =
        (vinogradovWeightedSolutionCountMod p a k s X : ℂ) := by
  classical
  simp_rw [vinogradovWeightedSolutionSelector_eq_indicator]
  simp [vinogradovWeightedSolutionCountMod, Finset.sum_boole]

/-- The conjugate `s`-th power expands over a second tuple with conjugated
weighted tuple phase. -/
theorem conj_vinogradovWeightedWeylSum_pow
    (p a k s X : ℕ) [Fact p.Prime]
    (c : VinogradovWeightedCoefficient p a k) :
    (starRingEnd ℂ) (vinogradovWeightedWeylSum p a k X c) ^ s =
      ∑ y : Fin s → Fin X,
        (starRingEnd ℂ) (vinogradovWeightedTuplePhase p a c y) := by
  rw [← map_pow, vinogradovWeightedWeylSum_pow, map_sum]

/-- Normalized complete `2s`-th moment of the degree-weighted Weyl sums. -/
noncomputable def normalizedVinogradovWeightedMomentMod
    (p a k s X : ℕ) [Fact p.Prime] : ℂ :=
  (∏ j : Fin k,
      (vinogradovWeightedModulus p a j : ℂ)⁻¹) *
    ∑ c : VinogradovWeightedCoefficient p a k,
      vinogradovWeightedWeylSum p a k X c ^ s *
        (starRingEnd ℂ) (vinogradovWeightedWeylSum p a k X c) ^ s

private theorem normalizedWeightedMoment_reindex
    (p a k s X : ℕ) [Fact p.Prime] :
    normalizedVinogradovWeightedMomentMod p a k s X =
      ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
        ((∏ j : Fin k,
            (vinogradovWeightedModulus p a j : ℂ)⁻¹) *
          ∑ c : VinogradovWeightedCoefficient p a k,
            (vinogradovWeightedTuplePhase p a c x *
              (starRingEnd ℂ) (vinogradovWeightedTuplePhase p a c y))) := by
  classical
  unfold normalizedVinogradovWeightedMomentMod
  simp_rw [vinogradovWeightedWeylSum_pow,
    conj_vinogradovWeightedWeylSum_pow]
  calc
    (∏ j : Fin k,
          (vinogradovWeightedModulus p a j : ℂ)⁻¹) *
        ∑ c : VinogradovWeightedCoefficient p a k,
          ((∑ x : Fin s → Fin X,
              vinogradovWeightedTuplePhase p a c x) *
            ∑ y : Fin s → Fin X,
              (starRingEnd ℂ) (vinogradovWeightedTuplePhase p a c y)) =
      ∑ c : VinogradovWeightedCoefficient p a k,
        ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
          (∏ j : Fin k,
              (vinogradovWeightedModulus p a j : ℂ)⁻¹) *
            (vinogradovWeightedTuplePhase p a c x *
              (starRingEnd ℂ) (vinogradovWeightedTuplePhase p a c y)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Fintype.sum_congr
      intro c
      rw [Finset.sum_comm]
    _ = ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
        ∑ c : VinogradovWeightedCoefficient p a k,
          (∏ j : Fin k,
              (vinogradovWeightedModulus p a j : ℂ)⁻¹) *
            (vinogradovWeightedTuplePhase p a c x *
              (starRingEnd ℂ) (vinogradovWeightedTuplePhase p a c y)) := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro x
      rw [Finset.sum_comm]
    _ = ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
        ((∏ j : Fin k,
            (vinogradovWeightedModulus p a j : ℂ)⁻¹) *
          ∑ c : VinogradovWeightedCoefficient p a k,
            (vinogradovWeightedTuplePhase p a c x *
              (starRingEnd ℂ) (vinogradovWeightedTuplePhase p a c y))) := by
      simp only [Finset.mul_sum]

/-- Finite weighted Vinogradov mean-value identity: the normalized complete
Weyl moment equals the number of solutions to the degree-weighted congruence
system. -/
theorem normalizedVinogradovWeightedMomentMod_eq_solutionCount
    (p a k s X : ℕ) [Fact p.Prime] :
    normalizedVinogradovWeightedMomentMod p a k s X =
      (vinogradovWeightedSolutionCountMod p a k s X : ℂ) := by
  rw [normalizedWeightedMoment_reindex]
  simp_rw [normalized_sum_weightedTuplePair_eq_selector]
  exact sum_vinogradovWeightedSolutionSelector_eq_count p a k s X

/-- In the no-wrap range, the normalized weighted Weyl moment computes the
ordinary integer Vinogradov mean value. -/
theorem normalizedVinogradovWeightedMomentMod_eq_natCount_of_scale
    (p a k s X : ℕ) [Fact p.Prime]
    (hscale : ∀ j : Fin k,
      s * X ^ (j.val + 1) < vinogradovWeightedModulus p a j) :
    normalizedVinogradovWeightedMomentMod p a k s X =
      (vinogradovSolutionCountNat k s X : ℂ) := by
  rw [normalizedVinogradovWeightedMomentMod_eq_solutionCount,
    vinogradovWeightedSolutionCountMod_eq_nat_of_scale
      p a k s X hscale]

/-- The product of complex normalization factors is the inverse critical
weight modulus. -/
theorem prod_vinogradovWeightedModulus_inv_natCast
    (p a k : ℕ) [Fact p.Prime] :
    (∏ j : Fin k,
        (vinogradovWeightedModulus p a j : ℂ)⁻¹) =
      (p ^ (a * (k * (k + 1) / 2)) : ℂ)⁻¹ := by
  rw [Finset.prod_inv_distrib]
  congr 1
  exact_mod_cast prod_vinogradovWeightedModulus p a k

end

end ZeroFreeRegion.VinogradovKorobov
