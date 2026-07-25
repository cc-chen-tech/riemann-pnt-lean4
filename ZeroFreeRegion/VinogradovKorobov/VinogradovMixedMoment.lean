import ZeroFreeRegion.VinogradovKorobov.VinogradovIntegerSelector
import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedConditionedSolution

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance mixedMomentPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The pair of main tuples lies in the fixed residue class `xi` modulo
`p^a`. -/
def VinogradovMixedMainResidueMem
    (p a r t X Y : ℕ) (xi : ℤ)
    (z : VinogradovMixedTuplePairs r t X Y) : Prop :=
  (∀ i, Int.ModEq ((p : ℤ) ^ a) xi
      (vinogradovFinTupleInt z.1.1 i)) ∧
    ∀ i, Int.ModEq ((p : ℤ) ^ a) xi
      (vinogradovFinTupleInt z.1.2 i)

/-- The integer Weyl sum restricted to the one-based indices in the residue
class `xi` modulo `p^a`. -/
noncomputable def vinogradovMixedMainWeylSum
    (p a Q k X : ℕ) [NeZero Q] (xi : ℤ)
    (c : Fin k → ZMod Q) : ℂ :=
  ∑ n : Fin X,
    if Int.ModEq ((p : ℤ) ^ a) xi (((n.val + 1 : ℕ) : ℤ)) then
      ZMod.stdAddChar
        (vinogradovIntPhaseMod Q c (((n.val + 1 : ℕ) : ℤ)))
    else 0

/-- Expanding a power of the restricted main Weyl sum keeps exactly the
ordered tuples whose every coordinate lies in the prescribed residue class. -/
theorem vinogradovMixedMainWeylSum_pow
    (p a Q k r X : ℕ) [NeZero Q] (xi : ℤ)
    (c : Fin k → ZMod Q) :
    vinogradovMixedMainWeylSum p a Q k X xi c ^ r =
      ∑ x : Fin r → Fin X,
        if (∀ i, Int.ModEq ((p : ℤ) ^ a) xi
            (vinogradovFinTupleInt x i)) then
          ZMod.stdAddChar
            (vinogradovIntTuplePhaseMod Q c (vinogradovFinTupleInt x))
        else 0 := by
  classical
  rw [vinogradovMixedMainWeylSum, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro x
  by_cases hres : ∀ i, Int.ModEq ((p : ℤ) ^ a) xi
      (vinogradovFinTupleInt x i)
  · rw [if_pos hres]
    have hpoint : ∀ i, Int.ModEq ((p : ℤ) ^ a) xi
        ((((x i).val + 1 : ℕ) : ℤ)) := by
      exact hres
    simp_rw [if_pos (hpoint _)]
    simpa [vinogradovIntTuplePhaseMod, vinogradovFinTupleInt] using
      (prod_stdAddChar_eq_sum Q (Finset.univ : Finset (Fin r))
        (fun i ↦ vinogradovIntPhaseMod Q c
          ((((x i).val + 1 : ℕ) : ℤ))))
  · rw [if_neg hres]
    simp only [not_forall] at hres
    obtain ⟨i, hi⟩ := hres
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [if_neg]
    exact hi

/-- The conjugate power of the restricted main Weyl sum expands with the
opposite tuple phase and the same residue restriction. -/
theorem conj_vinogradovMixedMainWeylSum_pow
    (p a Q k r X : ℕ) [NeZero Q] (xi : ℤ)
    (c : Fin k → ZMod Q) :
    (starRingEnd ℂ) (vinogradovMixedMainWeylSum p a Q k X xi c) ^ r =
      ∑ x : Fin r → Fin X,
        if (∀ i, Int.ModEq ((p : ℤ) ^ a) xi
            (vinogradovFinTupleInt x i)) then
          ZMod.stdAddChar
            (-vinogradovIntTuplePhaseMod Q c (vinogradovFinTupleInt x))
        else 0 := by
  rw [← map_pow, vinogradovMixedMainWeylSum_pow, map_sum]
  apply Fintype.sum_congr
  intro x
  by_cases hres : ∀ i, Int.ModEq ((p : ℤ) ^ a) xi
      (vinogradovFinTupleInt x i)
  · rw [if_pos hres, conj_stdAddChar, if_pos hres]
  · rw [if_neg hres, map_zero, if_neg hres]

/-- The left joined tuple for the mixed Fourier system: the main left tuple
is paired with the affine reconstruction of the second restricted tail. -/
def vinogradovMixedJoinedLeft
    (p b r t X Y : ℕ) (eta : ℤ)
    (z : VinogradovMixedTuplePairs r t X Y) : Fin (r + t) → ℤ :=
  vinogradovJoinTuple (vinogradovFinTupleInt z.1.1)
    (fun i ↦ eta + (p : ℤ) ^ b * vinogradovFinTupleInt z.2.2 i)

/-- The right joined tuple for the mixed Fourier system: the main right tuple
is paired with the affine reconstruction of the first restricted tail. -/
def vinogradovMixedJoinedRight
    (p b r t X Y : ℕ) (eta : ℤ)
    (z : VinogradovMixedTuplePairs r t X Y) : Fin (r + t) → ℤ :=
  vinogradovJoinTuple (vinogradovFinTupleInt z.1.2)
    (fun i ↦ eta + (p : ℤ) ^ b * vinogradovFinTupleInt z.2.1 i)

/-- The common-modulus Fourier selector restricted to the prescribed main
residue class. -/
noncomputable def vinogradovMixedModSolutionSelector
    (p B a b k r t X Y : ℕ) [NeZero (p ^ B)] (xi eta : ℤ)
    (z : VinogradovMixedTuplePairs r t X Y) : ℂ :=
  if VinogradovMixedMainResidueMem p a r t X Y xi z then
    vinogradovIntSolutionSelector (p ^ B) k (r + t)
      (vinogradovMixedJoinedLeft p b r t X Y eta z)
      (vinogradovMixedJoinedRight p b r t X Y eta z)
  else 0

/-- The restricted mixed Fourier selector is exactly the indicator of the
modular mixed conditioned solution predicate. -/
theorem vinogradovMixedModSolutionSelector_eq_indicator
    (p B a b k r t X Y : ℕ) [NeZero (p ^ B)] (xi eta : ℤ)
    (z : VinogradovMixedTuplePairs r t X Y) :
    vinogradovMixedModSolutionSelector
        p B a b k r t X Y xi eta z =
      if VinogradovMixedModConditionedSolutionMem
          p B a b k r t X Y xi eta z then 1 else 0 := by
  classical
  unfold vinogradovMixedModSolutionSelector
  by_cases hres : VinogradovMixedMainResidueMem p a r t X Y xi z
  · rw [if_pos hres, vinogradovIntSolutionSelector_eq_indicator]
    by_cases hmixed : IsVinogradovMixedAffineCongruenceInt p B b k r t eta
        (vinogradovFinTupleInt z.1.1) (vinogradovFinTupleInt z.1.2)
        (vinogradovFinTupleInt z.2.1) (vinogradovFinTupleInt z.2.2)
    · have hjoin : IsVinogradovSolutionIntMod (p ^ B) k (r + t)
          (vinogradovMixedJoinedLeft p b r t X Y eta z)
          (vinogradovMixedJoinedRight p b r t X Y eta z) := by
        simpa only [vinogradovMixedJoinedLeft,
          vinogradovMixedJoinedRight] using
          (isVinogradovMixedAffineCongruenceInt_iff_joinTuple
            p B b k r t eta _ _ _ _).mp hmixed
      rw [if_pos hjoin, if_pos]
      exact ⟨hres.1, hres.2, hmixed⟩
    · have hjoin : ¬ IsVinogradovSolutionIntMod (p ^ B) k (r + t)
          (vinogradovMixedJoinedLeft p b r t X Y eta z)
          (vinogradovMixedJoinedRight p b r t X Y eta z) := by
        intro h
        apply hmixed
        exact (isVinogradovMixedAffineCongruenceInt_iff_joinTuple
          p B b k r t eta _ _ _ _).mpr (by
            simpa only [vinogradovMixedJoinedLeft,
              vinogradovMixedJoinedRight] using h)
      rw [if_neg hjoin, if_neg]
      exact fun h ↦ hmixed h.2.2
  · rw [if_neg hres, if_neg]
    exact fun h ↦ hres ⟨h.1, h.2.1⟩

/-- The expanded normalized mixed coefficient average.  It is the finite
Fourier form obtained after expanding the two main and two restricted Weyl
blocks into ordered tuples. -/
noncomputable def normalizedVinogradovMixedModExpandedMoment
    (p B a b k r t X Y : ℕ) [NeZero (p ^ B)]
    (xi eta : ℤ) : ℂ :=
  ∑ z : VinogradovMixedTuplePairs r t X Y,
    if VinogradovMixedMainResidueMem p a r t X Y xi z then
      ((p ^ B : ℕ) : ℂ)⁻¹ ^ k *
        ∑ c : Fin k → ZMod (p ^ B),
          (ZMod.stdAddChar
              (vinogradovIntTuplePhaseMod (p ^ B) c
                (vinogradovMixedJoinedLeft p b r t X Y eta z)) *
            ZMod.stdAddChar
              (-vinogradovIntTuplePhaseMod (p ^ B) c
                (vinogradovMixedJoinedRight p b r t X Y eta z)))
    else 0

/-- Orthogonality identifies the expanded normalized mixed moment with the
cardinality of the common-modulus mixed conditioned solution set. -/
theorem normalizedVinogradovMixedModExpandedMoment_eq_solutionSetCard
    (p B a b k r t X Y : ℕ) [NeZero (p ^ B)]
    (xi eta : ℤ) :
    normalizedVinogradovMixedModExpandedMoment
        p B a b k r t X Y xi eta =
      (vinogradovMixedModConditionedSolutionSet
        p B a b k r t X Y xi eta).card := by
  classical
  unfold normalizedVinogradovMixedModExpandedMoment
  simp_rw [normalized_sum_intTuplePair_eq_selector]
  change
    (∑ z : VinogradovMixedTuplePairs r t X Y,
      vinogradovMixedModSolutionSelector
        p B a b k r t X Y xi eta z) = _
  simp_rw [vinogradovMixedModSolutionSelector_eq_indicator]
  simp [vinogradovMixedModConditionedSolutionSet, Finset.sum_boole]

/-- The affine integer represented by a restricted-tail index. -/
def vinogradovMixedTailValue
    (p b Y : ℕ) (eta : ℤ) (n : Fin Y) : ℤ :=
  eta + (p : ℤ) ^ b * (((n.val + 1 : ℕ) : ℤ))

/-- Four separated tuple characters recombine into the crossed pair of joined
tuple characters used by the mixed congruence system. -/
theorem stdAddChar_mixedBlocks
    (Q : ℕ) [NeZero Q] {k r t : ℕ}
    (c : Fin k → ZMod Q) (x y : Fin r → ℤ) (u v : Fin t → ℤ) :
    ZMod.stdAddChar (vinogradovIntTuplePhaseMod Q c x) *
        ZMod.stdAddChar (-vinogradovIntTuplePhaseMod Q c y) *
        ZMod.stdAddChar (-vinogradovIntTuplePhaseMod Q c u) *
        ZMod.stdAddChar (vinogradovIntTuplePhaseMod Q c v) =
      ZMod.stdAddChar
          (vinogradovIntTuplePhaseMod Q c (vinogradovJoinTuple x v)) *
        ZMod.stdAddChar
          (-vinogradovIntTuplePhaseMod Q c (vinogradovJoinTuple y u)) := by
  rw [vinogradovIntTuplePhaseMod_joinTuple,
    vinogradovIntTuplePhaseMod_joinTuple]
  rw [AddChar.map_add_eq_mul]
  rw [show -(vinogradovIntTuplePhaseMod Q c y +
      vinogradovIntTuplePhaseMod Q c u) =
        -vinogradovIntTuplePhaseMod Q c y +
          -vinogradovIntTuplePhaseMod Q c u by ring]
  rw [AddChar.map_add_eq_mul]
  ring

private theorem mixedWeylIntegrand_eq_tupleSum
    (p B a b k r t X Y : ℕ) [NeZero (p ^ B)]
    (xi eta : ℤ) (c : Fin k → ZMod (p ^ B)) :
    vinogradovMixedMainWeylSum p a (p ^ B) k X xi c ^ r *
        (starRingEnd ℂ)
            (vinogradovMixedMainWeylSum p a (p ^ B) k X xi c) ^ r *
        (starRingEnd ℂ)
            (vinogradovIntWeylSum (p ^ B) k Y
              (vinogradovMixedTailValue p b Y eta) c) ^ t *
        vinogradovIntWeylSum (p ^ B) k Y
            (vinogradovMixedTailValue p b Y eta) c ^ t =
      ∑ x : Fin r → Fin X, ∑ y : Fin r → Fin X,
        ∑ u : Fin t → Fin Y, ∑ v : Fin t → Fin Y,
          if (∀ i, Int.ModEq ((p : ℤ) ^ a) xi
                (vinogradovFinTupleInt x i)) ∧
              (∀ i, Int.ModEq ((p : ℤ) ^ a) xi
                (vinogradovFinTupleInt y i)) then
            ZMod.stdAddChar
                (vinogradovIntTuplePhaseMod (p ^ B) c
                  (vinogradovJoinTuple (vinogradovFinTupleInt x)
                    (fun i ↦ vinogradovMixedTailValue p b Y eta (v i)))) *
              ZMod.stdAddChar
                (-vinogradovIntTuplePhaseMod (p ^ B) c
                  (vinogradovJoinTuple (vinogradovFinTupleInt y)
                    (fun i ↦ vinogradovMixedTailValue p b Y eta (u i))))
          else 0 := by
  rw [vinogradovMixedMainWeylSum_pow,
    conj_vinogradovMixedMainWeylSum_pow,
    conj_vinogradovIntWeylSum_pow,
    vinogradovIntWeylSum_pow]
  rw [mul_assoc, mul_assoc]
  rw [Finset.sum_mul]
  apply Fintype.sum_congr
  intro x
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Fintype.sum_congr
  intro y
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  apply Fintype.sum_congr
  intro u
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Fintype.sum_congr
  intro v
  by_cases hx : ∀ i, Int.ModEq ((p : ℤ) ^ a) xi
      (vinogradovFinTupleInt x i)
  · by_cases hy : ∀ i, Int.ModEq ((p : ℤ) ^ a) xi
        (vinogradovFinTupleInt y i)
    · rw [if_pos hx, if_pos hy, if_pos ⟨hx, hy⟩]
      simpa only [mul_assoc] using
        (stdAddChar_mixedBlocks (p ^ B) c
          (vinogradovFinTupleInt x) (vinogradovFinTupleInt y)
          (fun i ↦ vinogradovMixedTailValue p b Y eta (u i))
          (fun i ↦ vinogradovMixedTailValue p b Y eta (v i)))
    · simp [hx, hy]
  · simp [hx]

/-- The normalized product-form mixed conditioned moment.  The tail factors
are ordered conjugate-first so that its tuple expansion matches the crossed
mixed congruence convention. -/
noncomputable def normalizedVinogradovMixedModConditionedMoment
    (p B a b k r t X Y : ℕ) [NeZero (p ^ B)]
    (xi eta : ℤ) : ℂ :=
  ((p ^ B : ℕ) : ℂ)⁻¹ ^ k *
    ∑ c : Fin k → ZMod (p ^ B),
      vinogradovMixedMainWeylSum p a (p ^ B) k X xi c ^ r *
        (starRingEnd ℂ)
            (vinogradovMixedMainWeylSum p a (p ^ B) k X xi c) ^ r *
        (starRingEnd ℂ)
            (vinogradovIntWeylSum (p ^ B) k Y
              (vinogradovMixedTailValue p b Y eta) c) ^ t *
        vinogradovIntWeylSum (p ^ B) k Y
            (vinogradovMixedTailValue p b Y eta) c ^ t

/-- Expanding all four Weyl blocks and commuting finite sums gives the
expanded mixed Fourier moment. -/
theorem normalizedVinogradovMixedModConditionedMoment_eq_expandedMoment
    (p B a b k r t X Y : ℕ) [NeZero (p ^ B)]
    (xi eta : ℤ) :
    normalizedVinogradovMixedModConditionedMoment
        p B a b k r t X Y xi eta =
      normalizedVinogradovMixedModExpandedMoment
        p B a b k r t X Y xi eta := by
  classical
  unfold normalizedVinogradovMixedModConditionedMoment
  simp_rw [mixedWeylIntegrand_eq_tupleSum]
  unfold normalizedVinogradovMixedModExpandedMoment
  simp_rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro x
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro y
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro u
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro v
  by_cases hx : ∀ i, Int.ModEq ((p : ℤ) ^ a) xi
      (vinogradovFinTupleInt x i)
  · by_cases hy : ∀ i, Int.ModEq ((p : ℤ) ^ a) xi
        (vinogradovFinTupleInt y i)
    · simp [VinogradovMixedMainResidueMem,
        vinogradovMixedJoinedLeft, vinogradovMixedJoinedRight,
        vinogradovMixedTailValue, vinogradovFinTupleInt]
    · simp [VinogradovMixedMainResidueMem, hx, hy]
  · simp [VinogradovMixedMainResidueMem, hx]

/-- The product-form mixed conditioned moment counts exactly the modular
mixed conditioned solutions. -/
theorem normalizedVinogradovMixedModConditionedMoment_eq_solutionSetCard
    (p B a b k r t X Y : ℕ) [NeZero (p ^ B)]
    (xi eta : ℤ) :
    normalizedVinogradovMixedModConditionedMoment
        p B a b k r t X Y xi eta =
      (vinogradovMixedModConditionedSolutionSet
        p B a b k r t X Y xi eta).card := by
  rw [normalizedVinogradovMixedModConditionedMoment_eq_expandedMoment,
    normalizedVinogradovMixedModExpandedMoment_eq_solutionSetCard]

end

end ZeroFreeRegion.VinogradovKorobov
