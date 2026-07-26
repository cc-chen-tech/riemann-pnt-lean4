import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedHolder
import ZeroFreeRegion.VinogradovKorobov.VinogradovNewton
import ZeroFreeRegion.VinogradovKorobov.VinogradovQuadratic
import ZeroFreeRegion.VinogradovKorobov.VinogradovWeightedConditioning
import Mathlib.Data.List.Permutation

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Tuple pairs whose images under an arbitrary integer-valued map solve the
common-modulus Vinogradov system. -/
noncomputable def vinogradovIntSolutionPairSet
    (Q k s X : ℕ) [NeZero Q] (value : Fin X → ℤ) :
    Finset ((Fin s → Fin X) × (Fin s → Fin X)) := by
  classical
  exact Finset.univ.filter fun xy ↦
    IsVinogradovSolutionIntMod Q k s
      (fun i ↦ value (xy.1 i)) (fun i ↦ value (xy.2 i))

theorem mem_vinogradovIntSolutionPairSet_iff
    (Q k s X : ℕ) [NeZero Q] (value : Fin X → ℤ)
    (xy : (Fin s → Fin X) × (Fin s → Fin X)) :
    xy ∈ vinogradovIntSolutionPairSet Q k s X value ↔
      IsVinogradovSolutionIntMod Q k s
        (fun i ↦ value (xy.1 i)) (fun i ↦ value (xy.2 i)) := by
  classical
  simp [vinogradovIntSolutionPairSet]

/-- Complex product-form normalization of an arbitrary integer-valued Weyl
moment. -/
noncomputable def normalizedVinogradovIntMoment
    (Q k s X : ℕ) [NeZero Q] (value : Fin X → ℤ) : ℂ :=
  (Q : ℂ)⁻¹ ^ k *
    ∑ a : Fin k → ZMod Q,
      vinogradovIntWeylSum Q k X value a ^ s *
        (starRingEnd ℂ) (vinogradovIntWeylSum Q k X value a) ^ s

/-- Real norm-power form of the same normalized integer-valued Weyl moment. -/
noncomputable def normalizedVinogradovIntNormMoment
    (Q k s X : ℕ) [NeZero Q] (value : Fin X → ℤ) : ℝ :=
  ((Q : ℝ)⁻¹ ^ k) *
    ∑ a : Fin k → ZMod Q,
      ‖vinogradovIntWeylSum Q k X value a‖ ^ (2 * s)

private theorem normalizedVinogradovIntMoment_reindex
    (Q k s X : ℕ) [NeZero Q] (value : Fin X → ℤ) :
    normalizedVinogradovIntMoment Q k s X value =
      ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
        ((Q : ℂ)⁻¹ ^ k *
          ∑ a : Fin k → ZMod Q,
            (ZMod.stdAddChar
                (vinogradovIntTuplePhaseMod Q a (fun i ↦ value (x i))) *
              ZMod.stdAddChar
                (-vinogradovIntTuplePhaseMod Q a
                  (fun i ↦ value (y i))))) := by
  classical
  let F : (Fin k → ZMod Q) → (Fin s → Fin X) → ℂ := fun a x ↦
    ZMod.stdAddChar
      (vinogradovIntTuplePhaseMod Q a (fun i ↦ value (x i)))
  let G : (Fin k → ZMod Q) → (Fin s → Fin X) → ℂ := fun a y ↦
    ZMod.stdAddChar
      (-vinogradovIntTuplePhaseMod Q a (fun i ↦ value (y i)))
  unfold normalizedVinogradovIntMoment
  simp_rw [vinogradovIntWeylSum_pow, conj_vinogradovIntWeylSum_pow]
  change
    (Q : ℂ)⁻¹ ^ k * ∑ a, (∑ x, F a x) * ∑ y, G a y =
      ∑ x, ∑ y, (Q : ℂ)⁻¹ ^ k * ∑ a, F a x * G a y
  calc
    (Q : ℂ)⁻¹ ^ k * ∑ a, (∑ x, F a x) * ∑ y, G a y =
        ∑ a, ∑ x, ∑ y, (Q : ℂ)⁻¹ ^ k * (F a x * G a y) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Fintype.sum_congr
      intro a
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, ∑ a, (Q : ℂ)⁻¹ ^ k * (F a x * G a y) := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro x
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, (Q : ℂ)⁻¹ ^ k * ∑ a, F a x * G a y := by
      simp only [Finset.mul_sum]

/-- Orthogonality turns an arbitrary integer-valued Weyl moment into the
exact number of modular power-sum solution pairs. -/
theorem normalizedVinogradovIntMoment_eq_solutionPairSetCard
    (Q k s X : ℕ) [NeZero Q] (value : Fin X → ℤ) :
    normalizedVinogradovIntMoment Q k s X value =
      ((vinogradovIntSolutionPairSet Q k s X value).card : ℂ) := by
  rw [normalizedVinogradovIntMoment_reindex]
  simp_rw [normalized_sum_intTuplePair_eq_selector]
  simp_rw [vinogradovIntSolutionSelector_eq_indicator]
  classical
  have hcard :
      ((vinogradovIntSolutionPairSet Q k s X value).card : ℂ) =
        ∑ xy : (Fin s → Fin X) × (Fin s → Fin X),
          if IsVinogradovSolutionIntMod Q k s
              (fun i ↦ value (xy.1 i)) (fun i ↦ value (xy.2 i))
            then 1 else 0 := by
    simp [vinogradovIntSolutionPairSet, Finset.sum_boole]
  rw [hcard, Fintype.sum_prod_type]

private theorem normalizedVinogradovIntNormMoment_cast
    (Q k s X : ℕ) [NeZero Q] (value : Fin X → ℤ) :
    (normalizedVinogradovIntNormMoment Q k s X value : ℂ) =
      normalizedVinogradovIntMoment Q k s X value := by
  unfold normalizedVinogradovIntNormMoment normalizedVinogradovIntMoment
  rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_sum]
  congr 1
  apply Fintype.sum_congr
  intro a
  let W := vinogradovIntWeylSum Q k X value a
  change ((‖W‖ ^ (2 * s) : ℝ) : ℂ) =
    W ^ s * (starRingEnd ℂ) W ^ s
  rw [← mul_pow, Complex.mul_conj']
  simp only [Complex.ofReal_pow, pow_mul]

/-- Real norm moments satisfy the same exact finite mean-value identity. -/
theorem normalizedVinogradovIntNormMoment_eq_solutionPairSetCard
    (Q k s X : ℕ) [NeZero Q] (value : Fin X → ℤ) :
    normalizedVinogradovIntNormMoment Q k s X value =
      (vinogradovIntSolutionPairSet Q k s X value).card := by
  apply Complex.ofReal_injective
  rw [normalizedVinogradovIntNormMoment_cast,
    normalizedVinogradovIntMoment_eq_solutionPairSetCard]
  norm_cast

/-- The integer modular predicate on the one-based integer representatives
is the ordinary modular Vinogradov predicate. -/
theorem isVinogradovSolutionIntMod_finTupleInt_iff
    (Q k s X : ℕ) (x y : Fin s → Fin X) :
    IsVinogradovSolutionIntMod Q k s
        (vinogradovFinTupleInt x) (vinogradovFinTupleInt y) ↔
      IsVinogradovSolutionMod Q k s X x y := by
  rw [isVinogradovSolutionIntMod_iff_powerSumMod]
  simp only [IsVinogradovSolutionMod]
  apply forall_congr'
  intro j
  simp [vinogradovIntPowerSumMod, vinogradovPowerSumMod,
    vinogradovFinTupleInt]

/-- The arbitrary-integer solution set specialized to one-based values is
exactly the ordinary modular Vinogradov solution-pair set. -/
theorem vinogradovIntSolutionPairSet_oneBased_eq_solutionPairSetMod
    (Q k s X : ℕ) [NeZero Q] :
    vinogradovIntSolutionPairSet Q k s X
        (fun n ↦ (((n.val + 1 : ℕ) : ℤ))) =
      vinogradovSolutionPairSetMod Q k s X := by
  classical
  ext xy
  rcases xy with ⟨x, y⟩
  rw [mem_vinogradovIntSolutionPairSet_iff,
    mem_vinogradovSolutionPairSetMod_iff]
  simpa [vinogradovFinTupleInt] using
    (isVinogradovSolutionIntMod_finTupleInt_iff Q k s X x y)

/-- The real one-based integer moment is the norm of the existing standard
complex Vinogradov moment. -/
theorem normalizedVinogradovIntNormMoment_oneBased_eq_norm
    (Q k s X : ℕ) [NeZero Q] :
    normalizedVinogradovIntNormMoment Q k s X
        (fun n ↦ (((n.val + 1 : ℕ) : ℤ))) =
      ‖normalizedVinogradovMomentMod Q k s X‖ := by
  rw [normalizedVinogradovIntNormMoment_eq_solutionPairSetCard,
    vinogradovIntSolutionPairSet_oneBased_eq_solutionPairSetMod,
    card_vinogradovSolutionPairSetMod,
    normalizedVinogradovMomentMod_eq_solutionCount]
  simp

/-- Any verified Vinogradov mean-value estimate bounds the one-based integer
norm moment when the common modulus is above the top power-sum scale. -/
theorem normalizedVinogradovIntNormMoment_oneBased_le_of_meanValueEstimate
    (Q k s X : ℕ) [NeZero Q] {ε C : ℝ}
    (hest : VinogradovMeanValueEstimate k s ε C)
    (hX : 1 ≤ X) (hQ : s * X ^ k < Q) :
    normalizedVinogradovIntNormMoment Q k s X
        (fun n ↦ (((n.val + 1 : ℕ) : ℤ))) ≤
      C * Real.rpow (X : ℝ) ε *
        ((X : ℝ) ^ s +
          (X : ℝ) ^ (2 * s - vinogradovCriticalWeight k)) := by
  rw [normalizedVinogradovIntNormMoment_oneBased_eq_norm]
  exact norm_normalizedVinogradovMomentMod_le_of_meanValueEstimate
    Q k s X hest hX hQ

/-- Modular Vinogradov solution pairs whose two tuples lie coordinatewise in
the main residue class selected by the mixed moment. -/
noncomputable def vinogradovMixedMainSolutionPairSet
    (p B a k s X : ℕ) [NeZero (p ^ B)] (xi : ℤ) :
    Finset ((Fin s → Fin X) × (Fin s → Fin X)) := by
  classical
  exact Finset.univ.filter fun xy ↦
    (∀ i, Int.ModEq ((p : ℤ) ^ a) xi
      (vinogradovFinTupleInt xy.1 i)) ∧
    (∀ i, Int.ModEq ((p : ℤ) ^ a) xi
      (vinogradovFinTupleInt xy.2 i)) ∧
    IsVinogradovSolutionIntMod (p ^ B) k s
      (vinogradovFinTupleInt xy.1) (vinogradovFinTupleInt xy.2)

theorem mem_vinogradovMixedMainSolutionPairSet_iff
    (p B a k s X : ℕ) [NeZero (p ^ B)] (xi : ℤ)
    (xy : (Fin s → Fin X) × (Fin s → Fin X)) :
    xy ∈ vinogradovMixedMainSolutionPairSet p B a k s X xi ↔
      (∀ i, Int.ModEq ((p : ℤ) ^ a) xi
        (vinogradovFinTupleInt xy.1 i)) ∧
      (∀ i, Int.ModEq ((p : ℤ) ^ a) xi
        (vinogradovFinTupleInt xy.2 i)) ∧
      IsVinogradovSolutionIntMod (p ^ B) k s
        (vinogradovFinTupleInt xy.1) (vinogradovFinTupleInt xy.2) := by
  classical
  simp [vinogradovMixedMainSolutionPairSet]

/-- Product-form complex moment for the residue-restricted main Weyl block. -/
private noncomputable def normalizedVinogradovMixedMainMoment
    (p B a k s X : ℕ) [NeZero (p ^ B)] (xi : ℤ) : ℂ :=
  ((p ^ B : ℕ) : ℂ)⁻¹ ^ k *
    ∑ c : Fin k → ZMod (p ^ B),
      vinogradovMixedMainWeylSum p a (p ^ B) k X xi c ^ s *
        (starRingEnd ℂ)
          (vinogradovMixedMainWeylSum p a (p ^ B) k X xi c) ^ s

private theorem normalizedVinogradovMixedMainMoment_reindex
    (p B a k s X : ℕ) [NeZero (p ^ B)] (xi : ℤ) :
    normalizedVinogradovMixedMainMoment p B a k s X xi =
      ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
        if (∀ i, Int.ModEq ((p : ℤ) ^ a) xi
              (vinogradovFinTupleInt x i)) ∧
            (∀ i, Int.ModEq ((p : ℤ) ^ a) xi
              (vinogradovFinTupleInt y i)) then
          ((p ^ B : ℕ) : ℂ)⁻¹ ^ k *
            ∑ c : Fin k → ZMod (p ^ B),
              ZMod.stdAddChar
                  (vinogradovIntTuplePhaseMod (p ^ B) c
                    (vinogradovFinTupleInt x)) *
                ZMod.stdAddChar
                  (-vinogradovIntTuplePhaseMod (p ^ B) c
                    (vinogradovFinTupleInt y))
        else 0 := by
  classical
  let F : (Fin k → ZMod (p ^ B)) → (Fin s → Fin X) → ℂ :=
    fun c x ↦
      if ∀ i, Int.ModEq ((p : ℤ) ^ a) xi
          (vinogradovFinTupleInt x i) then
        ZMod.stdAddChar
          (vinogradovIntTuplePhaseMod (p ^ B) c
            (vinogradovFinTupleInt x))
      else 0
  let G : (Fin k → ZMod (p ^ B)) → (Fin s → Fin X) → ℂ :=
    fun c y ↦
      if ∀ i, Int.ModEq ((p : ℤ) ^ a) xi
          (vinogradovFinTupleInt y i) then
        ZMod.stdAddChar
          (-vinogradovIntTuplePhaseMod (p ^ B) c
            (vinogradovFinTupleInt y))
      else 0
  unfold normalizedVinogradovMixedMainMoment
  simp_rw [vinogradovMixedMainWeylSum_pow,
    conj_vinogradovMixedMainWeylSum_pow]
  change
    ((p ^ B : ℕ) : ℂ)⁻¹ ^ k *
        ∑ c, (∑ x, F c x) * ∑ y, G c y =
      ∑ x, ∑ y,
        if (∀ i, Int.ModEq ((p : ℤ) ^ a) xi
              (vinogradovFinTupleInt x i)) ∧
            (∀ i, Int.ModEq ((p : ℤ) ^ a) xi
              (vinogradovFinTupleInt y i)) then
          ((p ^ B : ℕ) : ℂ)⁻¹ ^ k *
            ∑ c,
              ZMod.stdAddChar
                  (vinogradovIntTuplePhaseMod (p ^ B) c
                    (vinogradovFinTupleInt x)) *
                ZMod.stdAddChar
                  (-vinogradovIntTuplePhaseMod (p ^ B) c
                    (vinogradovFinTupleInt y))
        else 0
  calc
    ((p ^ B : ℕ) : ℂ)⁻¹ ^ k *
          ∑ c, (∑ x, F c x) * ∑ y, G c y =
        ∑ c, ∑ x, ∑ y,
          ((p ^ B : ℕ) : ℂ)⁻¹ ^ k *
            (F c x * G c y) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Fintype.sum_congr
      intro c
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, ∑ c,
          ((p ^ B : ℕ) : ℂ)⁻¹ ^ k *
            (F c x * G c y) := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro x
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ y,
          ((p ^ B : ℕ) : ℂ)⁻¹ ^ k *
            ∑ c, F c x * G c y := by
      simp only [Finset.mul_sum]
    _ = _ := by
      apply Fintype.sum_congr
      intro x
      apply Fintype.sum_congr
      intro y
      by_cases hx : ∀ i, Int.ModEq ((p : ℤ) ^ a) xi
          (vinogradovFinTupleInt x i)
      · by_cases hy : ∀ i, Int.ModEq ((p : ℤ) ^ a) xi
            (vinogradovFinTupleInt y i)
        · simp [F, G, hx, hy]
        · simp [F, G, hx, hy]
      · simp [F, G, hx]

private theorem normalizedVinogradovMixedMainMoment_eq_solutionPairSetCard
    (p B a k s X : ℕ) [NeZero (p ^ B)] (xi : ℤ) :
    normalizedVinogradovMixedMainMoment p B a k s X xi =
      ((vinogradovMixedMainSolutionPairSet p B a k s X xi).card : ℂ) := by
  rw [normalizedVinogradovMixedMainMoment_reindex]
  simp_rw [normalized_sum_intTuplePair_eq_selector]
  simp_rw [vinogradovIntSolutionSelector_eq_indicator]
  classical
  have hcard :
      ((vinogradovMixedMainSolutionPairSet
          p B a k s X xi).card : ℂ) =
        ∑ xy : (Fin s → Fin X) × (Fin s → Fin X),
          if (∀ i, Int.ModEq ((p : ℤ) ^ a) xi
                (vinogradovFinTupleInt xy.1 i)) ∧
              (∀ i, Int.ModEq ((p : ℤ) ^ a) xi
                (vinogradovFinTupleInt xy.2 i)) ∧
              IsVinogradovSolutionIntMod (p ^ B) k s
                (vinogradovFinTupleInt xy.1)
                (vinogradovFinTupleInt xy.2)
            then 1 else 0 := by
    simp [vinogradovMixedMainSolutionPairSet, Finset.sum_boole]
  rw [hcard, Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro x
  apply Fintype.sum_congr
  intro y
  by_cases hx : ∀ i, Int.ModEq ((p : ℤ) ^ a) xi
      (vinogradovFinTupleInt x i)
  · by_cases hy : ∀ i, Int.ModEq ((p : ℤ) ^ a) xi
        (vinogradovFinTupleInt y i)
    · simp [hx, hy]
    · simp [hx, hy]
  · simp [hx]

private theorem normalizedVinogradovMixedMainNormMoment_cast
    (p B a k s X : ℕ) [NeZero (p ^ B)] (xi : ℤ) :
    (normalizedVinogradovMixedMainNormMoment p B a k s X xi : ℂ) =
      normalizedVinogradovMixedMainMoment p B a k s X xi := by
  unfold normalizedVinogradovMixedMainNormMoment
  unfold normalizedVinogradovMixedMainMoment
  rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_sum]
  congr 1
  apply Fintype.sum_congr
  intro c
  let W := vinogradovMixedMainWeylSum p a (p ^ B) k X xi c
  change ((‖W‖ ^ (2 * s) : ℝ) : ℂ) =
    W ^ s * (starRingEnd ℂ) W ^ s
  rw [← mul_pow, Complex.mul_conj']
  simp only [Complex.ofReal_pow, pow_mul]

/-- The residue-restricted main norm moment is exactly the number of
modular Vinogradov solution pairs in that residue class. -/
theorem normalizedVinogradovMixedMainNormMoment_eq_solutionPairSetCard
    (p B a k s X : ℕ) [NeZero (p ^ B)] (xi : ℤ) :
    normalizedVinogradovMixedMainNormMoment p B a k s X xi =
      (vinogradovMixedMainSolutionPairSet p B a k s X xi).card := by
  apply Complex.ofReal_injective
  rw [normalizedVinogradovMixedMainNormMoment_cast,
    normalizedVinogradovMixedMainMoment_eq_solutionPairSetCard]
  norm_cast

/-- Forgetting the residue-class restriction embeds the main solution set
into the ordinary one-based Vinogradov solution set. -/
theorem vinogradovMixedMainSolutionPairSet_subset_unrestricted
    (p B a k s X : ℕ) [NeZero (p ^ B)] (xi : ℤ) :
    vinogradovMixedMainSolutionPairSet p B a k s X xi ⊆
      vinogradovIntSolutionPairSet (p ^ B) k s X
        (fun n ↦ (((n.val + 1 : ℕ) : ℤ))) := by
  intro xy hxy
  rw [mem_vinogradovIntSolutionPairSet_iff]
  exact
    (mem_vinogradovMixedMainSolutionPairSet_iff
      p B a k s X xi xy).mp hxy |>.2.2

/-- The main factor left by Cauchy separation is bounded by the standard
unrestricted Vinogradov mean value at the same modulus and moment order. -/
theorem normalizedVinogradovMixedMainNormMoment_le_unrestricted
    (p B a k s X : ℕ) [NeZero (p ^ B)] (xi : ℤ) :
    normalizedVinogradovMixedMainNormMoment p B a k s X xi ≤
      normalizedVinogradovIntNormMoment (p ^ B) k s X
        (fun n ↦ (((n.val + 1 : ℕ) : ℤ))) := by
  rw [normalizedVinogradovMixedMainNormMoment_eq_solutionPairSetCard,
    normalizedVinogradovIntNormMoment_eq_solutionPairSetCard]
  norm_cast
  exact Finset.card_le_card
    (vinogradovMixedMainSolutionPairSet_subset_unrestricted
      p B a k s X xi)

/-- The tail moment retained by mixed Cauchy separation is exactly an affine
integer Vinogradov solution count at the ambient prime-power modulus. -/
theorem normalizedVinogradovMixedTailNormMoment_eq_solutionPairSetCard
    (p B b k s Y : ℕ) [NeZero (p ^ B)] (eta : ℤ) :
    normalizedVinogradovMixedTailNormMoment p B b k s Y eta =
      (vinogradovIntSolutionPairSet (p ^ B) k s Y
        (vinogradovMixedTailValue p b Y eta)).card := by
  exact normalizedVinogradovIntNormMoment_eq_solutionPairSetCard
    (p ^ B) k s Y (vinogradovMixedTailValue p b Y eta)

/-- Removing a common affine shift and a factor `p^b` from a solution modulo
`p^B` leaves, in degree `d`, a congruence modulo the residual power
`p^(B-bd)`.  These residual moduli decrease with the degree. -/
theorem IsVinogradovSolutionIntMod.affine_residual_modEq
    {p B b k s : ℕ} (hp : p ≠ 0) {eta : ℤ}
    {x y : Fin s → ℤ}
    (h : IsVinogradovSolutionIntMod (p ^ B) k s
      (fun i ↦ eta + (p : ℤ) ^ b * x i)
      (fun i ↦ eta + (p : ℤ) ^ b * y i))
    (j : Fin k) (hdegree : b * (j.val + 1) ≤ B) :
    vinogradovPowerSumDifferenceInt x y (j.val + 1) ≡ 0
      [ZMOD (p : ℤ) ^ (B - b * (j.val + 1))] := by
  have htranslated := h.translate (-eta)
  have hx :
      (fun i ↦ eta + (p : ℤ) ^ b * x i + -eta) =
        (fun i ↦ (p : ℤ) ^ b * x i) := by
    funext i
    ring
  have hy :
      (fun i ↦ eta + (p : ℤ) ^ b * y i + -eta) =
        (fun i ↦ (p : ℤ) ^ b * y i) := by
    funext i
    ring
  rw [hx, hy] at htranslated
  have hrow := htranslated j
  have hdiff := hrow.sub
    (Int.ModEq.refl
      (vinogradovPowerSumInt (fun i ↦ (p : ℤ) ^ b * y i) j))
  have hzero :
      vinogradovPowerSumDifferenceInt
          (fun i ↦ (p : ℤ) ^ b * x i)
          (fun i ↦ (p : ℤ) ^ b * y i) (j.val + 1) ≡ 0
        [ZMOD (p : ℤ) ^ B] := by
    simpa [vinogradovPowerSumDifferenceInt, vinogradovPowerSumInt] using hdiff
  rw [vinogradovPowerSumDifferenceInt_scale] at hzero
  rw [← pow_mul] at hzero
  let d := j.val + 1
  have hexponent : b * d + (B - b * d) = B :=
    Nat.add_sub_of_le hdegree
  have hscaled :
      (p : ℤ) ^ (b * d) * vinogradovPowerSumDifferenceInt x y d ≡
        (p : ℤ) ^ (b * d) * 0
          [ZMOD (p : ℤ) ^ (b * d) * (p : ℤ) ^ (B - b * d)] := by
    simpa only [d, mul_zero, ← pow_add, hexponent] using hzero
  exact Int.ModEq.mul_left_cancel'
    (pow_ne_zero _ (Int.ofNat_ne_zero.mpr hp)) hscaled

/-- A tail solution counted by the separated mixed moment satisfies the
degree-`d` residual congruence after removing its affine shift and scale. -/
theorem vinogradovMixedTailSolutionPair_residual_modEq
    (p B b k s Y : ℕ) [NeZero (p ^ B)] (hp : p ≠ 0) (eta : ℤ)
    (xy : (Fin s → Fin Y) × (Fin s → Fin Y))
    (hxy : xy ∈ vinogradovIntSolutionPairSet (p ^ B) k s Y
      (vinogradovMixedTailValue p b Y eta))
    (j : Fin k) (hdegree : b * (j.val + 1) ≤ B) :
    vinogradovPowerSumDifferenceInt
        (vinogradovFinTupleInt xy.1) (vinogradovFinTupleInt xy.2)
        (j.val + 1) ≡ 0
      [ZMOD (p : ℤ) ^ (B - b * (j.val + 1))] := by
  have hsolution :=
    (mem_vinogradovIntSolutionPairSet_iff
      (p ^ B) k s Y (vinogradovMixedTailValue p b Y eta) xy).mp hxy
  have haffine :
      IsVinogradovSolutionIntMod (p ^ B) k s
        (fun i ↦ eta + (p : ℤ) ^ b * vinogradovFinTupleInt xy.1 i)
        (fun i ↦ eta + (p : ℤ) ^ b * vinogradovFinTupleInt xy.2 i) := by
    simpa [vinogradovMixedTailValue, vinogradovFinTupleInt] using hsolution
  exact haffine.affine_residual_modEq hp j hdegree

/-- The decreasing-modulus system left on a tail tuple pair after removing a
common affine shift and the scale `p^b`.  Only degrees for which `bd ≤ B`
carry a nontrivial residual congruence. -/
def IsVinogradovResidualTailSolution
    (p B b k s : ℕ) (x y : Fin s → ℤ) : Prop :=
  ∀ j : Fin k, b * (j.val + 1) ≤ B →
    vinogradovPowerSumDifferenceInt x y (j.val + 1) ≡ 0
      [ZMOD (p : ℤ) ^ (B - b * (j.val + 1))]

/-- Finite solution set for the decreasing-modulus tail system on the
one-based interval represented by `Fin Y`. -/
noncomputable def vinogradovResidualTailSolutionPairSet
    (p B b k s Y : ℕ) :
    Finset ((Fin s → Fin Y) × (Fin s → Fin Y)) := by
  classical
  exact Finset.univ.filter fun xy ↦
    IsVinogradovResidualTailSolution p B b k s
      (vinogradovFinTupleInt xy.1) (vinogradovFinTupleInt xy.2)

theorem mem_vinogradovResidualTailSolutionPairSet_iff
    (p B b k s Y : ℕ)
    (xy : (Fin s → Fin Y) × (Fin s → Fin Y)) :
    xy ∈ vinogradovResidualTailSolutionPairSet p B b k s Y ↔
      IsVinogradovResidualTailSolution p B b k s
        (vinogradovFinTupleInt xy.1) (vinogradovFinTupleInt xy.2) := by
  classical
  simp [vinogradovResidualTailSolutionPairSet]

/-- Every affine tail solution at the ambient modulus belongs to the
corresponding decreasing-modulus residual system. -/
theorem vinogradovIntSolutionPairSet_tail_subset_residual
    (p B b k s Y : ℕ) [NeZero (p ^ B)] (hp : p ≠ 0) (eta : ℤ) :
    vinogradovIntSolutionPairSet (p ^ B) k s Y
        (vinogradovMixedTailValue p b Y eta) ⊆
      vinogradovResidualTailSolutionPairSet p B b k s Y := by
  intro xy hxy
  rw [mem_vinogradovResidualTailSolutionPairSet_iff]
  intro j hdegree
  exact vinogradovMixedTailSolutionPair_residual_modEq
    p B b k s Y hp eta xy hxy j hdegree

/-- The separated tail moment is controlled by the finite residual-system
count.  Proving a nontrivial estimate for this count is the remaining
mean-value problem on the tail side. -/
theorem
    normalizedVinogradovMixedTailNormMoment_le_residualSolutionPairSetCard
    (p B b k s Y : ℕ) [NeZero (p ^ B)] (hp : p ≠ 0) (eta : ℤ) :
    normalizedVinogradovMixedTailNormMoment p B b k s Y eta ≤
      (vinogradovResidualTailSolutionPairSet p B b k s Y).card := by
  rw [normalizedVinogradovMixedTailNormMoment_eq_solutionPairSetCard]
  norm_cast
  exact Finset.card_le_card
    (vinogradovIntSolutionPairSet_tail_subset_residual
      p B b k s Y hp eta)

/-- Retain the whole left tuple and all but the final coordinate of the right
tuple.  The degree-one residual congruence will recover that final
coordinate when the interval does not wrap modulo `p^(B-b)`. -/
def vinogradovResidualTailSolutionPairProjection
    (n Y : ℕ)
    (xy : (Fin (n + 1) → Fin Y) × (Fin (n + 1) → Fin Y)) :
    (Fin (n + 1) → Fin Y) × (Fin n → Fin Y) :=
  (xy.1, fun i ↦ xy.2 i.castSucc)

/-- Under the no-wrap condition, the first residual congruence determines
the final coordinate of the right tuple. -/
theorem vinogradovResidualTailSolutionPairProjection_injOn
    (p B b k n Y : ℕ) (hk : 0 < k) (hbB : b ≤ B)
    (hY : Y ≤ p ^ (B - b)) :
    Set.InjOn
      (vinogradovResidualTailSolutionPairProjection n Y)
      (vinogradovResidualTailSolutionPairSet
        p B b k (n + 1) Y : Set
          ((Fin (n + 1) → Fin Y) × (Fin (n + 1) → Fin Y))) := by
  classical
  intro xy hxy zw hzw hprojection
  have hxySolution :=
    (mem_vinogradovResidualTailSolutionPairSet_iff
      p B b k (n + 1) Y xy).mp hxy
  have hzwSolution :=
    (mem_vinogradovResidualTailSolutionPairSet_iff
      p B b k (n + 1) Y zw).mp hzw
  have hx : xy.1 = zw.1 := by
    simpa [vinogradovResidualTailSolutionPairProjection] using
      congrArg Prod.fst hprojection
  have hinit :
      (fun i : Fin n ↦ xy.2 i.castSucc) =
        (fun i : Fin n ↦ zw.2 i.castSucc) := by
    simpa [vinogradovResidualTailSolutionPairProjection] using
      congrArg Prod.snd hprojection
  let j : Fin k := ⟨0, hk⟩
  have hdegree : b * (j.val + 1) ≤ B := by
    simpa [j] using hbB
  have hxyDegree := hxySolution j hdegree
  have hzwDegree := hzwSolution j hdegree
  have hxySum :
      (∑ i, vinogradovFinTupleInt xy.1 i) ≡
        (∑ i, vinogradovFinTupleInt xy.2 i)
          [ZMOD (p : ℤ) ^ (B - b)] := by
    have h := hxyDegree.add_right
      (∑ i, vinogradovFinTupleInt xy.2 i)
    simpa [j, vinogradovPowerSumDifferenceInt] using h
  have hzwSum :
      (∑ i, vinogradovFinTupleInt xy.1 i) ≡
        (∑ i, vinogradovFinTupleInt zw.2 i)
          [ZMOD (p : ℤ) ^ (B - b)] := by
    have h := hzwDegree.add_right
      (∑ i, vinogradovFinTupleInt zw.2 i)
    simpa [j, vinogradovPowerSumDifferenceInt, ← hx] using h
  have hyzSum :
      (∑ i, vinogradovFinTupleInt xy.2 i) ≡
        (∑ i, vinogradovFinTupleInt zw.2 i)
          [ZMOD (p : ℤ) ^ (B - b)] :=
    hxySum.symm.trans hzwSum
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hyzSum
  have hpref :
      (∑ i : Fin n, vinogradovFinTupleInt xy.2 i.castSucc) =
        ∑ i : Fin n, vinogradovFinTupleInt zw.2 i.castSucc := by
    apply Fintype.sum_congr
    intro i
    exact congrArg
      (fun u : Fin Y ↦ (((u.val + 1 : ℕ) : ℤ)))
      (congrFun hinit i)
  rw [hpref] at hyzSum
  have hlastOne :
      vinogradovFinTupleInt xy.2 (Fin.last n) ≡
        vinogradovFinTupleInt zw.2 (Fin.last n)
          [ZMOD (p : ℤ) ^ (B - b)] :=
    Int.ModEq.add_left_cancel' _ hyzSum
  have hlastVal :
      ((xy.2 (Fin.last n)).val : ℤ) ≡
        ((zw.2 (Fin.last n)).val : ℤ)
          [ZMOD (p : ℤ) ^ (B - b)] := by
    have h := hlastOne.add_right (-1)
    simpa [vinogradovFinTupleInt] using h
  have hlastNat :
      Nat.ModEq (p ^ (B - b))
        (xy.2 (Fin.last n)).val (zw.2 (Fin.last n)).val := by
    rw [Nat.modEq_iff_dvd]
    exact hlastVal.dvd
  have hlast : xy.2 (Fin.last n) = zw.2 (Fin.last n) := by
    apply Fin.ext
    exact hlastNat.eq_of_lt_of_lt
      ((xy.2 (Fin.last n)).isLt.trans_le hY)
      ((zw.2 (Fin.last n)).isLt.trans_le hY)
  apply Prod.ext
  · exact hx
  · funext i
    exact Fin.lastCases hlast (fun u ↦ congrFun hinit u) i

/-- A first-power residual congruence saves one full factor of `Y` over the
trivial `Y^(2(n+1))` count. -/
theorem card_vinogradovResidualTailSolutionPairSet_le_firstPower
    (p B b k n Y : ℕ) (hk : 0 < k) (hbB : b ≤ B)
    (hY : Y ≤ p ^ (B - b)) :
    (vinogradovResidualTailSolutionPairSet
        p B b k (n + 1) Y).card ≤ Y ^ (2 * n + 1) := by
  classical
  have hcard := Finset.card_le_card_of_injOn
    (vinogradovResidualTailSolutionPairProjection n Y)
    (s := vinogradovResidualTailSolutionPairSet p B b k (n + 1) Y)
    (t := Finset.univ)
    (by intro xy hxy; simp)
    (vinogradovResidualTailSolutionPairProjection_injOn
      p B b k n Y hk hbB hY)
  have hcard' :
      (vinogradovResidualTailSolutionPairSet
          p B b k (n + 1) Y).card ≤ Y ^ (n + 1) * Y ^ n := by
    simpa using hcard
  calc
    (vinogradovResidualTailSolutionPairSet
        p B b k (n + 1) Y).card ≤ Y ^ (n + 1) * Y ^ n := hcard'
    _ = Y ^ (2 * n + 1) := by
      rw [← pow_add]
      congr 1
      omega

/-- The first residual congruence gives the separated affine-tail moment one
full factor of `Y` of saving over its trivial `Y^(2(n+1))` bound. -/
theorem normalizedVinogradovMixedTailNormMoment_le_firstPower
    (p B b k n Y : ℕ) [NeZero (p ^ B)] (hp : p ≠ 0)
    (hk : 0 < k) (hbB : b ≤ B) (hY : Y ≤ p ^ (B - b))
    (eta : ℤ) :
    normalizedVinogradovMixedTailNormMoment
        p B b k (n + 1) Y eta ≤ (Y : ℝ) ^ (2 * n + 1) := by
  calc
    normalizedVinogradovMixedTailNormMoment
        p B b k (n + 1) Y eta ≤
      (vinogradovResidualTailSolutionPairSet
        p B b k (n + 1) Y).card :=
      normalizedVinogradovMixedTailNormMoment_le_residualSolutionPairSetCard
        p B b k (n + 1) Y hp eta
    _ ≤ Y ^ (2 * n + 1) := by
      exact_mod_cast
        card_vinogradovResidualTailSolutionPairSet_le_firstPower
        p B b k n Y hk hbB hY

/-- Split a sum over `Fin (n + 2)` into its first `n` entries and its final
two entries. -/
private theorem sum_fin_add_two {R : Type*} [AddCommMonoid R]
    (n : ℕ) (f : Fin (n + 2) → R) :
    (∑ i, f i) =
      (∑ i : Fin n, f i.castSucc.castSucc) +
        (f (Fin.last n).castSucc + f (Fin.last (n + 1))) := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  ac_rfl

/-- Retain the left tuple, the first `n` right coordinates, and one bit
recording the order of the final two coordinates. -/
def vinogradovResidualTailSolutionPairProjectionTwo
    (n Y : ℕ)
    (xy : (Fin (n + 2) → Fin Y) × (Fin (n + 2) → Fin Y)) :
    (Fin (n + 2) → Fin Y) × ((Fin n → Fin Y) × Bool) :=
  (xy.1,
    (fun i ↦ xy.2 i.castSucc.castSucc,
      decide
        ((xy.2 (Fin.last n).castSucc).val ≤
          (xy.2 (Fin.last (n + 1))).val)))

/-- The first `r` residual congruences do not wrap on an `r`-variable tail.
The degree-`d` power sum is at most `r * Y^d`, while its residual modulus is
`p^(B-bd)`. -/
def VinogradovResidualTailNoWrap
    (p B b r Y : ℕ) : Prop :=
  ∀ d, 1 ≤ d → d ≤ r →
    b * d ≤ B ∧ r * Y ^ d < p ^ (B - b * d)

/-- It suffices to check the no-wrap inequality at the highest degree.  The
tail power sums increase with the degree while the residual moduli decrease,
so degree `r` is the unique scale bottleneck. -/
theorem VinogradovResidualTailNoWrap.of_top_degree
    (p B b r Y : ℕ) (hp : 0 < p) (hY : 0 < Y)
    (hdegree : b * r ≤ B)
    (htop : r * Y ^ r < p ^ (B - b * r)) :
    VinogradovResidualTailNoWrap p B b r Y := by
  intro d _hd hdr
  have hbd : b * d ≤ b * r := Nat.mul_le_mul_left b hdr
  have hYpow : Y ^ d ≤ Y ^ r :=
    Nat.pow_le_pow_right hY hdr
  have hexponent : B - b * r ≤ B - b * d :=
    Nat.sub_le_sub_left hbd B
  have hpPow :
      p ^ (B - b * r) ≤ p ^ (B - b * d) :=
    Nat.pow_le_pow_right hp hexponent
  constructor
  · exact hbd.trans hdegree
  · exact (Nat.mul_le_mul_left r hYpow).trans_lt
      (htop.trans_le hpPow)

/-- Specialization of the top-degree no-wrap criterion to the modulus exponent
used by the mixed efficient-congruencing recurrence. -/
theorem VinogradovResidualTailNoWrap.of_mixed_recurrence_top_degree
    (p b k r q Y : ℕ) (hp : 0 < p) (hY : 0 < Y)
    (hdegree : b * q ≤ (k - r + 1) * b)
    (htop :
      q * Y ^ q <
        p ^ ((k - r + 1) * b - b * q)) :
    VinogradovResidualTailNoWrap
      p ((k - r + 1) * b) b q Y :=
  VinogradovResidualTailNoWrap.of_top_degree
    p ((k - r + 1) * b) b q Y hp hY hdegree htop

/-- Two residual solutions with the same left tuple have congruent
right-hand power sums. -/
private theorem residualTail_right_powerSum_modEq
    {p B b k s : ℕ} {x y z w : Fin s → ℤ}
    (hxy : IsVinogradovResidualTailSolution p B b k s x y)
    (hzw : IsVinogradovResidualTailSolution p B b k s z w)
    (hx : x = z) (j : Fin k)
    (hdegree : b * (j.val + 1) ≤ B) :
    (∑ i, y i ^ (j.val + 1)) ≡
      (∑ i, w i ^ (j.val + 1))
        [ZMOD (p : ℤ) ^ (B - b * (j.val + 1))] := by
  have hxyDegree := hxy j hdegree
  have hzwDegree := hzw j hdegree
  have hxySum :
      (∑ i, x i ^ (j.val + 1)) ≡
        (∑ i, y i ^ (j.val + 1))
          [ZMOD (p : ℤ) ^ (B - b * (j.val + 1))] := by
    have h := hxyDegree.add_right (∑ i, y i ^ (j.val + 1))
    simpa [vinogradovPowerSumDifferenceInt] using h
  have hzwSum :
      (∑ i, x i ^ (j.val + 1)) ≡
        (∑ i, w i ^ (j.val + 1))
          [ZMOD (p : ℤ) ^ (B - b * (j.val + 1))] := by
    have h := hzwDegree.add_right (∑ i, w i ^ (j.val + 1))
    simpa [vinogradovPowerSumDifferenceInt, ← hx] using h
  exact hxySum.symm.trans hzwSum

/-- Split a sum over `Fin (n + r)` into its first `n` entries and final `r`
entries. -/
private theorem sum_fin_add {R : Type*} [AddCommMonoid R]
    (n r : ℕ) (f : Fin (n + r) → R) :
    (∑ i, f i) =
      (∑ i : Fin n, f (Fin.castAdd r i)) +
        ∑ i : Fin r, f (Fin.natAdd n i) := by
  rw [← finSumFinEquiv.sum_comp f, Fintype.sum_sum_type]
  rfl

/-- Under the uniform no-wrap hypothesis, agreeing left tuples and right
prefixes force equality of every suffix power sum through degree `r`. -/
theorem residualTail_suffix_powerSums_eq
    (p B b k n r Y : ℕ)
    {xy zw :
      (Fin (n + r) → Fin Y) × (Fin (n + r) → Fin Y)}
    (hxy : IsVinogradovResidualTailSolution p B b k (n + r)
      (vinogradovFinTupleInt xy.1) (vinogradovFinTupleInt xy.2))
    (hzw : IsVinogradovResidualTailSolution p B b k (n + r)
      (vinogradovFinTupleInt zw.1) (vinogradovFinTupleInt zw.2))
    (hx : xy.1 = zw.1)
    (hprefix :
      (fun i : Fin n ↦ xy.2 (Fin.castAdd r i)) =
        (fun i : Fin n ↦ zw.2 (Fin.castAdd r i)))
    (hrk : r ≤ k)
    (hnowrap : VinogradovResidualTailNoWrap p B b r Y)
    (d : ℕ) (hd : 1 ≤ d) (hdr : d ≤ r) :
    (∑ i : Fin r,
        ((xy.2 (Fin.natAdd n i)).val + 1) ^ d) =
      ∑ i : Fin r,
        ((zw.2 (Fin.natAdd n i)).val + 1) ^ d := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin k, j.val + 1 = d := by
    refine ⟨⟨d - 1, by omega⟩, ?_⟩
    change d - 1 + 1 = d
    omega
  have hdegree : b * (j.val + 1) ≤ B := by
    rw [hj]
    exact (hnowrap d hd hdr).1
  have hsum := residualTail_right_powerSum_modEq
    hxy hzw (congrArg vinogradovFinTupleInt hx) j hdegree
  rw [sum_fin_add n r, sum_fin_add n r] at hsum
  have hpref :
      (∑ i : Fin n,
          vinogradovFinTupleInt xy.2 (Fin.castAdd r i) ^ (j.val + 1)) =
        ∑ i : Fin n,
          vinogradovFinTupleInt zw.2 (Fin.castAdd r i) ^ (j.val + 1) := by
    apply Fintype.sum_congr
    intro i
    exact congrArg
      (fun u : Fin Y ↦ (((u.val + 1 : ℕ) : ℤ) ^ (j.val + 1)))
      (congrFun hprefix i)
  rw [hpref] at hsum
  have hsuffixInt :
      (∑ i : Fin r,
          vinogradovFinTupleInt xy.2 (Fin.natAdd n i) ^ d) ≡
        (∑ i : Fin r,
          vinogradovFinTupleInt zw.2 (Fin.natAdd n i) ^ d)
        [ZMOD (p : ℤ) ^ (B - b * d)] := by
    simpa [hj] using Int.ModEq.add_left_cancel' _ hsum
  have hsuffixNat :
      Nat.ModEq (p ^ (B - b * d))
        (∑ i : Fin r,
          ((xy.2 (Fin.natAdd n i)).val + 1) ^ d)
        (∑ i : Fin r,
          ((zw.2 (Fin.natAdd n i)).val + 1) ^ d) := by
    rw [Nat.modEq_iff_dvd]
    simpa [vinogradovFinTupleInt] using hsuffixInt.dvd
  have hxyBound :
      (∑ i : Fin r,
          ((xy.2 (Fin.natAdd n i)).val + 1) ^ d) ≤
        r * Y ^ d := by
    calc
      (∑ i : Fin r,
          ((xy.2 (Fin.natAdd n i)).val + 1) ^ d) ≤
          ∑ _i : Fin r, Y ^ d := by
            apply Finset.sum_le_sum
            intro i _
            exact Nat.pow_le_pow_left (by omega) d
      _ = r * Y ^ d := by simp
  have hzwBound :
      (∑ i : Fin r,
          ((zw.2 (Fin.natAdd n i)).val + 1) ^ d) ≤
        r * Y ^ d := by
    calc
      (∑ i : Fin r,
          ((zw.2 (Fin.natAdd n i)).val + 1) ^ d) ≤
          ∑ _i : Fin r, Y ^ d := by
            apply Finset.sum_le_sum
            intro i _
            exact Nat.pow_le_pow_left (by omega) d
      _ = r * Y ^ d := by simp
  exact hsuffixNat.eq_of_lt_of_lt
    (hxyBound.trans_lt (hnowrap d hd hdr).2)
    (hzwBound.trans_lt (hnowrap d hd hdr).2)

/-- The first `r` no-wrap power sums determine the suffix coordinates as a
multiset.  Thus any two solutions in one left-tuple/right-prefix fiber differ
only by a permutation of their final `r` coordinates. -/
theorem residualTail_suffix_multiset_eq
    (p B b k n r Y : ℕ)
    {xy zw :
      (Fin (n + r) → Fin Y) × (Fin (n + r) → Fin Y)}
    (hxy : IsVinogradovResidualTailSolution p B b k (n + r)
      (vinogradovFinTupleInt xy.1) (vinogradovFinTupleInt xy.2))
    (hzw : IsVinogradovResidualTailSolution p B b k (n + r)
      (vinogradovFinTupleInt zw.1) (vinogradovFinTupleInt zw.2))
    (hx : xy.1 = zw.1)
    (hprefix :
      (fun i : Fin n ↦ xy.2 (Fin.castAdd r i)) =
        (fun i : Fin n ↦ zw.2 (Fin.castAdd r i)))
    (hrk : r ≤ k)
    (hnowrap : VinogradovResidualTailNoWrap p B b r Y) :
    Finset.univ.val.map (fun i : Fin r ↦ xy.2 (Fin.natAdd n i)) =
      Finset.univ.val.map (fun i : Fin r ↦ zw.2 (Fin.natAdd n i)) := by
  let embed : Fin Y → ℚ := fun z ↦ (z.val + 1 : ℕ)
  have hinj : Function.Injective embed := by
    intro a c hac
    apply Fin.ext
    have hac' : a.val + 1 = c.val + 1 := Nat.cast_injective hac
    omega
  apply Multiset.map_injective hinj
  simp only [Multiset.map_map, Function.comp_apply]
  change
    Finset.univ.val.map
        (fun i : Fin r ↦ embed (xy.2 (Fin.natAdd n i))) =
      Finset.univ.val.map
        (fun i : Fin r ↦ embed (zw.2 (Fin.natAdd n i)))
  apply multiset_eq_of_powerSums_eq
  intro d hd hdr
  have hpower := residualTail_suffix_powerSums_eq
    p B b k n r Y hxy hzw hx hprefix hrk hnowrap d hd hdr
  simpa only [embed, Nat.cast_sum, Nat.cast_pow] using
    congrArg (fun z : ℕ ↦ (z : ℚ)) hpower

/-- Retain the full left tuple and the first `n` right coordinates.  The
remaining `r` coordinates form a permutation fiber under the no-wrap
hypothesis. -/
def vinogradovResidualTailSolutionPairProjectionMany
    (n r Y : ℕ)
    (xy : (Fin (n + r) → Fin Y) × (Fin (n + r) → Fin Y)) :
    (Fin (n + r) → Fin Y) × (Fin n → Fin Y) :=
  (xy.1, fun i ↦ xy.2 (Fin.castAdd r i))

/-- Each fiber of the many-coordinate projection contains at most `r!`
residual solutions. -/
theorem
    card_vinogradovResidualTailSolutionPairProjectionMany_fiber_le_factorial
    (p B b k n r Y : ℕ) (hrk : r ≤ k)
    (hnowrap : VinogradovResidualTailNoWrap p B b r Y)
    (z : (Fin (n + r) → Fin Y) × (Fin n → Fin Y)) :
    {xy ∈ vinogradovResidualTailSolutionPairSet p B b k (n + r) Y |
      vinogradovResidualTailSolutionPairProjectionMany n r Y xy = z}.card ≤
        r.factorial := by
  classical
  let S :=
    vinogradovResidualTailSolutionPairSet p B b k (n + r) Y
  let fiber :=
    {xy ∈ S |
      vinogradovResidualTailSolutionPairProjectionMany n r Y xy = z}
  by_cases hfiber : fiber.Nonempty
  · obtain ⟨q, hq⟩ := hfiber
    let suffixList :
        ((Fin (n + r) → Fin Y) × (Fin (n + r) → Fin Y)) →
          List (Fin Y) :=
      fun xy ↦ List.ofFn (fun i : Fin r ↦ xy.2 (Fin.natAdd n i))
    have hcard := Finset.card_le_card_of_injOn suffixList
      (s := fiber)
      (t := (suffixList q).permutations.toFinset)
      (by
        intro xy hxy
        change suffixList xy ∈ (suffixList q).permutations.toFinset
        rw [List.mem_toFinset, List.mem_permutations]
        have hxyS : xy ∈ S := (Finset.mem_filter.mp hxy).1
        have hqS : q ∈ S := (Finset.mem_filter.mp hq).1
        have hxyProjection :=
          (Finset.mem_filter.mp hxy).2
        have hqProjection :=
          (Finset.mem_filter.mp hq).2
        have hprojection :
            vinogradovResidualTailSolutionPairProjectionMany n r Y xy =
              vinogradovResidualTailSolutionPairProjectionMany n r Y q :=
          hxyProjection.trans hqProjection.symm
        have hx : xy.1 = q.1 := by
          simpa [vinogradovResidualTailSolutionPairProjectionMany] using
            congrArg Prod.fst hprojection
        have hprefix :
            (fun i : Fin n ↦ xy.2 (Fin.castAdd r i)) =
              (fun i : Fin n ↦ q.2 (Fin.castAdd r i)) := by
          simpa [vinogradovResidualTailSolutionPairProjectionMany] using
            congrArg Prod.snd hprojection
        have hxySolution :=
          (mem_vinogradovResidualTailSolutionPairSet_iff
            p B b k (n + r) Y xy).mp hxyS
        have hqSolution :=
          (mem_vinogradovResidualTailSolutionPairSet_iff
            p B b k (n + r) Y q).mp hqS
        apply Multiset.coe_eq_coe.mp
        simpa [suffixList] using
          residualTail_suffix_multiset_eq
            p B b k n r Y hxySolution hqSolution hx hprefix hrk hnowrap)
      (by
        intro xy hxy qw hqw hsuffix
        have hxyProjection :=
          (Finset.mem_filter.mp hxy).2
        have hqwProjection :=
          (Finset.mem_filter.mp hqw).2
        have hprojection :
            vinogradovResidualTailSolutionPairProjectionMany n r Y xy =
              vinogradovResidualTailSolutionPairProjectionMany n r Y qw :=
          hxyProjection.trans hqwProjection.symm
        have hx : xy.1 = qw.1 := by
          simpa [vinogradovResidualTailSolutionPairProjectionMany] using
            congrArg Prod.fst hprojection
        have hprefix :
            (fun i : Fin n ↦ xy.2 (Fin.castAdd r i)) =
              (fun i : Fin n ↦ qw.2 (Fin.castAdd r i)) := by
          simpa [vinogradovResidualTailSolutionPairProjectionMany] using
            congrArg Prod.snd hprojection
        have hsuffixFunction :
            (fun i : Fin r ↦ xy.2 (Fin.natAdd n i)) =
              (fun i : Fin r ↦ qw.2 (Fin.natAdd n i)) := by
          exact List.ofFn_inj.mp hsuffix
        apply Prod.ext hx
        funext i
        obtain ⟨u, rfl⟩ := finSumFinEquiv.surjective i
        rcases u with j | j
        · simpa using congrFun hprefix j
        · simpa using congrFun hsuffixFunction j)
    calc
      {xy ∈ vinogradovResidualTailSolutionPairSet
          p B b k (n + r) Y |
        vinogradovResidualTailSolutionPairProjectionMany n r Y xy = z}.card =
          fiber.card := rfl
      _ ≤ (suffixList q).permutations.toFinset.card := hcard
      _ ≤ (suffixList q).permutations.length :=
        List.toFinset_card_le (suffixList q).permutations
      _ = r.factorial := by
        rw [List.length_permutations, List.length_ofFn]
  · have hempty : fiber = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hfiber
    change fiber.card ≤ r.factorial
    simp [hempty]

/-- The first `r` residual congruences save `r` powers of `Y`, up to the
permutation factor `r!`. -/
theorem card_vinogradovResidualTailSolutionPairSet_le_factorial
    (p B b k n r Y : ℕ) (hrk : r ≤ k)
    (hnowrap : VinogradovResidualTailNoWrap p B b r Y) :
    (vinogradovResidualTailSolutionPairSet
        p B b k (n + r) Y).card ≤
      r.factorial * Y ^ (2 * n + r) := by
  classical
  let S :=
    vinogradovResidualTailSolutionPairSet p B b k (n + r) Y
  let projection :=
    vinogradovResidualTailSolutionPairProjectionMany n r Y
  have hmaps : ∀ xy ∈ S,
      projection xy ∈
        (Finset.univ :
          Finset ((Fin (n + r) → Fin Y) × (Fin n → Fin Y))) :=
    fun _ _ ↦ Finset.mem_univ _
  rw [show
    vinogradovResidualTailSolutionPairSet p B b k (n + r) Y = S from rfl]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    (∑ z ∈
        (Finset.univ :
          Finset ((Fin (n + r) → Fin Y) × (Fin n → Fin Y))),
        {xy ∈ S | projection xy = z}.card) ≤
      ∑ _z ∈
        (Finset.univ :
          Finset ((Fin (n + r) → Fin Y) × (Fin n → Fin Y))),
        r.factorial := by
          apply Finset.sum_le_sum
          intro z _
          exact
            card_vinogradovResidualTailSolutionPairProjectionMany_fiber_le_factorial
              p B b k n r Y hrk hnowrap z
    _ = (Y ^ (n + r) * Y ^ n) * r.factorial := by simp
    _ = r.factorial * (Y ^ (n + r) * Y ^ n) := by ac_rfl
    _ = r.factorial * Y ^ (2 * n + r) := by
      rw [← pow_add]
      congr 2
      omega

/-- The factorial residual count transfers to the separated affine-tail
moment. -/
theorem normalizedVinogradovMixedTailNormMoment_le_factorial
    (p B b k n r Y : ℕ) [NeZero (p ^ B)] (hp : p ≠ 0)
    (hrk : r ≤ k)
    (hnowrap : VinogradovResidualTailNoWrap p B b r Y)
    (eta : ℤ) :
    normalizedVinogradovMixedTailNormMoment
        p B b k (n + r) Y eta ≤
      r.factorial * (Y : ℝ) ^ (2 * n + r) := by
  calc
    normalizedVinogradovMixedTailNormMoment
        p B b k (n + r) Y eta ≤
      (vinogradovResidualTailSolutionPairSet
        p B b k (n + r) Y).card :=
      normalizedVinogradovMixedTailNormMoment_le_residualSolutionPairSetCard
        p B b k (n + r) Y hp eta
    _ ≤ r.factorial * (Y : ℝ) ^ (2 * n + r) := by
      exact_mod_cast
        card_vinogradovResidualTailSolutionPairSet_le_factorial
          p B b k n r Y hrk hnowrap

/-- Cauchy separation with a factorial tail saving.  Writing the separated
tail moment order as `2t = n + q`, the first `q` no-wrap residual equations
save `q` powers of `Y` over the trivial fourth-moment tail count. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_factorialTail
    (p B a b k r t X Y n q : ℕ) [NeZero (p ^ B)]
    (hp : p ≠ 0) (hqk : q ≤ k) (hsplit : n + q = 2 * t)
    (hnowrap : VinogradovResidualTailNoWrap p B b q Y)
    (xi eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p B a b k r t X Y xi eta‖ ^ 2 ≤
      normalizedVinogradovMixedMainNormMoment p B a k (2 * r) X xi *
        ((q.factorial : ℝ) * (Y : ℝ) ^ (2 * n + q)) := by
  have hcauchy :=
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_separateMoments
      p B a b k r t X Y xi eta
  have htail :
      normalizedVinogradovMixedTailNormMoment p B b k (2 * t) Y eta ≤
        (q.factorial : ℝ) * (Y : ℝ) ^ (2 * n + q) := by
    rw [← hsplit]
    exact normalizedVinogradovMixedTailNormMoment_le_factorial
      p B b k n q Y hp hqk hnowrap eta
  have hmain :
      0 ≤ normalizedVinogradovMixedMainNormMoment
        p B a k (2 * r) X xi := by
    unfold normalizedVinogradovMixedMainNormMoment
    positivity
  exact hcauchy.trans
    (mul_le_mul_of_nonneg_left htail hmain)

/-- The complete Cauchy bridge: the mixed moment is controlled by an
ordinary unrestricted Vinogradov mean value and the factorially reduced
tail count. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_unrestricted_factorialTail
    (p B a b k r t X Y n q : ℕ) [NeZero (p ^ B)]
    (hp : p ≠ 0) (hqk : q ≤ k) (hsplit : n + q = 2 * t)
    (hnowrap : VinogradovResidualTailNoWrap p B b q Y)
    (xi eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p B a b k r t X Y xi eta‖ ^ 2 ≤
      normalizedVinogradovIntNormMoment (p ^ B) k (2 * r) X
          (fun z ↦ (((z.val + 1 : ℕ) : ℤ))) *
        ((q.factorial : ℝ) * (Y : ℝ) ^ (2 * n + q)) := by
  have hfactorial :=
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_factorialTail
      p B a b k r t X Y n q hp hqk hsplit hnowrap xi eta
  have hmain :=
    normalizedVinogradovMixedMainNormMoment_le_unrestricted
      p B a k (2 * r) X xi
  have htail :
      0 ≤ (q.factorial : ℝ) * (Y : ℝ) ^ (2 * n + q) := by
    positivity
  exact hfactorial.trans
    (mul_le_mul_of_nonneg_right hmain htail)

/-- Feeding a verified Vinogradov mean-value estimate into the complete
Cauchy bridge gives an explicit main-factor bound while retaining the
factorial tail saving. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_meanValueEstimate_factorialTail
    (p B a b k r t X Y n q : ℕ) [NeZero (p ^ B)] {ε C : ℝ}
    (hp : p ≠ 0) (hqk : q ≤ k) (hsplit : n + q = 2 * t)
    (hnowrap : VinogradovResidualTailNoWrap p B b q Y)
    (hest : VinogradovMeanValueEstimate k (2 * r) ε C)
    (hX : 1 ≤ X) (hscale : (2 * r) * X ^ k < p ^ B)
    (xi eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p B a b k r t X Y xi eta‖ ^ 2 ≤
      (C * Real.rpow (X : ℝ) ε *
          ((X : ℝ) ^ (2 * r) +
            (X : ℝ) ^ (2 * (2 * r) - vinogradovCriticalWeight k))) *
        ((q.factorial : ℝ) * (Y : ℝ) ^ (2 * n + q)) := by
  have hbridge :=
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_unrestricted_factorialTail
      p B a b k r t X Y n q hp hqk hsplit hnowrap xi eta
  have hmain :=
    normalizedVinogradovIntNormMoment_oneBased_le_of_meanValueEstimate
      (p ^ B) k (2 * r) X hest hX hscale
  have htail :
      0 ≤ (q.factorial : ℝ) * (Y : ℝ) ^ (2 * n + q) := by
    positivity
  exact hbridge.trans
    (mul_le_mul_of_nonneg_right hmain htail)

/-- In the proved diagonal range `2r ≤ k`, the main mean-value input is
unconditional.  Relative to the squared trivial bound, this saves the main
factor `X^(2r)` as well as the first `q` tail factors. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_diagonal_factorialTail
    (p B a b k r t X Y n q : ℕ) [NeZero (p ^ B)]
    (hp : p ≠ 0) (h2rk : 2 * r ≤ k)
    (hqk : q ≤ k) (hsplit : n + q = 2 * t)
    (hnowrap : VinogradovResidualTailNoWrap p B b q Y)
    (hX : 1 ≤ X) (hscale : (2 * r) * X ^ k < p ^ B)
    (xi eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p B a b k r t X Y xi eta‖ ^ 2 ≤
      ((2 * r).factorial : ℝ) *
          ((X : ℝ) ^ (2 * r) +
            (X : ℝ) ^ (2 * (2 * r) - vinogradovCriticalWeight k)) *
        ((q.factorial : ℝ) * (Y : ℝ) ^ (2 * n + q)) := by
  have h :=
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_meanValueEstimate_factorialTail
      p B a b k r t X Y n q hp hqk hsplit hnowrap
        (vinogradovMeanValueEstimate_diagonal k (2 * r) h2rk)
        hX hscale xi eta
  have hrpow : Real.rpow (X : ℝ) 0 = 1 := Real.rpow_zero _
  rw [hrpow, mul_one] at h
  exact h

/-- The diagonal mixed-moment estimate at the exact modulus exponent used by
the efficient-congruencing recurrence. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_recurrenceModulus_diagonal
    (p a b k r t X Y n q : ℕ) [Fact p.Prime]
    (h2rk : 2 * r ≤ k)
    (hqk : q ≤ k) (hsplit : n + q = 2 * t)
    (hY : 0 < Y)
    (hdegree : b * q ≤ (k - r + 1) * b)
    (htop :
      q * Y ^ q <
        p ^ ((k - r + 1) * b - b * q))
    (hX : 1 ≤ X)
    (hscale :
      (2 * r) * X ^ k < p ^ ((k - r + 1) * b))
    (xi eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * b) a b k r t X Y xi eta‖ ^ 2 ≤
      ((2 * r).factorial : ℝ) *
          ((X : ℝ) ^ (2 * r) +
            (X : ℝ) ^ (2 * (2 * r) - vinogradovCriticalWeight k)) *
        ((q.factorial : ℝ) * (Y : ℝ) ^ (2 * n + q)) := by
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  exact
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_diagonal_factorialTail
      p ((k - r + 1) * b) a b k r t X Y n q
        (Fact.out : p.Prime).ne_zero h2rk hqk hsplit
        (VinogradovResidualTailNoWrap.of_mixed_recurrence_top_degree
          p b k r q Y (Fact.out : p.Prime).pos hY hdegree htop)
        hX hscale xi eta

/-- A concrete nonempty parameter family for the mixed recurrence.  Taking
`b = 2`, one tail variable, and both box lengths equal to the prime gives an
unconditional power-saving moment bound throughout the diagonal range. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_primeScale_unitTail
    (p a k r : ℕ) [Fact p.Prime]
    (hr : 0 < r) (h2rk : 2 * r ≤ k) (hrp : 2 * r < p)
    (xi eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * 2) a 2 k r 1 p p xi eta‖ ^ 2 ≤
      ((2 * r).factorial : ℝ) *
          ((p : ℝ) ^ (2 * r) +
            (p : ℝ) ^ (2 * (2 * r) - vinogradovCriticalWeight k)) *
        (p : ℝ) ^ 3 := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hqk : 1 ≤ k := by omega
  have hdegree : 2 * 1 ≤ (k - r + 1) * 2 := by omega
  have htailExponent :
      1 < (k - r + 1) * 2 - 2 * 1 := by
    omega
  have htop :
      1 * p ^ 1 <
        p ^ ((k - r + 1) * 2 - 2 * 1) := by
    simpa using Nat.pow_lt_pow_right hp1 htailExponent
  have hmainExponent :
      k + 1 ≤ (k - r + 1) * 2 := by
    omega
  have hcoefficient :
      (2 * r) * p ^ k < p * p ^ k :=
    Nat.mul_lt_mul_of_pos_right hrp (pow_pos hp0 k)
  have hscale :
      (2 * r) * p ^ k <
        p ^ ((k - r + 1) * 2) := by
    calc
      (2 * r) * p ^ k < p * p ^ k := hcoefficient
      _ = p ^ (k + 1) := by
        simp [pow_succ, Nat.mul_comm]
      _ ≤ p ^ ((k - r + 1) * 2) :=
        Nat.pow_le_pow_right hp0 hmainExponent
  have h :=
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_recurrenceModulus_diagonal
      p a 2 k r 1 p p 1 1 h2rk hqk (by omega) hp0
        hdegree htop (by omega) hscale xi eta
  simpa only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one,
    show 2 * 1 + 1 = 3 by omega] using h

/-- The explicit prime-scale family is genuinely power-saving: its squared
moment has exponent `2r + 3`, compared with the squared trivial exponent
`4r + 4`, up to the displayed factorial constant. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_primeScale_powerSaving
    (p a k r : ℕ) [Fact p.Prime]
    (hr : 0 < r) (h2rk : 2 * r ≤ k) (hrp : 2 * r < p)
    (xi eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * 2) a 2 k r 1 p p xi eta‖ ^ 2 ≤
      2 * ((2 * r).factorial : ℝ) * (p : ℝ) ^ (2 * r + 3) := by
  have h :=
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_primeScale_unitTail
      p a k r hr h2rk hrp xi eta
  have hweight : 2 * r ≤ vinogradovCriticalWeight k := by
    unfold vinogradovCriticalWeight
    apply (Nat.le_div_iff_mul_le (by omega)).2
    calc
      (2 * r) * 2 ≤ k * 2 := Nat.mul_le_mul_right 2 h2rk
      _ ≤ k * (k + 1) := Nat.mul_le_mul_left k (by omega)
  have hexponent :
      2 * (2 * r) - vinogradovCriticalWeight k ≤ 2 * r := by
    omega
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hpow :
      (p : ℝ) ^ (2 * (2 * r) - vinogradovCriticalWeight k) ≤
        (p : ℝ) ^ (2 * r) :=
    pow_le_pow_right₀ hpR hexponent
  have hsum :
      (p : ℝ) ^ (2 * r) +
          (p : ℝ) ^ (2 * (2 * r) - vinogradovCriticalWeight k) ≤
        (p : ℝ) ^ (2 * r) + (p : ℝ) ^ (2 * r) :=
    add_le_add (le_refl _) hpow
  calc
    ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * 2) a 2 k r 1 p p xi eta‖ ^ 2
        ≤ ((2 * r).factorial : ℝ) *
            ((p : ℝ) ^ (2 * r) +
              (p : ℝ) ^
                (2 * (2 * r) - vinogradovCriticalWeight k)) *
              (p : ℝ) ^ 3 := h
    _ ≤ ((2 * r).factorial : ℝ) *
          ((p : ℝ) ^ (2 * r) + (p : ℝ) ^ (2 * r)) *
            (p : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (by positivity))
        (by positivity)
    _ = 2 * ((2 * r).factorial : ℝ) *
          (p : ℝ) ^ (2 * r + 3) := by
      rw [pow_add]
      ring

/-- A balanced prime-scale family with `q` recoverable tail variables.  The
condition `3q + 1 ≤ 2(k-r+1)` leaves enough residual modulus for the degree
`q` no-wrap check. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_primeScale_balancedTail
    (p a k r q : ℕ) [Fact p.Prime]
    (hr : 0 < r) (hq : 0 < q)
    (h2rk : 2 * r ≤ k) (hrp : 2 * r < p) (hqp : q < p)
    (hbudget : 3 * q + 1 ≤ 2 * (k - r + 1))
    (xi eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * 2) a 2 k r q p p xi eta‖ ^ 2 ≤
      ((2 * r).factorial : ℝ) *
          ((p : ℝ) ^ (2 * r) +
            (p : ℝ) ^ (2 * (2 * r) - vinogradovCriticalWeight k)) *
        ((q.factorial : ℝ) * (p : ℝ) ^ (3 * q)) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hqk : q ≤ k := by
    omega
  have hdegree :
      2 * q ≤ (k - r + 1) * 2 := by
    omega
  have htailExponent :
      q + 1 ≤ (k - r + 1) * 2 - 2 * q := by
    omega
  have hcoefficientTail :
      q * p ^ q < p * p ^ q :=
    Nat.mul_lt_mul_of_pos_right hqp (pow_pos hp0 q)
  have htop :
      q * p ^ q <
        p ^ ((k - r + 1) * 2 - 2 * q) := by
    calc
      q * p ^ q < p * p ^ q := hcoefficientTail
      _ = p ^ (q + 1) := by
        simp [pow_succ, Nat.mul_comm]
      _ ≤ p ^ ((k - r + 1) * 2 - 2 * q) :=
        Nat.pow_le_pow_right hp0 htailExponent
  have hmainExponent :
      k + 1 ≤ (k - r + 1) * 2 := by
    omega
  have hcoefficientMain :
      (2 * r) * p ^ k < p * p ^ k :=
    Nat.mul_lt_mul_of_pos_right hrp (pow_pos hp0 k)
  have hscale :
      (2 * r) * p ^ k <
        p ^ ((k - r + 1) * 2) := by
    calc
      (2 * r) * p ^ k < p * p ^ k := hcoefficientMain
      _ = p ^ (k + 1) := by
        simp [pow_succ, Nat.mul_comm]
      _ ≤ p ^ ((k - r + 1) * 2) :=
        Nat.pow_le_pow_right hp0 hmainExponent
  have h :=
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_recurrenceModulus_diagonal
      p a 2 k r q p p q q h2rk hqk (by omega) hp0
        hdegree htop (by omega) hscale xi eta
  simpa only [show 2 * q + q = 3 * q by omega] using h

/-- The balanced family saves the exponent `2r + q` relative to its squared
trivial scale: the proved exponent is `2r + 3q`, while the trivial exponent is
`4r + 4q`. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_primeScale_balancedTail_powerSaving
    (p a k r q : ℕ) [Fact p.Prime]
    (hr : 0 < r) (hq : 0 < q)
    (h2rk : 2 * r ≤ k) (hrp : 2 * r < p) (hqp : q < p)
    (hbudget : 3 * q + 1 ≤ 2 * (k - r + 1))
    (xi eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * 2) a 2 k r q p p xi eta‖ ^ 2 ≤
      2 * ((2 * r).factorial : ℝ) * (q.factorial : ℝ) *
        (p : ℝ) ^ (2 * r + 3 * q) := by
  have h :=
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_primeScale_balancedTail
      p a k r q hr hq h2rk hrp hqp hbudget xi eta
  have hweight : 2 * r ≤ vinogradovCriticalWeight k := by
    unfold vinogradovCriticalWeight
    apply (Nat.le_div_iff_mul_le (by omega)).2
    calc
      (2 * r) * 2 ≤ k * 2 := Nat.mul_le_mul_right 2 h2rk
      _ ≤ k * (k + 1) := Nat.mul_le_mul_left k (by omega)
  have hexponent :
      2 * (2 * r) - vinogradovCriticalWeight k ≤ 2 * r := by
    omega
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hpow :
      (p : ℝ) ^ (2 * (2 * r) - vinogradovCriticalWeight k) ≤
        (p : ℝ) ^ (2 * r) :=
    pow_le_pow_right₀ hpR hexponent
  have hsum :
      (p : ℝ) ^ (2 * r) +
          (p : ℝ) ^ (2 * (2 * r) - vinogradovCriticalWeight k) ≤
        (p : ℝ) ^ (2 * r) + (p : ℝ) ^ (2 * r) :=
    add_le_add (le_refl _) hpow
  calc
    ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * 2) a 2 k r q p p xi eta‖ ^ 2
        ≤ ((2 * r).factorial : ℝ) *
            ((p : ℝ) ^ (2 * r) +
              (p : ℝ) ^
                (2 * (2 * r) - vinogradovCriticalWeight k)) *
              ((q.factorial : ℝ) * (p : ℝ) ^ (3 * q)) := h
    _ ≤ ((2 * r).factorial : ℝ) *
          ((p : ℝ) ^ (2 * r) + (p : ℝ) ^ (2 * r)) *
            ((q.factorial : ℝ) * (p : ℝ) ^ (3 * q)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (by positivity))
        (by positivity)
    _ = 2 * ((2 * r).factorial : ℝ) * (q.factorial : ℝ) *
          (p : ℝ) ^ (2 * r + 3 * q) := by
      rw [pow_add]
      ring

/-- Largest balanced tail length allowed by the residual no-wrap exponent
budget at recurrence modulus exponent `2(k-r+1)`. -/
def vinogradovBalancedTailLength (k r : ℕ) : ℕ :=
  (2 * (k - r + 1) - 1) / 3

/-- The balanced tail length is exactly the largest integer satisfying the
residual exponent budget. -/
theorem vinogradovBalancedTailLength_spec (k r q : ℕ) :
    q ≤ vinogradovBalancedTailLength k r ↔
      3 * q + 1 ≤ 2 * (k - r + 1) := by
  unfold vinogradovBalancedTailLength
  rw [Nat.le_div_iff_mul_le (by omega)]
  omega

/-- Choosing the maximal balanced tail length makes the prime-scale saving
theorem parameter-free.  The natural recurrence hypothesis `k < p` supplies
both coefficient inequalities. -/
theorem
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_primeScale_optimizedBalancedTail_powerSaving
    (p a k r : ℕ) [Fact p.Prime]
    (hr : 0 < r) (h2rk : 2 * r ≤ k) (hkp : k < p)
    (xi eta : ℤ) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * 2) a 2 k r
          (vinogradovBalancedTailLength k r) p p xi eta‖ ^ 2 ≤
      2 * ((2 * r).factorial : ℝ) *
        ((vinogradovBalancedTailLength k r).factorial : ℝ) *
          (p : ℝ) ^
            (2 * r + 3 * vinogradovBalancedTailLength k r) := by
  have honeBudget :
      3 * 1 + 1 ≤ 2 * (k - r + 1) := by
    omega
  have hq :
      0 < vinogradovBalancedTailLength k r := by
    have hone :
        1 ≤ vinogradovBalancedTailLength k r :=
      (vinogradovBalancedTailLength_spec k r 1).2 honeBudget
    omega
  have hbudget :
      3 * vinogradovBalancedTailLength k r + 1 ≤
        2 * (k - r + 1) :=
    (vinogradovBalancedTailLength_spec
      k r (vinogradovBalancedTailLength k r)).1 (le_refl _)
  have hqk : vinogradovBalancedTailLength k r ≤ k := by
    omega
  exact
    norm_normalizedVinogradovMixedModConditionedMoment_sq_le_primeScale_balancedTail_powerSaving
      p a k r (vinogradovBalancedTailLength k r)
        hr hq h2rk (h2rk.trans_lt hkp) (hqk.trans_lt hkp)
        hbudget xi eta

/-- If the first `n` right coordinates agree, residual congruence reduces to
a congruence between the power sums of the final two coordinates. -/
private theorem residualTail_lastTwo_powerSum_modEq
    {p B b k n Y : ℕ}
    {xy zw :
      (Fin (n + 2) → Fin Y) × (Fin (n + 2) → Fin Y)}
    (hxy : IsVinogradovResidualTailSolution p B b k (n + 2)
      (vinogradovFinTupleInt xy.1) (vinogradovFinTupleInt xy.2))
    (hzw : IsVinogradovResidualTailSolution p B b k (n + 2)
      (vinogradovFinTupleInt zw.1) (vinogradovFinTupleInt zw.2))
    (hx : xy.1 = zw.1)
    (hprefix :
      (fun i : Fin n ↦ xy.2 i.castSucc.castSucc) =
        (fun i : Fin n ↦ zw.2 i.castSucc.castSucc))
    (j : Fin k) (hdegree : b * (j.val + 1) ≤ B) :
    vinogradovFinTupleInt xy.2 (Fin.last n).castSucc ^ (j.val + 1) +
        vinogradovFinTupleInt xy.2 (Fin.last (n + 1)) ^ (j.val + 1) ≡
      vinogradovFinTupleInt zw.2 (Fin.last n).castSucc ^ (j.val + 1) +
        vinogradovFinTupleInt zw.2 (Fin.last (n + 1)) ^ (j.val + 1)
      [ZMOD (p : ℤ) ^ (B - b * (j.val + 1))] := by
  have hsum := residualTail_right_powerSum_modEq hxy hzw
    (congrArg vinogradovFinTupleInt hx) j hdegree
  rw [sum_fin_add_two, sum_fin_add_two] at hsum
  have hpref :
      (∑ i : Fin n,
          vinogradovFinTupleInt xy.2 i.castSucc.castSucc ^ (j.val + 1)) =
        ∑ i : Fin n,
          vinogradovFinTupleInt zw.2 i.castSucc.castSucc ^ (j.val + 1) := by
    apply Fintype.sum_congr
    intro i
    exact congrArg
      (fun u : Fin Y ↦ (((u.val + 1 : ℕ) : ℤ) ^ (j.val + 1)))
      (congrFun hprefix i)
  rw [hpref] at hsum
  exact Int.ModEq.add_left_cancel' _ hsum

/-- The first two no-wrap residual congruences determine the final two right
coordinates up to transposition; the orientation bit removes that ambiguity. -/
theorem vinogradovResidualTailSolutionPairProjectionTwo_injOn
    (p B b k n Y : ℕ) (hk : 2 ≤ k) (h2bB : 2 * b ≤ B)
    (hlinear : 2 * Y < p ^ (B - b))
    (hquadratic : 2 * Y ^ 2 < p ^ (B - 2 * b)) :
    Set.InjOn
      (vinogradovResidualTailSolutionPairProjectionTwo n Y)
      (vinogradovResidualTailSolutionPairSet
        p B b k (n + 2) Y : Set
          ((Fin (n + 2) → Fin Y) × (Fin (n + 2) → Fin Y))) := by
  classical
  intro xy hxy zw hzw hprojection
  have hxySolution :=
    (mem_vinogradovResidualTailSolutionPairSet_iff
      p B b k (n + 2) Y xy).mp hxy
  have hzwSolution :=
    (mem_vinogradovResidualTailSolutionPairSet_iff
      p B b k (n + 2) Y zw).mp hzw
  have hx : xy.1 = zw.1 := by
    simpa [vinogradovResidualTailSolutionPairProjectionTwo] using
      congrArg Prod.fst hprojection
  have htailProjection := congrArg Prod.snd hprojection
  have hprefix :
      (fun i : Fin n ↦ xy.2 i.castSucc.castSucc) =
        (fun i : Fin n ↦ zw.2 i.castSucc.castSucc) := by
    simpa [vinogradovResidualTailSolutionPairProjectionTwo] using
      congrArg Prod.fst htailProjection
  have horientation :
      decide
          ((xy.2 (Fin.last n).castSucc).val ≤
            (xy.2 (Fin.last (n + 1))).val) =
        decide
          ((zw.2 (Fin.last n).castSucc).val ≤
            (zw.2 (Fin.last (n + 1))).val) := by
    simpa [vinogradovResidualTailSolutionPairProjectionTwo] using
      congrArg Prod.snd htailProjection
  let j₁ : Fin k := ⟨0, by omega⟩
  let j₂ : Fin k := ⟨1, by omega⟩
  have hdegree₁ : b * (j₁.val + 1) ≤ B := by
    dsimp [j₁]
    omega
  have hdegree₂ : b * (j₂.val + 1) ≤ B := by
    dsimp [j₂]
    omega
  have hsumModInt := residualTail_lastTwo_powerSum_modEq
    hxySolution hzwSolution hx hprefix j₁ hdegree₁
  have hsqModInt := residualTail_lastTwo_powerSum_modEq
    hxySolution hzwSolution hx hprefix j₂ hdegree₂
  let a := (xy.2 (Fin.last n).castSucc).val + 1
  let c := (xy.2 (Fin.last (n + 1))).val + 1
  let u := (zw.2 (Fin.last n).castSucc).val + 1
  let v := (zw.2 (Fin.last (n + 1))).val + 1
  have haY : a ≤ Y := by
    dsimp [a]
    omega
  have hcY : c ≤ Y := by
    dsimp [c]
    omega
  have huY : u ≤ Y := by
    dsimp [u]
    omega
  have hvY : v ≤ Y := by
    dsimp [v]
    omega
  have hsumMod : Nat.ModEq (p ^ (B - b)) (a + c) (u + v) := by
    rw [Nat.modEq_iff_dvd]
    simpa [j₁, a, c, u, v, vinogradovFinTupleInt] using hsumModInt.dvd
  have hsqMod :
      Nat.ModEq (p ^ (B - 2 * b))
        (a ^ 2 + c ^ 2) (u ^ 2 + v ^ 2) := by
    rw [Nat.modEq_iff_dvd]
    simpa [j₂, a, c, u, v, vinogradovFinTupleInt,
      Nat.mul_comm] using hsqModInt.dvd
  have hsum :
      a + c = u + v :=
    hsumMod.eq_of_lt_of_lt
      (lt_of_le_of_lt (by omega) hlinear)
      (lt_of_le_of_lt (by omega) hlinear)
  have haSq : a ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left haY _
  have hcSq : c ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hcY _
  have huSq : u ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left huY _
  have hvSq : v ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hvY _
  have hsq :
      a ^ 2 + c ^ 2 = u ^ 2 + v ^ 2 :=
    hsqMod.eq_of_lt_of_lt
      (lt_of_le_of_lt (by omega) hquadratic)
      (lt_of_le_of_lt (by omega) hquadratic)
  have horientationNat :
      decide (a ≤ c) = decide (u ≤ v) := by
    dsimp [a, c, u, v]
    simpa only [Nat.add_le_add_iff_right] using horientation
  have horientationIff :
      (a ≤ c) ↔ (u ≤ v) := by
    exact decide_eq_decide.mp horientationNat
  have hyzLast :
      xy.2 (Fin.last n).castSucc = zw.2 (Fin.last n).castSucc ∧
        xy.2 (Fin.last (n + 1)) = zw.2 (Fin.last (n + 1)) := by
    rcases pair_eq_or_swap_of_sum_sq hsum hsq with hdirect | hswap
    · constructor <;> apply Fin.ext <;> omega
    · have hac : a = c := by
        have hacIff : (a ≤ c) ↔ (c ≤ a) := by
          simpa [hswap.1, hswap.2] using horientationIff
        rcases Nat.le_total a c with hac | hca
        · exact Nat.le_antisymm hac (hacIff.mp hac)
        · exact Nat.le_antisymm (hacIff.mpr hca) hca
      constructor <;> apply Fin.ext <;> omega
  have hy : xy.2 = zw.2 := by
    funext i
    exact Fin.lastCases hyzLast.2
      (fun q ↦ Fin.lastCases hyzLast.1
        (fun r ↦ congrFun hprefix r) q) i
  exact Prod.ext hx hy

/-- The first two residual congruences save two full factors of `Y`, up to
the transposition factor `2`. -/
theorem card_vinogradovResidualTailSolutionPairSet_le_quadratic
    (p B b k n Y : ℕ) (hk : 2 ≤ k) (h2bB : 2 * b ≤ B)
    (hlinear : 2 * Y < p ^ (B - b))
    (hquadratic : 2 * Y ^ 2 < p ^ (B - 2 * b)) :
    (vinogradovResidualTailSolutionPairSet
        p B b k (n + 2) Y).card ≤ 2 * Y ^ (2 * n + 2) := by
  classical
  have hcard := Finset.card_le_card_of_injOn
    (vinogradovResidualTailSolutionPairProjectionTwo n Y)
    (s := vinogradovResidualTailSolutionPairSet p B b k (n + 2) Y)
    (t := Finset.univ)
    (by intro xy hxy; simp)
    (vinogradovResidualTailSolutionPairProjectionTwo_injOn
      p B b k n Y hk h2bB hlinear hquadratic)
  have hcard' :
      (vinogradovResidualTailSolutionPairSet
          p B b k (n + 2) Y).card ≤ Y ^ (n + 2) * (Y ^ n * 2) := by
    simpa using hcard
  calc
    (vinogradovResidualTailSolutionPairSet
        p B b k (n + 2) Y).card ≤ Y ^ (n + 2) * (Y ^ n * 2) := hcard'
    _ = 2 * (Y ^ (n + 2) * Y ^ n) := by ac_rfl
    _ = 2 * Y ^ (2 * n + 2) := by
      rw [← pow_add]
      congr 2
      omega

/-- Quadratic residual rigidity transfers the two-variable saving directly
to the separated affine-tail moment. -/
theorem normalizedVinogradovMixedTailNormMoment_le_quadratic
    (p B b k n Y : ℕ) [NeZero (p ^ B)] (hp : p ≠ 0)
    (hk : 2 ≤ k) (h2bB : 2 * b ≤ B)
    (hlinear : 2 * Y < p ^ (B - b))
    (hquadratic : 2 * Y ^ 2 < p ^ (B - 2 * b))
    (eta : ℤ) :
    normalizedVinogradovMixedTailNormMoment
        p B b k (n + 2) Y eta ≤ 2 * (Y : ℝ) ^ (2 * n + 2) := by
  calc
    normalizedVinogradovMixedTailNormMoment
        p B b k (n + 2) Y eta ≤
      (vinogradovResidualTailSolutionPairSet
        p B b k (n + 2) Y).card :=
      normalizedVinogradovMixedTailNormMoment_le_residualSolutionPairSetCard
        p B b k (n + 2) Y hp eta
    _ ≤ 2 * (Y : ℝ) ^ (2 * n + 2) := by
      exact_mod_cast
        card_vinogradovResidualTailSolutionPairSet_le_quadratic
          p B b k n Y hk h2bB hlinear hquadratic

end

end ZeroFreeRegion.VinogradovKorobov
