import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedHolder
import ZeroFreeRegion.VinogradovKorobov.VinogradovWeightedConditioning

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

end

end ZeroFreeRegion.VinogradovKorobov
