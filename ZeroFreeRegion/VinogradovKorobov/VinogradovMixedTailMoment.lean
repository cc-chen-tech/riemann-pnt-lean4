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

end

end ZeroFreeRegion.VinogradovKorobov
