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
