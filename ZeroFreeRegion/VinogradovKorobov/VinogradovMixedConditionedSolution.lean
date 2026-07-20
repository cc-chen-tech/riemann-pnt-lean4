import ZeroFreeRegion.VinogradovKorobov.VinogradovCongruence
import ZeroFreeRegion.VinogradovKorobov.VinogradovHighDegreeExpansion
import ZeroFreeRegion.VinogradovKorobov.VinogradovModularSymmetry
import ZeroFreeRegion.VinogradovKorobov.VinogradovTranslatedMeanValue

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Two ordered tuple pairs: a main block of length `r` and a restricted
block of length `t`. -/
abbrev VinogradovMixedTuplePairs (r t X Y : ℕ) :=
  ((Fin r → Fin X) × (Fin r → Fin X)) ×
    ((Fin t → Fin Y) × (Fin t → Fin Y))

/-- Mixed two-block power-sum congruences modulo the common ambient modulus
`p^B`.  The second block is reconstructed inside the affine residue class
`eta` modulo `p^b`. -/
def IsVinogradovMixedAffineCongruenceInt
    (p B b k r t : ℕ) (eta : ℤ)
    (x y : Fin r → ℤ) (u v : Fin t → ℤ) : Prop :=
  ∀ j : Fin k,
    Int.ModEq ((p : ℤ) ^ B)
      (vinogradovPowerSumDifferenceInt x y (j.val + 1))
      (vinogradovPowerSumDifferenceInt
        (fun i ↦ eta + (p : ℤ) ^ b * u i)
        (fun i ↦ eta + (p : ℤ) ^ b * v i) (j.val + 1))

/-- Centering a mixed modular system at `eta` exposes the exact factor
`p^(b(j+1))` contributed by the restricted block. -/
theorem IsVinogradovMixedAffineCongruenceInt.centered_powerSum_modEq
    {p B b k r t : ℕ} {eta : ℤ}
    {x y : Fin r → ℤ} {u v : Fin t → ℤ}
    (h : IsVinogradovMixedAffineCongruenceInt p B b k r t eta x y u v)
    (j : Fin k) :
    Int.ModEq ((p : ℤ) ^ B)
      (vinogradovPowerSumDifferenceInt
        (fun i ↦ x i - eta) (fun i ↦ y i - eta) (j.val + 1))
      ((p : ℤ) ^ (b * (j.val + 1)) *
        vinogradovPowerSumDifferenceInt u v (j.val + 1)) := by
  let q : ℤ := (p : ℤ) ^ b
  have hjoin :
      IsVinogradovSolutionIntMod (p ^ B) k (r + t)
        (vinogradovJoinTuple x (fun i ↦ eta + q * v i))
        (vinogradovJoinTuple y (fun i ↦ eta + q * u i)) := by
    intro l
    rw [vinogradovPowerSumInt_joinTuple,
      vinogradovPowerSumInt_joinTuple]
    have hl := h l
    change Int.ModEq ((p : ℤ) ^ B)
      (vinogradovPowerSumInt x l - vinogradovPowerSumInt y l)
      (vinogradovPowerSumInt (fun i ↦ eta + q * u i) l -
        vinogradovPowerSumInt (fun i ↦ eta + q * v i) l) at hl
    have hadd := hl.add_right
      (vinogradovPowerSumInt y l +
        vinogradovPowerSumInt (fun i ↦ eta + q * v i) l)
    convert hadd using 1 <;> ring
  have htranslated := hjoin.translate (-eta)
  have hleft :
      (fun i : Fin (r + t) ↦
        vinogradovJoinTuple x (fun z ↦ eta + q * v z) i + -eta) =
      vinogradovJoinTuple (fun z ↦ x z - eta) (fun z ↦ q * v z) := by
    funext i
    obtain ⟨z, rfl⟩ := finSumFinEquiv.surjective i
    rcases z with z | z <;>
      simp [vinogradovJoinTuple] <;> ring
  have hright :
      (fun i : Fin (r + t) ↦
        vinogradovJoinTuple y (fun z ↦ eta + q * u z) i + -eta) =
      vinogradovJoinTuple (fun z ↦ y z - eta) (fun z ↦ q * u z) := by
    funext i
    obtain ⟨z, rfl⟩ := finSumFinEquiv.surjective i
    rcases z with z | z <;>
      simp [vinogradovJoinTuple] <;> ring
  have hj := htranslated j
  rw [hleft, hright, vinogradovPowerSumInt_joinTuple,
    vinogradovPowerSumInt_joinTuple] at hj
  have hscale (z : Fin t → ℤ) :
      vinogradovPowerSumInt (fun i ↦ q * z i) j =
        (p : ℤ) ^ (b * (j.val + 1)) * vinogradovPowerSumInt z j := by
    simp [vinogradovPowerSumInt, mul_pow, ← Finset.mul_sum, q, pow_mul]
  rw [hscale v, hscale u] at hj
  have hrearranged := hj.add_right
    (-(vinogradovPowerSumInt (fun i ↦ y i - eta) j +
      (p : ℤ) ^ (b * (j.val + 1)) * vinogradovPowerSumInt v j))
  simpa only [vinogradovPowerSumDifferenceInt, vinogradovPowerSumInt] using
    (show Int.ModEq ((p : ℤ) ^ B)
      (vinogradovPowerSumInt (fun i ↦ x i - eta) j -
        vinogradovPowerSumInt (fun i ↦ y i - eta) j)
      ((p : ℤ) ^ (b * (j.val + 1)) *
        (vinogradovPowerSumInt u j - vinogradovPowerSumInt v j)) by
      convert hrearranged using 1 <;> ring)

/-- Once the common ambient exponent is no larger than the restricted-block
factor, the centered main power-sum difference vanishes modulo `p^B`. -/
theorem IsVinogradovMixedAffineCongruenceInt.centered_modEq
    {p B b k r t : ℕ} {eta : ℤ}
    {x y : Fin r → ℤ} {u v : Fin t → ℤ}
    (h : IsVinogradovMixedAffineCongruenceInt p B b k r t eta x y u v)
    (j : Fin k) (hB : B ≤ b * (j.val + 1)) :
    vinogradovPowerSumDifferenceInt
        (fun i ↦ x i - eta) (fun i ↦ y i - eta) (j.val + 1) ≡ 0
      [ZMOD (p : ℤ) ^ B] := by
  apply (h.centered_powerSum_modEq j).trans
  rw [Int.modEq_zero_iff_dvd]
  exact dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) hB) _

/-- Membership predicate for the modular two-block system counted by a
finite Fourier conditioned moment. -/
def VinogradovMixedModConditionedSolutionMem
    (p B a b k r t X Y : ℕ) (xi eta : ℤ)
    (z : VinogradovMixedTuplePairs r t X Y) : Prop :=
  (∀ i, Int.ModEq ((p : ℤ) ^ a) xi (vinogradovFinTupleInt z.1.1 i)) ∧
    (∀ i, Int.ModEq ((p : ℤ) ^ a) xi (vinogradovFinTupleInt z.1.2 i)) ∧
    IsVinogradovMixedAffineCongruenceInt p B b k r t eta
      (vinogradovFinTupleInt z.1.1) (vinogradovFinTupleInt z.1.2)
      (vinogradovFinTupleInt z.2.1) (vinogradovFinTupleInt z.2.2)

/-- The finite modular mixed conditioned solution set. -/
noncomputable def vinogradovMixedModConditionedSolutionSet
    (p B a b k r t X Y : ℕ) (xi eta : ℤ) :
    Finset (VinogradovMixedTuplePairs r t X Y) := by
  classical
  exact Finset.univ.filter
    (VinogradovMixedModConditionedSolutionMem
      p B a b k r t X Y xi eta)

theorem mem_vinogradovMixedModConditionedSolutionSet_iff
    (p B a b k r t X Y : ℕ) (xi eta : ℤ)
    (z : VinogradovMixedTuplePairs r t X Y) :
    z ∈ vinogradovMixedModConditionedSolutionSet
        p B a b k r t X Y xi eta ↔
      VinogradovMixedModConditionedSolutionMem
        p B a b k r t X Y xi eta z := by
  classical
  simp [vinogradovMixedModConditionedSolutionSet]

/-- The modular two-block system at ambient scale `(k-r+1)b` feeds directly
into the far-scale elimination after extracting affine coordinates from the
main residue class. -/
theorem VinogradovMixedModConditionedSolutionMem.exists_farScale_powerSumCongruences
    {p a b k r t X Y γ : ℕ} [Fact p.Prime]
    {xi eta omega : ℤ} {z : VinogradovMixedTuplePairs r t X Y}
    (h : VinogradovMixedModConditionedSolutionMem
      p ((k - r + 1) * b) a b k r t X Y xi eta z)
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b) (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hcenter : xi - eta = omega * (p : ℤ) ^ γ)
    (homega : IsCoprime (p : ℤ) omega) :
    ∃ x' y' : Fin r → ℤ,
      vinogradovFinTupleInt z.1.1 =
          (fun i ↦ xi + (p : ℤ) ^ a * x' i) ∧
        vinogradovFinTupleInt z.1.2 =
          (fun i ↦ xi + (p : ℤ) ^ a * y' i) ∧
        ∀ j : Fin r,
          vinogradovPowerSumDifferenceInt x' y' (j.val + 1) ≡ 0
            [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] := by
  obtain ⟨x', hx'⟩ := exists_affineCoordinates_of_forall_modEq
    (vinogradovFinTupleInt z.1.1) xi ((p : ℤ) ^ a) h.1
  obtain ⟨y', hy'⟩ := exists_affineCoordinates_of_forall_modEq
    (vinogradovFinTupleInt z.1.2) xi ((p : ℤ) ^ a) h.2.1
  have hxCenter :
      (fun i ↦ vinogradovFinTupleInt z.1.1 i - eta) =
        (fun i ↦ omega * (p : ℤ) ^ γ + (p : ℤ) ^ a * x' i) := by
    funext i
    rw [congrFun hx' i, ← hcenter]
    ring
  have hyCenter :
      (fun i ↦ vinogradovFinTupleInt z.1.2 i - eta) =
        (fun i ↦ omega * (p : ℤ) ^ γ + (p : ℤ) ^ a * y' i) := by
    funext i
    rw [congrFun hy' i, ← hcenter]
    ring
  have hraw : ∀ i : Fin r,
      vinogradovPowerSumDifferenceInt
          (fun q ↦ omega * (p : ℤ) ^ γ + (p : ℤ) ^ a * x' q)
          (fun q ↦ omega * (p : ℤ) ^ γ + (p : ℤ) ^ a * y' q)
          (vinogradovBinomialPoint k r i) ≡ 0
        [ZMOD (p : ℤ) ^ ((k - r + 1) * b)] := by
    intro i
    have hpointPos : 0 < vinogradovBinomialPoint k r i := by
      simp only [vinogradovBinomialPoint]
      omega
    have hpointLe : vinogradovBinomialPoint k r i ≤ k := by
      simp only [vinogradovBinomialPoint]
      omega
    let row : Fin k :=
      ⟨vinogradovBinomialPoint k r i - 1, by omega⟩
    have hrowDegree : row.val + 1 = vinogradovBinomialPoint k r i := by
      dsimp only [row]
      omega
    have hbasePoint : k - r + 1 ≤ vinogradovBinomialPoint k r i := by
      simp only [vinogradovBinomialPoint]
      omega
    have hambientExponent :
        (k - r + 1) * b ≤ b * vinogradovBinomialPoint k r i := by
      rw [Nat.mul_comm (k - r + 1) b]
      exact Nat.mul_le_mul_left b hbasePoint
    have hrow := h.2.2.centered_modEq row (by
      simpa only [hrowDegree] using hambientExponent)
    rw [hrowDegree] at hrow
    simpa only [hxCenter, hyCenter] using hrow
  refine ⟨x', y', hx', hy', ?_⟩
  exact vinogradovMonomial_highDegree_to_farScale_of_tailScale
    p k r a b γ hrk hkp hb hγa hbudget htail omega homega x' y' hraw

/-- Membership predicate for the finite two-block system underlying
Wooley's conditioned mean value.  The main pair lies in one residue class
modulo `p^a`; the second pair is reconstructed in the affine class `eta`
modulo `p^b`; and the two power-sum differences agree through degree `k`. -/
def VinogradovMixedConditionedSolutionMem
    (p a b k r t X Y : ℕ) (xi eta : ℤ)
    (z : VinogradovMixedTuplePairs r t X Y) : Prop :=
  (∀ i, Int.ModEq ((p : ℤ) ^ a) xi (vinogradovFinTupleInt z.1.1 i)) ∧
    (∀ i, Int.ModEq ((p : ℤ) ^ a) xi (vinogradovFinTupleInt z.1.2 i)) ∧
    IsVinogradovMixedAffineEquationInt p b k r t eta
      (vinogradovFinTupleInt z.1.1) (vinogradovFinTupleInt z.1.2)
      (vinogradovFinTupleInt z.2.1) (vinogradovFinTupleInt z.2.2)

/-- The finite solution set counted by the two-block conditioned system. -/
noncomputable def vinogradovMixedConditionedSolutionSet
    (p a b k r t X Y : ℕ) (xi eta : ℤ) :
    Finset (VinogradovMixedTuplePairs r t X Y) := by
  classical
  exact Finset.univ.filter
    (VinogradovMixedConditionedSolutionMem p a b k r t X Y xi eta)

/-- Membership in the finite set is exactly the two residue restrictions and
the mixed affine power-sum system. -/
theorem mem_vinogradovMixedConditionedSolutionSet_iff
    (p a b k r t X Y : ℕ) (xi eta : ℤ)
    (z : VinogradovMixedTuplePairs r t X Y) :
    z ∈ vinogradovMixedConditionedSolutionSet
        p a b k r t X Y xi eta ↔
      VinogradovMixedConditionedSolutionMem
        p a b k r t X Y xi eta z := by
  classical
  simp [vinogradovMixedConditionedSolutionSet]

/-- Every member of the mixed conditioned solution set satisfies the strong
degree-weighted congruences after centering the main block at `eta`.  This is
the finite-set form of the passage from Wooley's mixed equations to strong
congruences. -/
theorem VinogradovMixedConditionedSolutionMem.centered_weightedSolution
    {p a b k r t X Y : ℕ} {xi eta : ℤ}
    {z : VinogradovMixedTuplePairs r t X Y}
    (h : VinogradovMixedConditionedSolutionMem
      p a b k r t X Y xi eta z) :
    IsVinogradovWeightedSolutionInt p b k r
      (fun i ↦ vinogradovFinTupleInt z.1.1 i - eta)
      (fun i ↦ vinogradovFinTupleInt z.1.2 i - eta) := by
  exact h.2.2.centered_weightedSolution

/-- The common residue restriction on the main tuple pair supplies affine
coordinates at scale `p^a` for both sides. -/
theorem VinogradovMixedConditionedSolutionMem.exists_main_affineCoordinates
    {p a b k r t X Y : ℕ} {xi eta : ℤ}
    {z : VinogradovMixedTuplePairs r t X Y}
    (h : VinogradovMixedConditionedSolutionMem
      p a b k r t X Y xi eta z) :
    ∃ x' y' : Fin r → ℤ,
      vinogradovFinTupleInt z.1.1 =
          (fun i ↦ xi + (p : ℤ) ^ a * x' i) ∧
        vinogradovFinTupleInt z.1.2 =
          (fun i ↦ xi + (p : ℤ) ^ a * y' i) := by
  obtain ⟨x', hx'⟩ := exists_affineCoordinates_of_forall_modEq
    (vinogradovFinTupleInt z.1.1) xi ((p : ℤ) ^ a) h.1
  obtain ⟨y', hy'⟩ := exists_affineCoordinates_of_forall_modEq
    (vinogradovFinTupleInt z.1.2) xi ((p : ℤ) ^ a) h.2.1
  exact ⟨x', y', hx', hy'⟩

/-- A mixed conditioned solution whose two residue centers differ by
`omega * p^gamma` produces the ordinary degree-`r` Vinogradov congruences at
the residual far scale.  The conclusion retains the affine coordinates, so
later counting arguments can stratify their possible residue classes. -/
theorem VinogradovMixedConditionedSolutionMem.exists_farScale_powerSumCongruences
    {p a b k r t X Y γ : ℕ} [Fact p.Prime]
    {xi eta omega : ℤ} {z : VinogradovMixedTuplePairs r t X Y}
    (h : VinogradovMixedConditionedSolutionMem
      p a b k r t X Y xi eta z)
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b) (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hcenter : xi - eta = omega * (p : ℤ) ^ γ)
    (homega : IsCoprime (p : ℤ) omega) :
    ∃ x' y' : Fin r → ℤ,
      vinogradovFinTupleInt z.1.1 =
          (fun i ↦ xi + (p : ℤ) ^ a * x' i) ∧
        vinogradovFinTupleInt z.1.2 =
          (fun i ↦ xi + (p : ℤ) ^ a * y' i) ∧
        ∀ j : Fin r,
          vinogradovPowerSumDifferenceInt x' y' (j.val + 1) ≡ 0
            [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] := by
  obtain ⟨x', y', hx', hy'⟩ := h.exists_main_affineCoordinates
  have hxCenter :
      (fun i ↦ vinogradovFinTupleInt z.1.1 i - eta) =
        (fun i ↦ omega * (p : ℤ) ^ γ + (p : ℤ) ^ a * x' i) := by
    funext i
    rw [congrFun hx' i]
    rw [← hcenter]
    ring
  have hyCenter :
      (fun i ↦ vinogradovFinTupleInt z.1.2 i - eta) =
        (fun i ↦ omega * (p : ℤ) ^ γ + (p : ℤ) ^ a * y' i) := by
    funext i
    rw [congrFun hy' i]
    rw [← hcenter]
    ring
  have hweighted := h.centered_weightedSolution
  rw [hxCenter, hyCenter] at hweighted
  have hweightedMod :=
    (isVinogradovWeightedSolutionInt_iff_modEq p b k r _ _).mp hweighted
  have hraw : ∀ i : Fin r,
      vinogradovPowerSumDifferenceInt
          (fun q ↦ omega * (p : ℤ) ^ γ + (p : ℤ) ^ a * x' q)
          (fun q ↦ omega * (p : ℤ) ^ γ + (p : ℤ) ^ a * y' q)
          (vinogradovBinomialPoint k r i) ≡ 0
        [ZMOD (p : ℤ) ^ ((k - r + 1) * b)] := by
    intro i
    have hpointPos : 0 < vinogradovBinomialPoint k r i := by
      simp only [vinogradovBinomialPoint]
      omega
    have hpointLe : vinogradovBinomialPoint k r i ≤ k := by
      simp only [vinogradovBinomialPoint]
      omega
    let row : Fin k :=
      ⟨vinogradovBinomialPoint k r i - 1, by omega⟩
    have hrow := hweightedMod row
    have hrowDegree : row.val + 1 = vinogradovBinomialPoint k r i := by
      dsimp only [row]
      omega
    rw [hrowDegree] at hrow
    apply hrow.of_dvd
    apply pow_dvd_pow
    exact Nat.mul_le_mul_right b (by
      simp only [vinogradovBinomialPoint]
      omega)
  refine ⟨x', y', hx', hy', ?_⟩
  exact vinogradovMonomial_highDegree_to_farScale_of_tailScale
    p k r a b γ hrk hkp hb hγa hbudget htail omega homega x' y' hraw

end

end ZeroFreeRegion.VinogradovKorobov
