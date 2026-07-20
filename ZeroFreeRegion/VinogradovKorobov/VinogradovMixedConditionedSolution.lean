import ZeroFreeRegion.VinogradovKorobov.VinogradovCongruence
import ZeroFreeRegion.VinogradovKorobov.VinogradovHighDegreeExpansion
import ZeroFreeRegion.VinogradovKorobov.VinogradovTranslatedMeanValue

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Two ordered tuple pairs: a main block of length `r` and a restricted
block of length `t`. -/
abbrev VinogradovMixedTuplePairs (r t X Y : ℕ) :=
  ((Fin r → Fin X) × (Fin r → Fin X)) ×
    ((Fin t → Fin Y) × (Fin t → Fin Y))

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
