import ZeroFreeRegion.VinogradovKorobov.VinogradovFarScaleElimination
import ZeroFreeRegion.VinogradovKorobov.VinogradovWeightedConditioning

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The terms of the affine binomial expansion through degree `r`. -/
def vinogradovAffineTruncation {s : ℕ}
    (ξ q : ℤ) (x y : Fin s → ℤ) (n r : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (r + 1),
    (n.choose m : ℤ) * ξ ^ (n - m) * q ^ m *
      vinogradovPowerSumDifferenceInt x y m

/-- The terms above degree `r` in the affine binomial expansion. -/
def vinogradovAffineTail {s : ℕ}
    (ξ q : ℤ) (x y : Fin s → ℤ) (n r : ℕ) : ℤ :=
  ∑ m ∈ Finset.Ico (r + 1) (n + 1),
    (n.choose m : ℤ) * ξ ^ (n - m) * q ^ m *
      vinogradovPowerSumDifferenceInt x y m

/-- Exact decomposition of an affine power-sum difference into its first
`r` degrees and the remaining high-degree tail. -/
theorem vinogradovPowerSumDifferenceInt_affine_eq_truncation_add_tail
    {s : ℕ} (ξ q : ℤ) (x y : Fin s → ℤ) (n r : ℕ) :
    vinogradovPowerSumDifferenceInt
        (fun i ↦ ξ + q * x i) (fun i ↦ ξ + q * y i) n =
      vinogradovAffineTruncation ξ q x y n r +
        vinogradovAffineTail ξ q x y n r := by
  rw [vinogradovPowerSumDifferenceInt_affine]
  by_cases hrn : r ≤ n
  · exact (Finset.sum_range_add_sum_Ico _ (Nat.succ_le_succ hrn)).symm
  · have hnr : n < r := Nat.lt_of_not_ge hrn
    let f : ℕ → ℤ := fun m ↦
      (n.choose m : ℤ) * ξ ^ (n - m) * q ^ m *
        vinogradovPowerSumDifferenceInt x y m
    have hextra : ∑ m ∈ Finset.Ico (n + 1) (r + 1), f m = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hnm : n < m := by
        simp only [Finset.mem_Ico] at hm
        omega
      simp only [f, Nat.choose_eq_zero_of_lt hnm, Nat.cast_zero, zero_mul]
    have hsplit := Finset.sum_range_add_sum_Ico f
      (Nat.succ_le_succ (Nat.le_of_lt hnr))
    have htail : Finset.Ico (r + 1) (n + 1) = ∅ :=
      Finset.Ico_eq_empty (by omega)
    unfold vinogradovAffineTruncation vinogradovAffineTail
    rw [htail, Finset.sum_empty, add_zero]
    simpa only [f, hextra, add_zero] using hsplit

/-- Every high-degree tail has the expected common factor `q^(r+1)`. -/
theorem vinogradovAffineTail_modEq_zero {s : ℕ}
    (ξ q : ℤ) (x y : Fin s → ℤ) (n r : ℕ) :
    vinogradovAffineTail ξ q x y n r ≡ 0 [ZMOD q ^ (r + 1)] := by
  unfold vinogradovAffineTail
  simpa only [Finset.sum_const_zero] using Int.ModEq.sum (s := Finset.Ico (r + 1) (n + 1))
    (f := fun m ↦
      (n.choose m : ℤ) * ξ ^ (n - m) * q ^ m *
        vinogradovPowerSumDifferenceInt x y m)
    (g := fun _ ↦ 0) (by
  intro m hm
  simp only [Finset.mem_Ico] at hm
  rw [Int.modEq_zero_iff_dvd]
  obtain ⟨z, hz⟩ := pow_dvd_pow q hm.1
  refine ⟨(n.choose m : ℤ) * ξ ^ (n - m) * z *
    vinogradovPowerSumDifferenceInt x y m, ?_⟩
  dsimp
  rw [hz]
  ring)

/-- At a prime-power scale, the tail vanishes modulo every lower exponent
`M ≤ a(r+1)`. -/
theorem vinogradovAffineTail_primePower_modEq_zero_of_le {s : ℕ}
    (p a M : ℕ) (ξ : ℤ) (x y : Fin s → ℤ) (n r : ℕ)
    (hM : M ≤ a * (r + 1)) :
    vinogradovAffineTail ξ ((p : ℤ) ^ a) x y n r ≡ 0
      [ZMOD (p : ℤ) ^ M] := by
  have htail := vinogradovAffineTail_modEq_zero
    ξ ((p : ℤ) ^ a) x y n r
  have hdvd : (p : ℤ) ^ M ∣ (p : ℤ) ^ (a * (r + 1)) :=
    pow_dvd_pow (p : ℤ) hM
  apply htail.of_dvd
  simpa only [pow_mul] using hdvd

/-- The affine power-sum difference is congruent to its degree-`r`
truncation modulo `q^(r+1)`. -/
theorem vinogradovPowerSumDifferenceInt_affine_modEq_truncation
    {s : ℕ} (ξ q : ℤ) (x y : Fin s → ℤ) (n r : ℕ) :
    vinogradovPowerSumDifferenceInt
        (fun i ↦ ξ + q * x i) (fun i ↦ ξ + q * y i) n ≡
      vinogradovAffineTruncation ξ q x y n r [ZMOD q ^ (r + 1)] := by
  rw [vinogradovPowerSumDifferenceInt_affine_eq_truncation_add_tail
    ξ q x y n r]
  simpa using (Int.ModEq.refl (vinogradovAffineTruncation ξ q x y n r)).add
    (vinogradovAffineTail_modEq_zero ξ q x y n r)

/-- Since the degree-zero power-sum difference vanishes, the truncation is
exactly a sum over the positive degrees `1, ..., r`. -/
theorem vinogradovAffineTruncation_eq_sum_fin {s : ℕ}
    (ξ q : ℤ) (x y : Fin s → ℤ) (n r : ℕ) :
    vinogradovAffineTruncation ξ q x y n r =
      ∑ j : Fin r,
        (n.choose (j.val + 1) : ℤ) * ξ ^ (n - (j.val + 1)) *
          q ^ (j.val + 1) *
            vinogradovPowerSumDifferenceInt x y (j.val + 1) := by
  rw [vinogradovAffineTruncation,
    ← Fin.sum_univ_eq_sum_range (fun m ↦
      (n.choose m : ℤ) * ξ ^ (n - m) * q ^ m *
        vinogradovPowerSumDifferenceInt x y m) (r + 1),
    Fin.sum_univ_succ]
  simp

/-- Paper-facing high-degree expansion.  The row indexed by `i` has outer
degree `k-r+1+i`; its low-degree coefficients are precisely the consecutive
binomial matrix used by the later elimination module. -/
theorem vinogradovHighDegree_affine_expansion {s : ℕ}
    (ξ q : ℤ) (x y : Fin s → ℤ) (k r : ℕ)
    (i : Fin r) :
    vinogradovPowerSumDifferenceInt
        (fun z ↦ ξ + q * x z) (fun z ↦ ξ + q * y z)
        (vinogradovBinomialPoint k r i) =
      (∑ j : Fin r,
        (Nat.choose (vinogradovBinomialPoint k r i) (j.val + 1) : ℤ) *
          ξ ^ (vinogradovBinomialPoint k r i - (j.val + 1)) *
          q ^ (j.val + 1) *
            vinogradovPowerSumDifferenceInt x y (j.val + 1)) +
      vinogradovAffineTail ξ q x y
        (vinogradovBinomialPoint k r i) r := by
  rw [vinogradovPowerSumDifferenceInt_affine_eq_truncation_add_tail
    ξ q x y (vinogradovBinomialPoint k r i) r,
    vinogradovAffineTruncation_eq_sum_fin]

/-- The exact integer binomial matrix attached to the consecutive high
degrees `k-r+1, ..., k`. -/
def vinogradovPureBinomialIntMatrix (k r : ℕ) :
    Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of fun i j ↦
    (Nat.choose (vinogradovBinomialPoint k r i) (j.val + 1) : ℤ)

theorem vinogradovPureBinomialIntMatrix_isVinogradov
    (p k r : ℕ) :
    IsVinogradovBinomialCoefficientMatrix p k r
      (vinogradovPureBinomialIntMatrix k r) := by
  intro i j
  exact Int.ModEq.refl _

/-- The column-aligned low-degree power-sum vector. -/
def vinogradovAlignedAffinePowerSumDifference {s r : ℕ}
    (ξ q : ℤ) (k : ℕ) (x y : Fin s → ℤ) (j : Fin r) : ℤ :=
  ξ ^ (k - (j.val + 1)) * q ^ (j.val + 1) *
    vinogradovPowerSumDifferenceInt x y (j.val + 1)

/-- Multiplying row `i` by the complementary center power aligns all
binomial coefficients with the same column vector. -/
theorem vinogradovHighDegree_lowSum_row_alignment {s : ℕ}
    (ξ q : ℤ) (x y : Fin s → ℤ) (k r : ℕ) (hrk : r ≤ k)
    (i : Fin r) :
    ξ ^ (k - vinogradovBinomialPoint k r i) *
        (∑ j : Fin r,
          (Nat.choose (vinogradovBinomialPoint k r i) (j.val + 1) : ℤ) *
            ξ ^ (vinogradovBinomialPoint k r i - (j.val + 1)) *
            q ^ (j.val + 1) *
              vinogradovPowerSumDifferenceInt x y (j.val + 1)) =
      ∑ j : Fin r,
        vinogradovPureBinomialIntMatrix k r i j *
          vinogradovAlignedAffinePowerSumDifference ξ q k x y j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val + 1 ≤ vinogradovBinomialPoint k r i
  · have hpointk : vinogradovBinomialPoint k r i ≤ k := by
      simp only [vinogradovBinomialPoint]
      omega
    have hexponent :
        k - vinogradovBinomialPoint k r i +
            (vinogradovBinomialPoint k r i - (j.val + 1)) =
          k - (j.val + 1) := by omega
    simp only [vinogradovPureBinomialIntMatrix, Matrix.of_apply,
      vinogradovAlignedAffinePowerSumDifference]
    have hpow :
        ξ ^ (k - vinogradovBinomialPoint k r i) *
            ξ ^ (vinogradovBinomialPoint k r i - (j.val + 1)) =
          ξ ^ (k - (j.val + 1)) := by
      rw [← pow_add, hexponent]
    calc
      ξ ^ (k - vinogradovBinomialPoint k r i) *
          ((Nat.choose (vinogradovBinomialPoint k r i) (j.val + 1) : ℤ) *
            ξ ^ (vinogradovBinomialPoint k r i - (j.val + 1)) *
            q ^ (j.val + 1) *
              vinogradovPowerSumDifferenceInt x y (j.val + 1)) =
        (Nat.choose (vinogradovBinomialPoint k r i) (j.val + 1) : ℤ) *
          (ξ ^ (k - vinogradovBinomialPoint k r i) *
            ξ ^ (vinogradovBinomialPoint k r i - (j.val + 1))) *
          q ^ (j.val + 1) *
            vinogradovPowerSumDifferenceInt x y (j.val + 1) := by ring
      _ = (Nat.choose (vinogradovBinomialPoint k r i) (j.val + 1) : ℤ) *
          (ξ ^ (k - (j.val + 1)) * q ^ (j.val + 1) *
            vinogradovPowerSumDifferenceInt x y (j.val + 1)) := by
            rw [hpow]
            ring
  · have hpointj : vinogradovBinomialPoint k r i < j.val + 1 :=
      Nat.lt_of_not_ge hj
    simp only [vinogradovPureBinomialIntMatrix, Matrix.of_apply,
      vinogradovAlignedAffinePowerSumDifference,
      Nat.choose_eq_zero_of_lt hpointj, Nat.cast_zero, zero_mul, mul_zero]

/-- Raw monomial high-degree congruences, together with vanishing of their
high-degree tails, produce the homogeneous binomial system consumed by the
prime-power elimination theorem. -/
theorem vinogradovHighDegree_homogeneousSystem_of_tail {s : ℕ}
    (p k r M : ℕ) (hrk : r ≤ k) (ξ q : ℤ) (x y : Fin s → ℤ)
    (hraw : ∀ i : Fin r,
      vinogradovPowerSumDifferenceInt
          (fun z ↦ ξ + q * x z) (fun z ↦ ξ + q * y z)
          (vinogradovBinomialPoint k r i) ≡ 0
        [ZMOD (p : ℤ) ^ M])
    (htail : ∀ i : Fin r,
      vinogradovAffineTail ξ q x y
          (vinogradovBinomialPoint k r i) r ≡ 0
        [ZMOD (p : ℤ) ^ M]) :
    IsVinogradovHomogeneousCongruenceSystem p M r
      (vinogradovPureBinomialIntMatrix k r)
      (vinogradovAlignedAffinePowerSumDifference ξ q k x y) := by
  intro i
  have hrow := hraw i
  rw [vinogradovHighDegree_affine_expansion] at hrow
  have hlow := hrow.sub (htail i)
  simp only [add_sub_cancel_right, sub_zero] at hlow
  have haligned := hlow.mul_left
    (ξ ^ (k - vinogradovBinomialPoint k r i))
  rw [vinogradovHighDegree_lowSum_row_alignment ξ q x y k r hrk i] at haligned
  simpa only [IsVinogradovHomogeneousCongruenceSystem, mul_zero] using haligned

/-- Specializing the aligned vector to a center `ω p^γ` and scale `p^a`
gives the valuation-separated vector used by far-scale cancellation. -/
theorem vinogradovAlignedAffinePowerSumDifference_primePower {s r : ℕ}
    (p k a γ : ℕ) (ω : ℤ) (x y : Fin s → ℤ) (j : Fin r) :
    vinogradovAlignedAffinePowerSumDifference
        (ω * (p : ℤ) ^ γ) ((p : ℤ) ^ a) k x y j =
      vinogradovAlignedFarScaleDifference p k a γ ω
        (fun l ↦ vinogradovPowerSumDifferenceInt x y (l.val + 1)) j := by
  simp only [vinogradovAlignedAffinePowerSumDifference,
    vinogradovAlignedFarScaleDifference, mul_pow, ← pow_mul]
  ring

/-- Pure-monomial far-scale elimination.  This closes the complete algebraic
passage from the high-degree affine congruences to common lower-degree
congruences modulo `p^B'`, provided the explicit high-degree tails vanish at
the ambient modulus. -/
theorem vinogradovMonomial_highDegree_to_farScale {s : ℕ}
    (p k r a b γ : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b) (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω) (x y : Fin s → ℤ)
    (hraw : ∀ i : Fin r,
      vinogradovPowerSumDifferenceInt
          (fun z ↦ ω * (p : ℤ) ^ γ + (p : ℤ) ^ a * x z)
          (fun z ↦ ω * (p : ℤ) ^ γ + (p : ℤ) ^ a * y z)
          (vinogradovBinomialPoint k r i) ≡ 0
        [ZMOD (p : ℤ) ^ ((k - r + 1) * b)])
    (htail : ∀ i : Fin r,
      vinogradovAffineTail (ω * (p : ℤ) ^ γ) ((p : ℤ) ^ a) x y
          (vinogradovBinomialPoint k r i) r ≡ 0
        [ZMOD (p : ℤ) ^ ((k - r + 1) * b)]) :
    ∀ j : Fin r,
      vinogradovPowerSumDifferenceInt x y (j.val + 1) ≡ 0
        [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] := by
  let d : Fin r → ℤ := fun j ↦
    vinogradovPowerSumDifferenceInt x y (j.val + 1)
  have hsystem := vinogradovHighDegree_homogeneousSystem_of_tail
    p k r ((k - r + 1) * b) hrk
      (ω * (p : ℤ) ^ γ) ((p : ℤ) ^ a) x y hraw htail
  have haligned := vinogradovBinomial_homogeneous_elimination
    p k r ((k - r + 1) * b) hrk hkp
      (Nat.mul_pos (Nat.succ_pos _) hb)
      (vinogradovPureBinomialIntMatrix k r)
      (vinogradovPureBinomialIntMatrix_isVinogradov p k r)
      (vinogradovAlignedAffinePowerSumDifference
        (ω * (p : ℤ) ^ γ) ((p : ℤ) ^ a) k x y) hsystem
  apply vinogradovAlignedCongruences_to_farScale
    p k r a b γ (Fact.out : p.Prime).ne_zero hrk hγa hbudget ω hω d
  intro j
  simpa only [d, vinogradovAlignedAffinePowerSumDifference_primePower]
    using haligned j

/-- In the range `(k-r+1)b ≤ a(r+1)`, the affine tail is automatically
absorbed by the ambient modulus, so the raw high-degree monomial congruences
alone imply the far-scale system. -/
theorem vinogradovMonomial_highDegree_to_farScale_of_tailScale {s : ℕ}
    (p k r a b γ : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b) (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (htailScale : (k - r + 1) * b ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω) (x y : Fin s → ℤ)
    (hraw : ∀ i : Fin r,
      vinogradovPowerSumDifferenceInt
          (fun z ↦ ω * (p : ℤ) ^ γ + (p : ℤ) ^ a * x z)
          (fun z ↦ ω * (p : ℤ) ^ γ + (p : ℤ) ^ a * y z)
          (vinogradovBinomialPoint k r i) ≡ 0
        [ZMOD (p : ℤ) ^ ((k - r + 1) * b)]) :
    ∀ j : Fin r,
      vinogradovPowerSumDifferenceInt x y (j.val + 1) ≡ 0
        [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] := by
  apply vinogradovMonomial_highDegree_to_farScale
    p k r a b γ hrk hkp hb hγa hbudget ω hω x y hraw
  intro i
  exact vinogradovAffineTail_primePower_modEq_zero_of_le
    p a ((k - r + 1) * b) (ω * (p : ℤ) ^ γ) x y
      (vinogradovBinomialPoint k r i) r htailScale

end

end ZeroFreeRegion.VinogradovKorobov
