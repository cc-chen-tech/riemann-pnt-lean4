import PrimeNumberTheorem.ZeroDensityCount
import PrimeNumberTheorem.QuantitativeGoodHeight
import PrimeNumberTheorem.VKEdgeHighZeroBucketEnergy

open Complex Filter Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem

open VKEdgePiOverTwo

/-- A pointwise multiplicity cap upgrades a nonnegative linear capacity to a
square-multiplicity capacity. -/
theorem squareMultiplicityCapacity_le_max_mul_linearMultiplicityCapacity
    {α : Type*} [DecidableEq α] (R : Finset α) (m w : α → ℝ) (M : ℝ)
    (hm0 : ∀ a ∈ R, 0 ≤ m a) (hw0 : ∀ a ∈ R, 0 ≤ w a)
    (hmM : ∀ a ∈ R, m a ≤ M) :
    (∑ a ∈ R, m a ^ 2 * w a) ≤ M * ∑ a ∈ R, m a * w a := by
  calc
    (∑ a ∈ R, m a ^ 2 * w a) ≤ ∑ a ∈ R, M * (m a * w a) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [show m a ^ 2 * w a = m a * (m a * w a) by ring]
      exact mul_le_mul_of_nonneg_right (hmM a ha) (mul_nonneg (hm0 a ha) (hw0 a ha))
    _ = M * ∑ a ∈ R, m a * w a := by rw [Finset.mul_sum]

/-- Deleting a finite exceptional set cannot increase a nonnegative square capacity. -/
theorem squareMultiplicityCapacity_sdiff_le
    {α : Type*} [DecidableEq α] (R S : Finset α) (m w : α → ℝ)
    (hw0 : ∀ a ∈ R, 0 ≤ w a) :
    (∑ a ∈ R \ S, m a ^ 2 * w a) ≤ ∑ a ∈ R, m a ^ 2 * w a := by
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    (fun a ha _ => mul_nonneg (sq_nonneg (m a)) (hw0 a ha))

namespace ExplicitFormulaAux

/-- Above the explicit ordinate threshold, each actual zeta zero has logarithmic multiplicity. -/
theorem exists_analyticOrderNatAt_riemannZeta_le_log_im_of_nontrivialZero :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ rho : ℂ, RiemannHypothesis.IsNontrivialZero rho → 4 ≤ |rho.im| →
      (analyticOrderNatAt riemannZeta rho : ℝ) ≤ B * (1 + Real.log (|rho.im| + 6)) := by
  rcases exists_localZeroMultiplicity_le_log_bound with ⟨B, hB, hlocal⟩
  refine ⟨B, hB, ?_⟩
  intro rho hrho hh
  let A : ℝ := |rho.im|
  let R := (nontrivialZerosFinset (A + 2)).filter fun z : ℂ =>
    A - 1 / 4 ≤ |z.im| ∧ |z.im| ≤ A + 5 / 4
  have hmem : rho ∈ R := by
    refine Finset.mem_filter.mpr ⟨mem_nontrivialZerosFinset.mpr ⟨hrho, by dsimp [A]; linarith⟩, ?_⟩
    dsimp [A]; constructor <;> linarith
  have hsingle : (analyticOrderNatAt riemannZeta rho : ℝ) ≤ ∑ z ∈ R, (analyticOrderNatAt riemannZeta z : ℝ) :=
    Finset.single_le_sum (fun z _ => Nat.cast_nonneg _) hmem
  calc
    _ ≤ ∑ z ∈ R, (analyticOrderNatAt riemannZeta z : ℝ) := hsingle
    _ = localZeroMultiplicity A := rfl
    _ ≤ B * (1 + Real.log (A + 6)) := hlocal A (by simpa [A] using hh)
    _ = _ := rfl

end ExplicitFormulaAux

/-- Actual zeros with absolute ordinate in the half-open dyadic block `[2^k,2^(k+1))`. -/
noncomputable def actualZetaDyadicZeroBlock (k : ℕ) : Finset ℂ :=
  (nontrivialZerosFinset ((2 : ℝ) ^ (k + 1))).filter fun rho =>
    (2 : ℝ) ^ k ≤ |rho.im| ∧ |rho.im| < (2 : ℝ) ^ (k + 1)

/-- The actual half-open dyadic zero block is exactly covered by the unit
ordinate buckets whose natural indices lie in the corresponding closed index
interval.  The forward direction selects `Nat.floor |rho.im|`; the reverse
direction uses the unit-bucket bounds and the truncated-zero membership. -/
theorem mem_actualZetaDyadicZeroBlock_iff_exists_mem_zeroOrdinateUnitBucket
    {k : ℕ} {rho : ℂ} :
    rho ∈ actualZetaDyadicZeroBlock k ↔
      ∃ n ∈ Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1),
        rho ∈ zeroOrdinateUnitBucket n := by
  classical
  constructor
  · intro hrho
    rcases Finset.mem_filter.mp hrho with ⟨hrhoTruncated, hbounds⟩
    let n : ℕ := Nat.floor |rho.im|
    have hfloorBounds :
        (n : ℝ) ≤ |rho.im| ∧ |rho.im| < (n : ℝ) + 1 :=
      (Nat.floor_eq_iff (abs_nonneg rho.im)).1 rfl
    have hnLower : 2 ^ k ≤ n := by
      apply Nat.le_floor
      simpa using hbounds.1
    have hnUpperLt : n < 2 ^ (k + 1) := by
      exact_mod_cast hfloorBounds.1.trans_lt hbounds.2
    have hnUpper : n ≤ 2 ^ (k + 1) - 1 := by omega
    refine ⟨n, Finset.mem_Icc.mpr ⟨hnLower, hnUpper⟩, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hfloorBounds.1, hfloorBounds.2⟩
    apply mem_nontrivialZerosFinset.mpr
    refine ⟨(mem_nontrivialZerosFinset.mp hrhoTruncated).1, ?_⟩
    linarith [hfloorBounds.2]
  · rintro ⟨n, hnIcc, hrhoBucket⟩
    rcases Finset.mem_Icc.mp hnIcc with ⟨hnLower, hnUpper⟩
    rcases Finset.mem_filter.mp hrhoBucket with
      ⟨hrhoTruncated, hunitBounds⟩
    have hupperPos : 0 < 2 ^ (k + 1) := by positivity
    have hnSucc : n + 1 ≤ 2 ^ (k + 1) := by omega
    have hnLowerReal : (2 : ℝ) ^ k ≤ (n : ℝ) := by
      exact_mod_cast hnLower
    have hnSuccReal : (n : ℝ) + 1 ≤ (2 : ℝ) ^ (k + 1) := by
      exact_mod_cast hnSucc
    have hlower : (2 : ℝ) ^ k ≤ |rho.im| :=
      hnLowerReal.trans hunitBounds.1
    have hupper : |rho.im| < (2 : ℝ) ^ (k + 1) :=
      hunitBounds.2.trans_le hnSuccReal
    apply Finset.mem_filter.mpr
    refine ⟨?_, hlower, hupper⟩
    exact mem_nontrivialZerosFinset.mpr
      ⟨(mem_nontrivialZerosFinset.mp hrhoTruncated).1, hupper.le⟩

/-- Finset form of the exact unit-bucket cover of one actual dyadic block. -/
theorem actualZetaDyadicZeroBlock_eq_biUnion_zeroOrdinateUnitBucket
    (k : ℕ) :
    actualZetaDyadicZeroBlock k =
      (Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1)).biUnion
        zeroOrdinateUnitBucket := by
  classical
  ext rho
  rw [mem_actualZetaDyadicZeroBlock_iff_exists_mem_zeroOrdinateUnitBucket]
  simp

noncomputable def actualZetaDyadicLinearReciprocalCapacityExcluding (k : ℕ) (S : Finset ℂ) : ℝ :=
  ∑ rho ∈ actualZetaDyadicZeroBlock k \ S, (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ ^ 2

noncomputable def actualZetaDyadicSquareReciprocalCapacityExcluding (k : ℕ) (S : Finset ℂ) : ℝ :=
  ∑ rho ∈ actualZetaDyadicZeroBlock k \ S, (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2

/-- With an explicit pointwise high-block bound `M` (and with low zeros placed in `S`),
the deleted actual-zeta square reciprocal capacity is at most `M` times its linear capacity. -/
theorem actualZetaDyadicSquareReciprocalCapacityExcluding_le_linear
    (k : ℕ) (S : Finset ℂ) (M : ℝ)
    (hM : ∀ rho ∈ actualZetaDyadicZeroBlock k \ S,
      (analyticOrderNatAt riemannZeta rho : ℝ) ≤ M) :
    actualZetaDyadicSquareReciprocalCapacityExcluding k S ≤
      M * actualZetaDyadicLinearReciprocalCapacityExcluding k S := by
  unfold actualZetaDyadicSquareReciprocalCapacityExcluding actualZetaDyadicLinearReciprocalCapacityExcluding
  simpa only [div_eq_mul_inv] using
    squareMultiplicityCapacity_le_max_mul_linearMultiplicityCapacity
      (actualZetaDyadicZeroBlock k \ S) (fun rho => (analyticOrderNatAt riemannZeta rho : ℝ))
      (fun rho => (‖rho‖ ^ 2)⁻¹) M
      (fun _ _ => Nat.cast_nonneg _) (fun _ _ => inv_nonneg.mpr (sq_nonneg _)) hM

/-- If every zero below the fixed local-multiplicity threshold is placed in
`S`, then one logarithmic dyadic cap controls the deleted square capacity. -/
theorem exists_actualZetaDyadicSquareReciprocalCapacityExcluding_le_log_linear :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, ∀ S : Finset ℂ,
      (∀ rho ∈ actualZetaDyadicZeroBlock k, |rho.im| < 4 → rho ∈ S) →
      actualZetaDyadicSquareReciprocalCapacityExcluding k S ≤
        (B * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 6))) *
          actualZetaDyadicLinearReciprocalCapacityExcluding k S := by
  rcases ExplicitFormulaAux.exists_analyticOrderNatAt_riemannZeta_le_log_im_of_nontrivialZero
    with ⟨B, hB, hpoint⟩
  refine ⟨B, hB, ?_⟩
  intro k S hlow
  apply actualZetaDyadicSquareReciprocalCapacityExcluding_le_linear
  intro rho hrho
  have hnotS : rho ∉ S := (Finset.mem_sdiff.mp hrho).2
  have hblock := (Finset.mem_sdiff.mp hrho).1
  rcases Finset.mem_filter.mp hblock with ⟨hzero, hbounds⟩
  have hheight : 4 ≤ |rho.im| := by
    by_contra h
    exact hnotS (hlow rho hblock (lt_of_not_ge h))
  have hbase := hpoint rho (mem_nontrivialZerosFinset.mp hzero).1 hheight
  have hlog : Real.log (|rho.im| + 6) ≤
      Real.log ((2 : ℝ) ^ (k + 1) + 6) := by
    apply Real.log_le_log
    · positivity
    · linarith [hbounds.2]
  exact hbase.trans (mul_le_mul_of_nonneg_left (by linarith [hlog]) hB)

end PrimeNumberTheorem
