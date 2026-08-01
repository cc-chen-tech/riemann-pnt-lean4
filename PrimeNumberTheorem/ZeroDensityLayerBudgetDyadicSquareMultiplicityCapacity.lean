import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonDyadicShellMass
import PrimeNumberTheorem.QuantitativeGoodHeight

open Complex Filter Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem

/-- Pure finite-capacity upgrade: a pointwise maximum multiplicity converts a
linear multiplicity capacity into a square multiplicity capacity for every
nonnegative weight. -/
theorem squareMultiplicityCapacity_le_max_mul_linearMultiplicityCapacity
    {α : Type*} [DecidableEq α] (S : Finset α)
    (m w : α → ℝ) (M : ℝ)
    (hm0 : ∀ a ∈ S, 0 ≤ m a) (hw0 : ∀ a ∈ S, 0 ≤ w a)
    (hmM : ∀ a ∈ S, m a ≤ M) :
    (∑ a ∈ S, (m a) ^ 2 * w a) ≤
      M * ∑ a ∈ S, m a * w a := by
  calc
    (∑ a ∈ S, (m a) ^ 2 * w a) ≤
        ∑ a ∈ S, M * (m a * w a) := by
      apply Finset.sum_le_sum
      intro a ha
      calc
        (m a) ^ 2 * w a = m a * (m a * w a) := by ring
        _ ≤ M * (m a * w a) :=
          mul_le_mul_of_nonneg_right (hmM a ha)
            (mul_nonneg (hm0 a ha) (hw0 a ha))
    _ = M * ∑ a ∈ S, m a * w a := by
      rw [Finset.mul_sum]

/-- Removing a finite exceptional set cannot increase a nonnegative weighted
square capacity. -/
theorem squareMultiplicityCapacity_sdiff_le
    {α : Type*} [DecidableEq α] (R S : Finset α)
    (m w : α → ℝ) (hw0 : ∀ a ∈ R, 0 ≤ w a) :
    (∑ a ∈ R \ S, (m a) ^ 2 * w a) ≤
      ∑ a ∈ R, (m a) ^ 2 * w a := by
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    (fun a ha _ => mul_nonneg (sq_nonneg (m a)) (hw0 a ha))

namespace ExplicitFormulaAux

/-- A single nontrivial zeta zero has analytic multiplicity `O(log |Im rho|)`.
This is extracted from the proved fixed-width local multiplicity estimate. -/
theorem exists_analyticOrderNatAt_riemannZeta_le_log_im_of_nontrivialZero :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ rho : ℂ,
      RiemannHypothesis.IsNontrivialZero rho → 4 ≤ |rho.im| →
        (analyticOrderNatAt riemannZeta rho : ℝ) ≤
          B * (1 + Real.log (|rho.im| + 6)) := by
  rcases exists_localZeroMultiplicity_le_log_bound with ⟨B, hB, hlocal⟩
  refine ⟨B, hB, ?_⟩
  intro rho hrho hheight
  let A : ℝ := |rho.im|
  let S : Finset ℂ :=
    (nontrivialZerosFinset (A + 2)).filter fun z : ℂ =>
      A - 1 / 4 ≤ |z.im| ∧ |z.im| ≤ A + 5 / 4
  have hrhoS : rho ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨mem_nontrivialZerosFinset.mpr ⟨hrho, ?_⟩, ?_, ?_⟩
    · dsimp [A]
      linarith
    · dsimp [A]
      linarith
    · dsimp [A]
      linarith
  have hsingle : (analyticOrderNatAt riemannZeta rho : ℝ) ≤
      ∑ z ∈ S, (analyticOrderNatAt riemannZeta z : ℝ) := by
    exact Finset.single_le_sum
      (fun z _ => Nat.cast_nonneg (analyticOrderNatAt riemannZeta z)) hrhoS
  calc
    (analyticOrderNatAt riemannZeta rho : ℝ) ≤
        ∑ z ∈ S, (analyticOrderNatAt riemannZeta z : ℝ) := hsingle
    _ = localZeroMultiplicity A := by
      rfl
    _ ≤ B * (1 + Real.log (A + 6)) := hlocal A (by simpa [A] using hheight)
    _ = B * (1 + Real.log (|rho.im| + 6)) := by rfl

end ExplicitFormulaAux

/-- Actual zeta zeros in one dyadic height shell and one narrow real-part
strip `sigma < Re rho <= tau`. -/
noncomputable def actualCarlsonDyadicZeroStrip
    (sigma tau : ℝ) (n : ℕ) : Finset ℂ :=
  (actualCarlsonDyadicZeroShell sigma n).filter fun rho => rho.re ≤ tau

theorem actualCarlsonDyadicZeroStrip_subset_shell
    (sigma tau : ℝ) (n : ℕ) :
    actualCarlsonDyadicZeroStrip sigma tau n ⊆
      actualCarlsonDyadicZeroShell sigma n :=
  Finset.filter_subset _ _

/-- Linear analytic-multiplicity capacity of one actual zeta dyadic strip. -/
noncomputable def actualCarlsonDyadicStripLinearMultiplicityCapacity
    (sigma tau : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n,
    (analyticOrderNatAt riemannZeta rho : ℝ)

/-- Linear multiplicity capacity with the direct-L2 reciprocal-square
weight. -/
noncomputable def actualCarlsonDyadicStripLinearReciprocalSquareCapacity
    (sigma tau : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n,
    (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ ^ 2

/-- Square analytic-multiplicity capacity with the direct-L2
`1 / |rho|^2` weight. -/
noncomputable def actualCarlsonDyadicStripSquareReciprocalCapacity
    (sigma tau : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n,
    (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2

/-- The same square capacity after deleting an arbitrary finite exceptional
set. -/
noncomputable def actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
    (sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) : ℝ :=
  ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
    (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2

theorem actualCarlsonDyadicStripLinearMultiplicityCapacity_nonneg
    (sigma tau : ℝ) (n : ℕ) :
    0 ≤ actualCarlsonDyadicStripLinearMultiplicityCapacity sigma tau n := by
  unfold actualCarlsonDyadicStripLinearMultiplicityCapacity
  positivity

theorem actualCarlsonDyadicStripLinearReciprocalSquareCapacity_nonneg
    (sigma tau : ℝ) (n : ℕ) :
    0 ≤ actualCarlsonDyadicStripLinearReciprocalSquareCapacity sigma tau n := by
  unfold actualCarlsonDyadicStripLinearReciprocalSquareCapacity
  positivity

theorem actualCarlsonDyadicStripSquareReciprocalCapacity_nonneg
    (sigma tau : ℝ) (n : ℕ) :
    0 ≤ actualCarlsonDyadicStripSquareReciprocalCapacity sigma tau n := by
  unfold actualCarlsonDyadicStripSquareReciprocalCapacity
  positivity

/-- The linear strip multiplicity is bounded by the cumulative actual Carlson
count at the upper dyadic endpoint. -/
theorem actualCarlsonDyadicStripLinearMultiplicityCapacity_le_count
    (sigma tau : ℝ) (n : ℕ) :
    actualCarlsonDyadicStripLinearMultiplicityCapacity sigma tau n ≤
      actualCarlsonDyadicCount sigma (n + 1) := by
  unfold actualCarlsonDyadicStripLinearMultiplicityCapacity
    actualCarlsonDyadicCount actualCarlsonDyadicZeroStrip
    actualCarlsonDyadicZeroShell ZeroDensity.zeroDensityCount
  exact_mod_cast Finset.sum_le_sum_of_subset_of_nonneg
    ((Finset.filter_subset _ _).trans Finset.sdiff_subset)
    (fun _ _ _ => Nat.zero_le _)

/-- The direct-L2 linear weighted capacity gains the full reciprocal square
of the lower dyadic height. -/
theorem actualCarlsonDyadicStripLinearReciprocalSquareCapacity_le_count_div_sq
    (sigma tau : ℝ) (n : ℕ) :
    actualCarlsonDyadicStripLinearReciprocalSquareCapacity sigma tau n ≤
      actualCarlsonDyadicCount sigma (n + 1) / ((2 : ℝ) ^ n) ^ 2 := by
  have hterm : ∀ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n,
      (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ ^ 2 ≤
        (analyticOrderNatAt riemannZeta rho : ℝ) / ((2 : ℝ) ^ n) ^ 2 := by
    intro rho hrho
    have hshell := actualCarlsonDyadicZeroStrip_subset_shell sigma tau n hrho
    have hlower : (2 : ℝ) ^ n ≤ ‖rho‖ :=
      (actualCarlsonDyadicZeroShell_im_gt hshell).le.trans
        (Complex.im_le_norm rho)
    have hsquare : ((2 : ℝ) ^ n) ^ 2 ≤ ‖rho‖ ^ 2 := by
      nlinarith [norm_nonneg rho, (by positivity : 0 ≤ (2 : ℝ) ^ n)]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
      (by positivity) hsquare
  unfold actualCarlsonDyadicStripLinearReciprocalSquareCapacity
  calc
    (∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n,
        (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ ^ 2) ≤
      ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n,
        (analyticOrderNatAt riemannZeta rho : ℝ) / ((2 : ℝ) ^ n) ^ 2 :=
      Finset.sum_le_sum hterm
    _ = actualCarlsonDyadicStripLinearMultiplicityCapacity sigma tau n /
        ((2 : ℝ) ^ n) ^ 2 := by
      simp [actualCarlsonDyadicStripLinearMultiplicityCapacity,
        Finset.sum_div]
    _ ≤ actualCarlsonDyadicCount sigma (n + 1) / ((2 : ℝ) ^ n) ^ 2 :=
      div_le_div_of_nonneg_right
        (actualCarlsonDyadicStripLinearMultiplicityCapacity_le_count sigma tau n)
        (by positivity)

/-- A logarithmic local maximum multiplicity is valid uniformly throughout
every sufficiently high actual dyadic zeta strip. -/
theorem exists_actualCarlsonDyadicStrip_maxMultiplicity_le_log :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ sigma tau : ℝ, ∀ n : ℕ,
      4 ≤ (2 : ℝ) ^ n → ∀ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n,
        (analyticOrderNatAt riemannZeta rho : ℝ) ≤
          B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) := by
  rcases
      ExplicitFormulaAux.exists_analyticOrderNatAt_riemannZeta_le_log_im_of_nontrivialZero
    with ⟨B, hB, hpoint⟩
  refine ⟨B, hB, ?_⟩
  intro sigma tau n hn rho hrho
  have hshell := actualCarlsonDyadicZeroStrip_subset_shell sigma tau n hrho
  have hdiff := Finset.mem_sdiff.mp hshell
  have hup := ZeroDensity.mem_zeroDensityZerosFinset.mp hdiff.1
  have himpos : 0 < rho.im := hup.2.1
  have himupper : rho.im ≤ (2 : ℝ) ^ (n + 1) := hup.2.2.1
  have habs : |rho.im| = rho.im := abs_of_pos himpos
  have hheight : 4 ≤ |rho.im| := by
    rw [habs]
    exact hn.trans (actualCarlsonDyadicZeroShell_im_gt hshell).le
  have hbase := hpoint rho hup.1 hheight
  have hlog : Real.log (|rho.im| + 6) ≤
      Real.log ((2 : ℝ) ^ (n + 1) + 6) := by
    apply Real.log_le_log
    · positivity
    · rw [habs]
      linarith
  exact hbase.trans (mul_le_mul_of_nonneg_left (by linarith [hlog]) hB)

/-- Recent direct-L2 acceptance theorem: linear Carlson multiplicity capacity
plus the local logarithmic maximum multiplicity controls the reciprocal-square
square-multiplicity capacity of every actual dyadic zeta strip. -/
theorem exists_actualCarlsonDyadicStripSquareReciprocalCapacity_le_count :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ sigma tau : ℝ, ∀ n : ℕ,
      4 ≤ (2 : ℝ) ^ n →
        actualCarlsonDyadicStripSquareReciprocalCapacity sigma tau n ≤
          (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6))) *
            (actualCarlsonDyadicCount sigma (n + 1) / ((2 : ℝ) ^ n) ^ 2) := by
  rcases exists_actualCarlsonDyadicStrip_maxMultiplicity_le_log with
    ⟨B, hB, hmax⟩
  refine ⟨B, hB, ?_⟩
  intro sigma tau n hn
  let M : ℝ := B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6))
  have hlift : actualCarlsonDyadicStripSquareReciprocalCapacity sigma tau n ≤
      M * actualCarlsonDyadicStripLinearReciprocalSquareCapacity sigma tau n := by
    unfold actualCarlsonDyadicStripSquareReciprocalCapacity
      actualCarlsonDyadicStripLinearReciprocalSquareCapacity
    calc
      (∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n,
          (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) ≤
        ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n,
          M * ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro rho hrho
        rw [← mul_div_assoc]
        apply div_le_div_of_nonneg_right _ (sq_nonneg ‖rho‖)
        calc
          (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 =
              (analyticOrderNatAt riemannZeta rho : ℝ) *
                (analyticOrderNatAt riemannZeta rho : ℝ) := by ring
          _ ≤ M * (analyticOrderNatAt riemannZeta rho : ℝ) :=
            mul_le_mul_of_nonneg_right (hmax sigma tau n hn rho hrho)
              (Nat.cast_nonneg _)
      _ = M * ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n,
          (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ ^ 2 := by
        rw [Finset.mul_sum]
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    have hpow : 0 ≤ (2 : ℝ) ^ (n + 1) := by positivity
    have harg : 1 ≤ (2 : ℝ) ^ (n + 1) + 6 := by linarith
    exact mul_nonneg hB (by
      nlinarith [Real.log_nonneg harg])
  exact hlift.trans (mul_le_mul_of_nonneg_left
    (actualCarlsonDyadicStripLinearReciprocalSquareCapacity_le_count_div_sq
      sigma tau n)
    hMnonneg)

/-- Deleting any finite set `S` preserves the same real-zeta square-capacity
bound solely by nonnegative-mass monotonicity. -/
theorem exists_actualCarlsonDyadicStripSquareReciprocalCapacityExcluding_le_count :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ sigma tau : ℝ, ∀ n : ℕ,
      4 ≤ (2 : ℝ) ^ n → ∀ S : Finset ℂ,
        actualCarlsonDyadicStripSquareReciprocalCapacityExcluding sigma tau n S ≤
          (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6))) *
            (actualCarlsonDyadicCount sigma (n + 1) / ((2 : ℝ) ^ n) ^ 2) := by
  rcases exists_actualCarlsonDyadicStripSquareReciprocalCapacity_le_count with
    ⟨B, hB, hfull⟩
  refine ⟨B, hB, ?_⟩
  intro sigma tau n hn S
  calc
    actualCarlsonDyadicStripSquareReciprocalCapacityExcluding sigma tau n S ≤
        actualCarlsonDyadicStripSquareReciprocalCapacity sigma tau n := by
      unfold actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
        actualCarlsonDyadicStripSquareReciprocalCapacity
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun _ _ _ => by positivity)
    _ ≤ _ := hfull sigma tau n hn

/-- Carlson's classical density exponent is at most one throughout the closed
critical strip. -/
theorem pntCarlsonClassicalDensityExponent_le_one
    (sigma : ℝ) :
    pntCarlsonClassicalDensityExponent sigma ≤ 1 := by
  unfold pntCarlsonClassicalDensityExponent
  nlinarith [sq_nonneg (2 * sigma - 1)]

/-- After the direct-L2 reciprocal square, the power exponent is at most
`-1`, hence strictly negative even at the critical-line equality case. -/
theorem pntCarlsonClassicalDensityExponent_sub_two_le_neg_one
    (sigma : ℝ) :
    pntCarlsonClassicalDensityExponent sigma - 2 ≤ -1 := by
  linarith [pntCarlsonClassicalDensityExponent_le_one sigma]

theorem pntCarlsonClassicalDensityExponent_sub_two_lt_zero
    (sigma : ℝ) :
    pntCarlsonClassicalDensityExponent sigma - 2 < 0 := by
  linarith [pntCarlsonClassicalDensityExponent_sub_two_le_neg_one sigma]

theorem pntCarlsonClassicalDensityExponent_half_eq_one :
    pntCarlsonClassicalDensityExponent (1 / 2 : ℝ) = 1 := by
  norm_num [pntCarlsonClassicalDensityExponent]

end PrimeNumberTheorem
