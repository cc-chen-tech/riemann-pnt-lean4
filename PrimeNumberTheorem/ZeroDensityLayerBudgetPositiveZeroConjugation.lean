import PrimeNumberTheorem.ZeroDensityLayerBudgetPositiveZeroBucket
import PrimeNumberTheorem.RiemannVonMangoldt.CriticalLinePartition

/-!
# Conjugation recovery from positive-height zero density

The project Carlson count controls positive ordinates. This module reconstructs
the negative-ordinate contribution by conjugation and keeps the real-ordinate
contribution as an explicit residual.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem

noncomputable def nonPositiveNontrivialZerosFinset (T : ℝ) : Finset ℂ :=
  (nontrivialZerosFinset T).filter fun ρ => ¬ 0 < ρ.im

noncomputable def negativeNontrivialZerosFinset (T : ℝ) : Finset ℂ :=
  (nonPositiveNontrivialZerosFinset T).filter fun ρ => ρ.im < 0

/-- The residual not covered by either strict half-plane. Its members have
imaginary part zero. -/
noncomputable def realOrdinateNontrivialZerosFinset (T : ℝ) : Finset ℂ :=
  (nonPositiveNontrivialZerosFinset T).filter fun ρ => ¬ ρ.im < 0

lemma mem_realOrdinateNontrivialZerosFinset {ρ : ℂ} {T : ℝ} :
    ρ ∈ realOrdinateNontrivialZerosFinset T ↔
      ρ ∈ nontrivialZerosFinset T ∧ ρ.im = 0 := by
  simp only [realOrdinateNontrivialZerosFinset,
    nonPositiveNontrivialZerosFinset, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hρ, hnonpos⟩, hnneg⟩
    exact ⟨hρ, le_antisymm (le_of_not_gt hnonpos)
      (not_lt.mp hnneg)⟩
  · rintro ⟨hρ, him⟩
    simp [hρ, him]

/-- Exact positive/negative/real-ordinate partition of the finite zero sum. -/
theorem finiteZeroSum_eq_positive_add_negative_add_real
    (T : ℝ) (term : ℂ → ℂ) :
    ∑ ρ ∈ nontrivialZerosFinset T, term ρ =
      (∑ ρ ∈ positiveNontrivialZerosFinset T, term ρ) +
      (∑ ρ ∈ negativeNontrivialZerosFinset T, term ρ) +
      ∑ ρ ∈ realOrdinateNontrivialZerosFinset T, term ρ := by
  have hsplit₁ :=
    Finset.sum_filter_add_sum_filter_not
      (nontrivialZerosFinset T) (fun ρ : ℂ => 0 < ρ.im) term
  have hsplit₂ :=
    Finset.sum_filter_add_sum_filter_not
      (nonPositiveNontrivialZerosFinset T) (fun ρ : ℂ => ρ.im < 0) term
  calc
    ∑ ρ ∈ nontrivialZerosFinset T, term ρ =
        (∑ ρ ∈ positiveNontrivialZerosFinset T, term ρ) +
          ∑ ρ ∈ nonPositiveNontrivialZerosFinset T, term ρ := hsplit₁.symm
    _ = (∑ ρ ∈ positiveNontrivialZerosFinset T, term ρ) +
          ((∑ ρ ∈ negativeNontrivialZerosFinset T, term ρ) +
            ∑ ρ ∈ realOrdinateNontrivialZerosFinset T, term ρ) := by
          congr 1
          exact hsplit₂.symm
    _ = (∑ ρ ∈ positiveNontrivialZerosFinset T, term ρ) +
          (∑ ρ ∈ negativeNontrivialZerosFinset T, term ρ) +
            ∑ ρ ∈ realOrdinateNontrivialZerosFinset T, term ρ := by
          rw [add_assoc]

/-- Conjugation bijects positive and negative ordinates, so an equivariant term
has conjugate half-plane sums. -/
theorem sum_negative_eq_conj_sum_positive
    (T : ℝ) (term : ℂ → ℂ)
    (hterm : ∀ ρ ∈ nontrivialZerosFinset T,
      term (conj ρ) = conj (term ρ)) :
    (∑ ρ ∈ negativeNontrivialZerosFinset T, term ρ) =
      conj (∑ ρ ∈ positiveNontrivialZerosFinset T, term ρ) := by
  have hsum :
      (∑ ρ ∈ positiveNontrivialZerosFinset T, conj (term ρ)) =
        ∑ ρ ∈ negativeNontrivialZerosFinset T, term ρ := by
    apply Finset.sum_bij (fun ρ _ => conj ρ)
    · intro ρ hρ
      have hp := mem_positiveNontrivialZerosFinset.mp hρ
      have hconjZero :=
        RiemannVonMangoldt.isNontrivialZero_conj hp.1
      have hconjMem : conj ρ ∈ nontrivialZerosFinset T := by
        apply mem_nontrivialZerosFinset.mpr
        refine ⟨hconjZero, ?_⟩
        simpa [abs_of_pos hp.2.1] using hp.2.2
      simp only [negativeNontrivialZerosFinset,
        nonPositiveNontrivialZerosFinset, Finset.mem_filter]
      exact ⟨⟨hconjMem, by simp [hp.2.1.le]⟩, by simp [hp.2.1]⟩
    · intro ρ₁ hρ₁ ρ₂ hρ₂ heq
      have := congrArg conj heq
      simpa using this
    · intro ρ hρ
      have hρneg := (Finset.mem_filter.mp hρ).2
      have hρnonpos := (Finset.mem_filter.mp
        (Finset.mem_filter.mp hρ).1).1
      refine ⟨conj ρ, ?_, ?_⟩
      · apply mem_positiveNontrivialZerosFinset.mpr
        have hzero := (mem_nontrivialZerosFinset.mp hρnonpos).1
        refine ⟨RiemannVonMangoldt.isNontrivialZero_conj hzero,
          by simpa using neg_pos.mpr hρneg, ?_⟩
        have himT := (mem_nontrivialZerosFinset.mp hρnonpos).2
        simpa [abs_of_neg hρneg] using himT
      · simp
    · intro ρ hρ
      have hp := mem_positiveNontrivialZerosFinset.mp hρ
      have hheight : |ρ.im| ≤ T := by
        simpa [abs_of_pos hp.2.1] using hp.2.2
      exact (hterm ρ (mem_nontrivialZerosFinset.mpr ⟨hp.1, hheight⟩)).symm
  rw [← hsum]
  simpa only [map_sum]

/-- Full finite-zero norm bound from a positive-height Carlson budget plus the
explicit real-ordinate residual. -/
theorem PositiveZeroBucketInput.norm_full_sum_le_two_mul_pintzCarlsonBudget_add_real
    {T x : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n)
    (term : ℂ → ℂ)
    (hterm : ∀ ρ ∈ nontrivialZerosFinset T,
      term (conj ρ) = conj (term ρ))
    (hkernel : ∀ i, ∀ ρ ∈ input.layer i,
      ‖term ρ‖ ≤ Real.exp (-Pintz.pintzZeroEnvelope x)) :
    ‖∑ ρ ∈ nontrivialZerosFinset T, term ρ‖ ≤
      2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) input.sigma () x T +
      ‖∑ ρ ∈ realOrdinateNontrivialZerosFinset T, term ρ‖ := by
  let positiveSum := ∑ ρ ∈ positiveNontrivialZerosFinset T, term ρ
  let negativeSum := ∑ ρ ∈ negativeNontrivialZerosFinset T, term ρ
  let realSum := ∑ ρ ∈ realOrdinateNontrivialZerosFinset T, term ρ
  have hdecomp :
      (∑ ρ ∈ nontrivialZerosFinset T, term ρ) =
        positiveSum + negativeSum + realSum :=
    finiteZeroSum_eq_positive_add_negative_add_real T term
  have hnegative : negativeSum = conj positiveSum :=
    sum_negative_eq_conj_sum_positive T term hterm
  have hpositive :=
    input.norm_sum_le_pintzCarlsonDensityBudget term hkernel
  rw [hdecomp]
  calc
    ‖positiveSum + negativeSum + realSum‖ ≤
        ‖positiveSum‖ + ‖negativeSum‖ + ‖realSum‖ := by
          calc
            ‖positiveSum + negativeSum + realSum‖ ≤
                ‖positiveSum + negativeSum‖ + ‖realSum‖ := norm_add_le _ _
            _ ≤ ‖positiveSum‖ + ‖negativeSum‖ + ‖realSum‖ := by
              gcongr
              exact norm_add_le _ _
    _ = 2 * ‖positiveSum‖ + ‖realSum‖ := by
          rw [hnegative, norm_conj]
          ring
    _ ≤ 2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
          (Finset.univ : Finset (Fin n)) input.sigma () x T +
        ‖realSum‖ := by
          gcongr

end PrimeNumberTheorem
