import PrimeNumberTheorem.ZeroDensityLayerBudgetPositiveZeroConjugation

/-!
# The PNT explicit-formula zero kernel

This module instantiates conjugation recovery for the actual multiplicity-weighted
zero term.  The relative contribution is the natural input for a decaying
Pintz--Carlson kernel bound.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem

/-- The unsigned multiplicity-weighted zero term occurring in the finite PNT
explicit formula. -/
noncomputable def pntExplicitFormulaZeroTerm (x : ℝ) (ρ : ℂ) : ℂ :=
  (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ

/-- The signed zero contribution in the finite PNT explicit formula. -/
noncomputable def pntFiniteZeroContribution (x : ℝ) (ρ : ℂ) : ℂ :=
  -pntExplicitFormulaZeroTerm x ρ

/-- The zero contribution after normalizing the PNT error by `x`. -/
noncomputable def pntRelativeZeroContribution (x : ℝ) (ρ : ℂ) : ℂ :=
  ((x : ℂ)⁻¹) * pntFiniteZeroContribution x ρ

theorem pntExplicitFormulaZeroTerm_conj
    {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hρ : RiemannHypothesis.IsNontrivialZero ρ) :
    pntExplicitFormulaZeroTerm x (conj ρ) =
      conj (pntExplicitFormulaZeroTerm x ρ) := by
  have harg : Complex.arg (x : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact ne_of_lt Real.pi_pos
  have hpow : (x : ℂ) ^ conj ρ = conj ((x : ℂ) ^ ρ) := by
    simpa using Complex.cpow_conj (x : ℂ) ρ harg
  unfold pntExplicitFormulaZeroTerm
  rw [RiemannVonMangoldt.analyticOrderNatAt_riemannZeta_conj_of_nontrivialZero hρ,
    hpow]
  simp

theorem pntFiniteZeroContribution_conj
    {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hρ : RiemannHypothesis.IsNontrivialZero ρ) :
    pntFiniteZeroContribution x (conj ρ) =
      conj (pntFiniteZeroContribution x ρ) := by
  simpa [pntFiniteZeroContribution] using
    congrArg (fun z : ℂ => -z) (pntExplicitFormulaZeroTerm_conj hx hρ)

theorem pntRelativeZeroContribution_conj
    {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hρ : RiemannHypothesis.IsNontrivialZero ρ) :
    pntRelativeZeroContribution x (conj ρ) =
      conj (pntRelativeZeroContribution x ρ) := by
  simp [pntRelativeZeroContribution, pntFiniteZeroContribution_conj hx hρ]

/-- Carlson control of the full signed finite-zero sum, with the real-ordinate
residual kept explicit. -/
theorem PositiveZeroBucketInput.norm_full_pntFiniteZeroContribution_sum_le
    {T x : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n)
    (hx : 0 < x)
    (hkernel : ∀ i, ∀ ρ ∈ input.layer i,
      ‖pntFiniteZeroContribution x ρ‖ ≤
        Real.exp (-Pintz.pintzZeroEnvelope x)) :
    ‖∑ ρ ∈ nontrivialZerosFinset T, pntFiniteZeroContribution x ρ‖ ≤
      2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) input.sigma () x T +
      ‖∑ ρ ∈ realOrdinateNontrivialZerosFinset T,
        pntFiniteZeroContribution x ρ‖ := by
  apply input.norm_full_sum_le_two_mul_pintzCarlsonBudget_add_real
  · intro ρ hρ
    exact pntFiniteZeroContribution_conj hx
      (mem_nontrivialZerosFinset.mp hρ).1
  · exact hkernel

/-- Carlson control of the normalized PNT finite-zero sum.  Discharging
`hkernel` is the remaining analytic kernel estimate, not part of conjugation
recovery. -/
theorem PositiveZeroBucketInput.norm_full_pntRelativeZeroContribution_sum_le
    {T x : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n)
    (hx : 0 < x)
    (hkernel : ∀ i, ∀ ρ ∈ input.layer i,
      ‖pntRelativeZeroContribution x ρ‖ ≤
        Real.exp (-Pintz.pintzZeroEnvelope x)) :
    ‖∑ ρ ∈ nontrivialZerosFinset T, pntRelativeZeroContribution x ρ‖ ≤
      2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) input.sigma () x T +
      ‖∑ ρ ∈ realOrdinateNontrivialZerosFinset T,
        pntRelativeZeroContribution x ρ‖ := by
  apply input.norm_full_sum_le_two_mul_pintzCarlsonBudget_add_real
  · intro ρ hρ
    exact pntRelativeZeroContribution_conj hx
      (mem_nontrivialZerosFinset.mp hρ).1
  · exact hkernel

end PrimeNumberTheorem
