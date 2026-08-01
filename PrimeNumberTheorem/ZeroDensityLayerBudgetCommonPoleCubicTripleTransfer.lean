import PrimeNumberTheorem.ZeroDensityLayerBudgetCubicExplicitFormula
import PrimeNumberTheorem.ZeroDensityLayerBudgetCubicExplicitFormulaSecondDifferenceTransfer

open Complex Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- The actual residue sum minus the three non-right contour edges. -/
noncomputable def cubicExplicitFormulaApproximant
    (poles : Finset ℂ) (residue : ℂ → ℂ) (x a c W : ℝ) : ℂ :=
  (∑ p ∈ poles, residue p) - thirdOrderContourRemainder x a c W

/-- The explicit right-line truncation error in the cubic Perron formula. -/
noncomputable def cubicPerronTruncationBudget (x c W : ℝ) : ℝ :=
  ∑' n : ℕ,
    vonMangoldt n * (x / n) ^ c / (8 * Real.pi ^ 3 * W ^ 2)

lemma mem_cubic_closedRectangle_of_strict
    {p : ℂ} {a c W : ℝ} (hac : a < c)
    (hp : a < p.re ∧ p.re < c ∧
      -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    p ∈ ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) := by
  constructor
  · rw [uIcc_of_le hac.le]
    exact ⟨hp.1.le, hp.2.1.le⟩
  · have hvertical : -(2 * Real.pi * W) ≤ 2 * Real.pi * W := by
      exact (hp.2.2.1.trans hp.2.2.2).le
    rw [uIcc_of_le hvertical]
    exact ⟨hp.2.2.1.le, hp.2.2.2.le⟩

/-- Classification plus completeness makes the finite cubic pole set unique;
it is therefore independent of the sample point used in the Perron kernel. -/
theorem cubicPoleFinset_eq_of_complete
    {P Q : Finset ℂ} {a c W : ℝ} (hac : a < c)
    (hPmem : ∀ p ∈ P, a < p.re ∧ p.re < c ∧
      -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W)
    (hPclass : ∀ p ∈ P, p = 1 ∨ riemannZeta p = 0)
    (hPcomplete : ∀ p, p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
      p = 1 ∨ riemannZeta p = 0 → p ∈ P)
    (hQmem : ∀ p ∈ Q, a < p.re ∧ p.re < c ∧
      -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W)
    (hQclass : ∀ p ∈ Q, p = 1 ∨ riemannZeta p = 0)
    (hQcomplete : ∀ p, p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
      p = 1 ∨ riemannZeta p = 0 → p ∈ Q) :
    P = Q := by
  ext p
  constructor
  · intro hp
    exact hQcomplete p
      (mem_cubic_closedRectangle_of_strict hac (hPmem p hp))
      (hPclass p hp)
  · intro hp
    exact hPcomplete p
      (mem_cubic_closedRectangle_of_strict hac (hQmem p hp))
      (hQclass p hp)

/-- Three actual finite-height cubic explicit formulas can be chosen with one
common pole set and then de-smoothed to endpoint bounds for Chebyshev psi. -/
theorem exists_commonPole_cubicApproximants_chebyshevPsi_bounds
    {x h a c W : ℝ} (hx : 0 < x) (hh : 0 < h)
    (ha : 0 < a) (hac : a < c) (hc : 1 < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (poles : Finset ℂ) (residue0 residue1 residue2 : ℂ → ℂ),
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      (∀ p ∈ poles, residue0 p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      (∀ p ∈ poles, residue1 p =
        if p = 1 then ((x * Real.exp h : ℝ) : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) *
          ((x * Real.exp h : ℝ) : ℂ) ^ p / p ^ 3) ∧
      (∀ p ∈ poles, residue2 p =
        if p = 1 then ((x * Real.exp (2 * h) : ℝ) : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) *
          ((x * Real.exp (2 * h) : ℝ) : ℂ) ^ p / p ^ 3) ∧
      chebyshevPsi x ≤
          ((cubicExplicitFormulaApproximant poles residue2
                (x * Real.exp (2 * h)) a c W).re -
              2 * (cubicExplicitFormulaApproximant poles residue1
                (x * Real.exp h) a c W).re +
              (cubicExplicitFormulaApproximant poles residue0 x a c W).re +
            (cubicPerronTruncationBudget (x * Real.exp (2 * h)) c W +
              2 * cubicPerronTruncationBudget (x * Real.exp h) c W +
              cubicPerronTruncationBudget x c W)) / h ^ 2 ∧
        ((cubicExplicitFormulaApproximant poles residue2
                (x * Real.exp (2 * h)) a c W).re -
              2 * (cubicExplicitFormulaApproximant poles residue1
                (x * Real.exp h) a c W).re +
              (cubicExplicitFormulaApproximant poles residue0 x a c W).re -
            (cubicPerronTruncationBudget (x * Real.exp (2 * h)) c W +
              2 * cubicPerronTruncationBudget (x * Real.exp h) c W +
              cubicPerronTruncationBudget x c W)) / h ^ 2 ≤
          chebyshevPsi (x * Real.exp (2 * h)) := by
  have hy : 0 < x * Real.exp h := mul_pos hx (Real.exp_pos h)
  have hz : 0 < x * Real.exp (2 * h) := mul_pos hx (Real.exp_pos (2 * h))
  rcases exists_norm_residue_sum_sub_thirdOrderContourRemainder_sub_secondRieszPsi_le
      hx ha hac hc hW hboundary with
    ⟨P0, r0, hP0mem, hP0class, hP0complete, hr0, happrox0⟩
  rcases exists_norm_residue_sum_sub_thirdOrderContourRemainder_sub_secondRieszPsi_le
      hy ha hac hc hW hboundary with
    ⟨P1, r1, hP1mem, hP1class, hP1complete, hr1, happrox1⟩
  rcases exists_norm_residue_sum_sub_thirdOrderContourRemainder_sub_secondRieszPsi_le
      hz ha hac hc hW hboundary with
    ⟨P2, r2, hP2mem, hP2class, hP2complete, hr2, happrox2⟩
  have hP10 : P1 = P0 := cubicPoleFinset_eq_of_complete hac
    hP1mem hP1class hP1complete hP0mem hP0class hP0complete
  have hP20 : P2 = P0 := cubicPoleFinset_eq_of_complete hac
    hP2mem hP2class hP2complete hP0mem hP0class hP0complete
  subst P1
  subst P2
  change ‖cubicExplicitFormulaApproximant P0 r0 x a c W -
    (secondRieszChebyshevPsi x : ℂ)‖ ≤
      cubicPerronTruncationBudget x c W at happrox0
  change ‖cubicExplicitFormulaApproximant P0 r1 (x * Real.exp h) a c W -
    (secondRieszChebyshevPsi (x * Real.exp h) : ℂ)‖ ≤
      cubicPerronTruncationBudget (x * Real.exp h) c W at happrox1
  change ‖cubicExplicitFormulaApproximant P0 r2 (x * Real.exp (2 * h)) a c W -
    (secondRieszChebyshevPsi (x * Real.exp (2 * h)) : ℂ)‖ ≤
      cubicPerronTruncationBudget (x * Real.exp (2 * h)) c W at happrox2
  refine ⟨P0, r0, r1, r2, hP0mem, hP0class, hP0complete,
    hr0, hr1, hr2, ?_⟩
  exact chebyshevPsi_bounds_of_three_secondRiesz_complex_approximations
    hx hh happrox0 happrox1 happrox2

end ExplicitFormulaResidues
end PrimeNumberTheorem
