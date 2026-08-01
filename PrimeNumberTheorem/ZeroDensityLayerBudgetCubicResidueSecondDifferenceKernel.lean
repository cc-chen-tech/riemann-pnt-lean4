import PrimeNumberTheorem.ZeroDensityLayerBudgetCommonPoleCubicTripleTransfer

open Complex Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- The contribution of the zeta pole at one after the logarithmic second
forward difference of the cubic residue sum. -/
noncomputable def cubicPoleOneSecondDifference (x h : ℝ) : ℂ :=
  ((x * Real.exp (2 * h) : ℝ) : ℂ) -
    2 * ((x * Real.exp h : ℝ) : ℂ) + (x : ℂ)

/-- The exact cubic residue kernel of one non-one pole after the logarithmic
second forward difference. -/
noncomputable def cubicZeroResidueSecondDifference
    (rho : ℂ) (x h : ℝ) : ℂ :=
  -(analyticOrderNatAt riemannZeta rho : ℂ) *
      (((x * Real.exp (2 * h) : ℝ) : ℂ) ^ rho -
        2 * (((x * Real.exp h : ℝ) : ℂ) ^ rho) + (x : ℂ) ^ rho) /
    rho ^ 3

/-- The bottom/top/left contour remainder after the same second difference. -/
noncomputable def cubicContourSecondDifference
    (x h a c W : ℝ) : ℂ :=
  thirdOrderContourRemainder (x * Real.exp (2 * h)) a c W -
    2 * thirdOrderContourRemainder (x * Real.exp h) a c W +
    thirdOrderContourRemainder x a c W

lemma one_mem_cubicPoleFinset_of_complete
    {P : Finset ℂ} {a c W : ℝ} (haOne : a < 1) (hc : 1 < c) (hW : 0 < W)
    (hcomplete : ∀ p, p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
      p = 1 ∨ riemannZeta p = 0 → p ∈ P) :
    (1 : ℂ) ∈ P := by
  apply hcomplete 1
  · apply mem_cubic_closedRectangle_of_strict (haOne.trans hc)
    change a < 1 ∧ 1 < c ∧
      -(2 * Real.pi * W) < 0 ∧ 0 < 2 * Real.pi * W
    exact ⟨haOne, hc, by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  · exact Or.inl rfl

/-- Pointwise residue formulas on a common pole set give the exact discrete
cubic kernel sum. -/
theorem cubicResidueSum_secondDifference_eq
    {P : Finset ℂ} {r0 r1 r2 : ℂ → ℂ} {x h : ℝ}
    (hone : (1 : ℂ) ∈ P)
    (hr0 : ∀ p ∈ P, r0 p =
      if p = 1 then (x : ℂ)
      else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3)
    (hr1 : ∀ p ∈ P, r1 p =
      if p = 1 then ((x * Real.exp h : ℝ) : ℂ)
      else -(analyticOrderNatAt riemannZeta p : ℂ) *
        ((x * Real.exp h : ℝ) : ℂ) ^ p / p ^ 3)
    (hr2 : ∀ p ∈ P, r2 p =
      if p = 1 then ((x * Real.exp (2 * h) : ℝ) : ℂ)
      else -(analyticOrderNatAt riemannZeta p : ℂ) *
        ((x * Real.exp (2 * h) : ℝ) : ℂ) ^ p / p ^ 3) :
    (∑ p ∈ P, r2 p) - 2 * (∑ p ∈ P, r1 p) + (∑ p ∈ P, r0 p) =
      cubicPoleOneSecondDifference x h +
        ∑ p ∈ P.erase 1, cubicZeroResidueSecondDifference p x h := by
  let f : ℂ → ℂ := fun p => r2 p - 2 * r1 p + r0 p
  have honeTerm : f 1 = cubicPoleOneSecondDifference x h := by
    dsimp [f, cubicPoleOneSecondDifference]
    rw [hr0 1 hone, hr1 1 hone, hr2 1 hone]
    simp
  have herase :
      (∑ p ∈ P.erase 1, f p) =
        ∑ p ∈ P.erase 1, cubicZeroResidueSecondDifference p x h := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpP : p ∈ P := Finset.mem_of_mem_erase hp
    have hp1 : p ≠ 1 := Finset.ne_of_mem_erase hp
    dsimp [f, cubicZeroResidueSecondDifference]
    rw [hr0 p hpP, hr1 p hpP, hr2 p hpP]
    simp only [hp1, if_false]
    ring
  calc
    (∑ p ∈ P, r2 p) - 2 * (∑ p ∈ P, r1 p) + (∑ p ∈ P, r0 p) =
        ∑ p ∈ P, f p := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    _ = (∑ p ∈ P.erase 1, f p) + f 1 :=
      (Finset.sum_erase_add _ _ hone).symm
    _ = _ := by rw [herase, honeTerm, add_comm]

/-- Exact decomposition of the three-point cubic approximant into the pole at
one, the common zero-kernel sum, and the contour second difference. -/
theorem cubicExplicitFormulaApproximant_secondDifference_eq
    {P : Finset ℂ} {r0 r1 r2 : ℂ → ℂ} {x h a c W : ℝ}
    (hone : (1 : ℂ) ∈ P)
    (hr0 : ∀ p ∈ P, r0 p =
      if p = 1 then (x : ℂ)
      else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3)
    (hr1 : ∀ p ∈ P, r1 p =
      if p = 1 then ((x * Real.exp h : ℝ) : ℂ)
      else -(analyticOrderNatAt riemannZeta p : ℂ) *
        ((x * Real.exp h : ℝ) : ℂ) ^ p / p ^ 3)
    (hr2 : ∀ p ∈ P, r2 p =
      if p = 1 then ((x * Real.exp (2 * h) : ℝ) : ℂ)
      else -(analyticOrderNatAt riemannZeta p : ℂ) *
        ((x * Real.exp (2 * h) : ℝ) : ℂ) ^ p / p ^ 3) :
    cubicExplicitFormulaApproximant P r2 (x * Real.exp (2 * h)) a c W -
        2 * cubicExplicitFormulaApproximant P r1 (x * Real.exp h) a c W +
        cubicExplicitFormulaApproximant P r0 x a c W =
      cubicPoleOneSecondDifference x h +
        (∑ p ∈ P.erase 1, cubicZeroResidueSecondDifference p x h) -
        cubicContourSecondDifference x h a c W := by
  have hsum := cubicResidueSum_secondDifference_eq hone hr0 hr1 hr2
  simp only [cubicExplicitFormulaApproximant, cubicContourSecondDifference]
  linear_combination hsum

theorem cubicExplicitFormulaApproximant_realSecondDifference_eq
    {P : Finset ℂ} {r0 r1 r2 : ℂ → ℂ} {x h a c W : ℝ}
    (hone : (1 : ℂ) ∈ P)
    (hr0 : ∀ p ∈ P, r0 p =
      if p = 1 then (x : ℂ)
      else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3)
    (hr1 : ∀ p ∈ P, r1 p =
      if p = 1 then ((x * Real.exp h : ℝ) : ℂ)
      else -(analyticOrderNatAt riemannZeta p : ℂ) *
        ((x * Real.exp h : ℝ) : ℂ) ^ p / p ^ 3)
    (hr2 : ∀ p ∈ P, r2 p =
      if p = 1 then ((x * Real.exp (2 * h) : ℝ) : ℂ)
      else -(analyticOrderNatAt riemannZeta p : ℂ) *
        ((x * Real.exp (2 * h) : ℝ) : ℂ) ^ p / p ^ 3) :
    (cubicExplicitFormulaApproximant P r2 (x * Real.exp (2 * h)) a c W).re -
        2 * (cubicExplicitFormulaApproximant P r1 (x * Real.exp h) a c W).re +
        (cubicExplicitFormulaApproximant P r0 x a c W).re =
      (cubicPoleOneSecondDifference x h +
        (∑ p ∈ P.erase 1, cubicZeroResidueSecondDifference p x h) -
        cubicContourSecondDifference x h a c W).re := by
  have hcomplex := cubicExplicitFormulaApproximant_secondDifference_eq
    (a := a) (c := c) (W := W) hone hr0 hr1 hr2
  simpa using congrArg Complex.re hcomplex

/-- The actual cubic explicit formula, after exact kernel extraction, gives
endpoint Chebyshev bounds involving only one common zero set, the pole-at-one
term, the contour second difference, and the Perron truncation budget. -/
theorem exists_cubicZeroKernelSum_chebyshevPsi_bounds
    {x h a c W : ℝ} (hx : 0 < x) (hh : 0 < h)
    (ha : 0 < a) (haOne : a < 1) (hc : 1 < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ poles : Finset ℂ,
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      chebyshevPsi x ≤
          ((cubicPoleOneSecondDifference x h +
                (∑ p ∈ poles.erase 1, cubicZeroResidueSecondDifference p x h) -
                cubicContourSecondDifference x h a c W).re +
            (cubicPerronTruncationBudget (x * Real.exp (2 * h)) c W +
              2 * cubicPerronTruncationBudget (x * Real.exp h) c W +
              cubicPerronTruncationBudget x c W)) / h ^ 2 ∧
        ((cubicPoleOneSecondDifference x h +
                (∑ p ∈ poles.erase 1, cubicZeroResidueSecondDifference p x h) -
                cubicContourSecondDifference x h a c W).re -
            (cubicPerronTruncationBudget (x * Real.exp (2 * h)) c W +
              2 * cubicPerronTruncationBudget (x * Real.exp h) c W +
              cubicPerronTruncationBudget x c W)) / h ^ 2 ≤
          chebyshevPsi (x * Real.exp (2 * h)) := by
  have hac : a < c := haOne.trans hc
  rcases exists_commonPole_cubicApproximants_chebyshevPsi_bounds
      hx hh ha hac hc hW hboundary with
    ⟨P, r0, r1, r2, hPmem, hPclass, hPcomplete, hr0, hr1, hr2, hpsi⟩
  have hone : (1 : ℂ) ∈ P :=
    one_mem_cubicPoleFinset_of_complete haOne hc hW hPcomplete
  have hkernel := cubicExplicitFormulaApproximant_realSecondDifference_eq
    (a := a) (c := c) (W := W) hone hr0 hr1 hr2
  rw [hkernel] at hpsi
  exact ⟨P, hPmem, hPclass, hPcomplete, hpsi⟩

end ExplicitFormulaResidues
end PrimeNumberTheorem
