import PrimeNumberTheorem.ZeroDensityLayerBudgetCompleteCubicLogDerivPerron
import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderPerronKernel

open Complex Filter Topology Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- Finite rectangular residue formula for the actual cubic zeta kernel. -/
theorem exists_boundaryRectIntegral_thirdOrderExplicitFormulaIntegrand_eq_residue_sum
    {x a c W : ℝ} (hx : 0 < x) (ha : 0 < a) (hac : a < c)
    (hboundary : ∀ p ∈ ([[a, c]] ×ℂ [[-W, W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈ ([[a, c]] ×ℂ [[-W, W]] : Set ℂ) →
        p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      MathlibAux.boundaryRectIntegral
          (thirdOrderExplicitFormulaIntegrand x) a c (-W) W =
        (2 * Real.pi * I) * ∑ p ∈ poles, residue p := by
  classical
  let K : Set ℂ := [[a, c]] ×ℂ [[-W, W]]
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_uIcc.reProdIm isCompact_uIcc
  rcases exists_finite_explicitFormulaIntegrand_analytic_regularized_remainder
      hx hKcompact with
    ⟨poles, residue, hpoles_mem, hpoles_classify, hpoles_complete,
      hresidue, hoff_eq, hregular⟩
  let P : Finset ℂ := poles.erase 0
  let residue2 : ℂ → ℂ := fun p => residue p / p
  let residue3 : ℂ → ℂ := fun p => residue p / p ^ 2
  let r0 : ℂ := if 0 ∈ poles then residue 0 else 0
  let raw : ℂ → ℂ := fun z =>
    explicitFormulaIntegrand x z -
      ∑ p ∈ poles, (z - p)⁻¹ * residue p
  let g : ℂ → ℂ := toMeromorphicNFOn raw K
  let g3 : ℂ → ℂ := fun z =>
    g z / z ^ 2 + z⁻¹ * r0 / z ^ 2 -
      z⁻¹ * ∑ p ∈ P, residue3 p -
      (z ^ 2)⁻¹ * ∑ p ∈ P, residue2 p
  have hz0_of_mem {z : ℂ} (hzK : z ∈ K) : z ≠ 0 := by
    intro hz
    subst z
    have hzre := hzK.1
    rw [uIcc_of_le hac.le] at hzre
    simp at hzre
    linarith
  have hg3 : DifferentiableOn ℂ g3 K := by
    intro z hzK
    have hz0 := hz0_of_mem hzK
    have hz20 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
    have hg : AnalyticAt ℂ g z := by
      simpa [g, raw] using hregular z hzK
    have hinv : AnalyticAt ℂ (fun w : ℂ => w⁻¹) z := analyticAt_id.inv hz0
    have hinv2 : AnalyticAt ℂ (fun w : ℂ => (w ^ 2)⁻¹) z :=
      (analyticAt_id.pow 2).inv hz20
    have hquot : AnalyticAt ℂ (fun w : ℂ => g w / w ^ 2) z :=
      hg.div (analyticAt_id.pow 2) hz20
    have hzeroTerm : AnalyticAt ℂ (fun w : ℂ => w⁻¹ * r0 / w ^ 2) z :=
      (hinv.mul analyticAt_const).div (analyticAt_id.pow 2) hz20
    have hcorrection1 : AnalyticAt ℂ
        (fun w : ℂ => w⁻¹ * ∑ p ∈ P, residue3 p) z :=
      hinv.mul analyticAt_const
    have hcorrection2 : AnalyticAt ℂ
        (fun w : ℂ => (w ^ 2)⁻¹ * ∑ p ∈ P, residue2 p) z :=
      hinv2.mul analyticAt_const
    exact (((hquot.add hzeroTerm).sub hcorrection1).sub hcorrection2).differentiableWithinAt
  have hP_mem : ∀ p ∈ P,
      a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W := by
    intro p hp
    have hp' := Finset.mem_erase.mp hp
    have hp0 : p ≠ 0 := hp'.1
    have hpK : p ∈ K := (hpoles_mem p hp'.2).resolve_left hp0
    have hpclass := hpoles_classify p hp'.2
    exact hboundary p hpK (hpclass.resolve_left hp0)
  have hP_classify : ∀ p ∈ P, p = 1 ∨ riemannZeta p = 0 := by
    intro p hp
    have hp' := Finset.mem_erase.mp hp
    exact (hpoles_classify p hp'.2).resolve_left hp'.1
  have hP_complete : ∀ p, p ∈ K →
      p = 1 ∨ riemannZeta p = 0 → p ∈ P := by
    intro p hpK hpclass
    exact Finset.mem_erase.mpr
      ⟨hz0_of_mem hpK, hpoles_complete p hpK (Or.inr hpclass)⟩
  have hP_residue : ∀ p ∈ P, residue3 p =
      if p = 1 then (x : ℂ)
      else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3 := by
    intro p hp
    have hp0 : p ≠ 0 := Finset.ne_of_mem_erase hp
    dsimp [residue3]
    rw [hresidue p]
    by_cases hp1 : p = 1
    · subst p
      simp
    · simp only [hp1, if_false, hp0]
      field_simp [hp0]
  have hboundary_eq : ∀ z ∈ K,
      ¬(a < z.re ∧ z.re < c ∧ -W < z.im ∧ z.im < W) →
      thirdOrderExplicitFormulaIntegrand x z =
        g3 z + ∑ p ∈ P, (z - p)⁻¹ * residue3 p := by
    intro z hzK hzboundary
    have hz0 := hz0_of_mem hzK
    have hz_not_P : z ∉ P := by
      intro hzP
      exact hzboundary (hP_mem z hzP)
    have hz_not_poles : z ∉ poles := by
      intro hzpoles
      by_cases hz : z = 0
      · exact hz0 hz
      · exact hz_not_P (Finset.mem_erase.mpr ⟨hz, hzpoles⟩)
    have hg_eq := hoff_eq z hzK hz_not_poles
    change g z = raw z at hg_eq
    have hsum_split :
        (∑ p ∈ poles, (z - p)⁻¹ * residue p) =
          z⁻¹ * r0 + ∑ p ∈ P, (z - p)⁻¹ * residue p := by
      by_cases h0 : 0 ∈ poles
      · rw [show (∑ p ∈ poles, (z - p)⁻¹ * residue p) =
            (∑ p ∈ poles.erase 0, (z - p)⁻¹ * residue p) +
              (z - 0)⁻¹ * residue 0 by
            exact (Finset.sum_erase_add _ _ h0).symm]
        simp [P, r0, h0]
      · simp [P, r0, h0]
    have hterm (p : ℂ) (hp : p ∈ P) :
        ((z - p)⁻¹ * residue p) / z ^ 2 =
          (z - p)⁻¹ * residue3 p - z⁻¹ * residue3 p -
            (z ^ 2)⁻¹ * residue2 p := by
      exact simplePoleTerm_div_sq_eq hz0 (Finset.ne_of_mem_erase hp)
        (fun hzp => hz_not_P (by simpa [hzp] using hp))
    have hsum_div :
        (∑ p ∈ P, (z - p)⁻¹ * residue p) / z ^ 2 =
          (∑ p ∈ P, (z - p)⁻¹ * residue3 p) -
            z⁻¹ * ∑ p ∈ P, residue3 p -
            (z ^ 2)⁻¹ * ∑ p ∈ P, residue2 p := by
      rw [Finset.sum_div]
      calc
        (∑ p ∈ P, ((z - p)⁻¹ * residue p) / z ^ 2) =
            ∑ p ∈ P,
              ((z - p)⁻¹ * residue3 p - z⁻¹ * residue3 p -
                (z ^ 2)⁻¹ * residue2 p) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hterm p hp
        _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
    rw [thirdOrderExplicitFormulaIntegrand_eq_explicitFormulaIntegrand_div_sq]
    dsimp [g3]
    rw [hg_eq]
    dsimp [raw]
    rw [hsum_split]
    rw [show (explicitFormulaIntegrand x z -
          (z⁻¹ * r0 + ∑ p ∈ P, (z - p)⁻¹ * residue p)) / z ^ 2 =
        explicitFormulaIntegrand x z / z ^ 2 - z⁻¹ * r0 / z ^ 2 -
          (∑ p ∈ P, (z - p)⁻¹ * residue p) / z ^ 2 by ring]
    rw [hsum_div]
    ring
  refine ⟨P, residue3, hP_mem, hP_classify, hP_complete, hP_residue, ?_⟩
  calc
    MathlibAux.boundaryRectIntegral
        (thirdOrderExplicitFormulaIntegrand x) a c (-W) W =
      MathlibAux.boundaryRectIntegral
        (fun z => g3 z + ∑ p ∈ P, (z - p)⁻¹ * residue3 p)
          a c (-W) W := by
      apply MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
      simpa [K] using hboundary_eq
    _ = (2 * Real.pi * I) * ∑ p ∈ P, residue3 p :=
      MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
        P residue3 hg3 hP_mem

end ExplicitFormulaResidues
end PrimeNumberTheorem
