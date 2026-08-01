import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderExplicitFormulaResidues

open Complex Filter Topology Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- The normalized bottom, top, and left edges after shifting the cubic Perron
contour from `Re(s)=c` to `Re(s)=a`. -/
noncomputable def thirdOrderContourRemainder
    (x a c W : ℝ) : ℂ :=
  ((∫ σ : ℝ in a..c,
      thirdOrderExplicitFormulaIntegrand x
        ((σ : ℂ) + ((-(2 * Real.pi * W) : ℝ) : ℂ) * I)) -
    (∫ σ : ℝ in a..c,
      thirdOrderExplicitFormulaIntegrand x
        ((σ : ℂ) + (((2 * Real.pi * W) : ℝ) : ℂ) * I)) -
    I * (∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
      thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I))) /
    (2 * Real.pi * I)

theorem exists_scaledRightIntegral_eq_residue_sum_sub_thirdOrderContourRemainder
    {x a c W : ℝ} (hx : 0 < x) (ha : 0 < a) (hac : a < c)
    (hboundary : ∀ p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      (∫ w : ℝ in (-W)..W,
          thirdOrderExplicitFormulaIntegrand x
            ((c : ℂ) + 2 * Real.pi * w * I)) =
        (∑ p ∈ poles, residue p) - thirdOrderContourRemainder x a c W := by
  rcases
      exists_boundaryRectIntegral_thirdOrderExplicitFormulaIntegrand_eq_residue_sum
        hx ha hac hboundary with
    ⟨poles, residue, hpoles, hclass, hcomplete, hresidue, hrect⟩
  refine ⟨poles, residue, hpoles, hclass, hcomplete, hresidue, ?_⟩
  have hright := I_mul_verticalIntegral_eq_two_pi_I_mul_scaledIntegral
    (thirdOrderExplicitFormulaIntegrand x) c W
  unfold MathlibAux.boundaryRectIntegral at hrect
  simp only [smul_eq_mul] at hrect
  rw [hright] at hrect
  have hden : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  let B : ℂ := ∫ σ : ℝ in a..c,
    thirdOrderExplicitFormulaIntegrand x
      ((σ : ℂ) + ((-(2 * Real.pi * W) : ℝ) : ℂ) * I)
  let T : ℂ := ∫ σ : ℝ in a..c,
    thirdOrderExplicitFormulaIntegrand x
      ((σ : ℂ) + (((2 * Real.pi * W) : ℝ) : ℂ) * I)
  let L : ℂ := ∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
    thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)
  let R : ℂ := ∫ w : ℝ in (-W)..W,
    thirdOrderExplicitFormulaIntegrand x
      ((c : ℂ) + 2 * Real.pi * w * I)
  let S : ℂ := ∑ p ∈ poles, residue p
  have hrect'' : (B - T + (2 * Real.pi * I) * R) - I * L =
      (2 * Real.pi * I) * S := by
    simpa [B, T, L, R, S] using hrect
  change R = S - (B - T - I * L) / (2 * Real.pi * I)
  field_simp [hden]
  linear_combination hrect''

/-- Actual finite-height cubic explicit formula for the von Mangoldt second
Riesz mean. -/
theorem exists_norm_residue_sum_sub_thirdOrderContourRemainder_sub_secondRieszPsi_le
    {x a c W : ℝ} (hx : 0 < x) (ha : 0 < a) (hac : a < c)
    (hc : 1 < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      ‖((∑ p ∈ poles, residue p) - thirdOrderContourRemainder x a c W) -
          (secondRieszChebyshevPsi x : ℂ)‖ ≤
        ∑' n : ℕ,
          vonMangoldt n * (x / n) ^ c /
            (8 * Real.pi ^ 3 * W ^ 2) := by
  rcases
      exists_scaledRightIntegral_eq_residue_sum_sub_thirdOrderContourRemainder
        hx ha hac hboundary with
    ⟨poles, residue, hpoles, hclass, hcomplete, hresidue, hshift⟩
  refine ⟨poles, residue, hpoles, hclass, hcomplete, hresidue, ?_⟩
  have hperron :=
    norm_truncated_negLogDeriv_thirdOrder_sub_secondRieszPsi_le hx hc hW
  have hintegral :
      (∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          (-deriv riemannZeta (perronLine c w) /
            riemannZeta (perronLine c w)) /
              (perronLine c w) ^ 3) =
        ∫ w : ℝ in (-W)..W,
          thirdOrderExplicitFormulaIntegrand x
            ((c : ℂ) + 2 * Real.pi * w * I) := by
    apply intervalIntegral.integral_congr
    intro w hw
    dsimp
    rw [thirdOrderExplicitFormulaIntegrand_eq_neg_logDeriv_kernel]
    simp only [perronLine]
  rw [hintegral, hshift] at hperron
  exact hperron

end ExplicitFormulaResidues
end PrimeNumberTheorem
