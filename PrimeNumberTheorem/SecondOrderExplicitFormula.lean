import MathlibAux.BoundaryRectResidue
import PrimeNumberTheorem.ExplicitFormulaResidues
import PrimeNumberTheorem.CompletePerron

open Complex Filter Topology Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- The second-order Perron integrand used to recover the first Riesz mean. -/
noncomputable def secondOrderExplicitFormulaIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  explicitFormulaIntegrand x s / s

lemma secondOrderExplicitFormulaIntegrand_eq_neg_logDeriv_kernel
    (x : ℝ) (s : ℂ) :
    secondOrderExplicitFormulaIntegrand x s =
      (x : ℂ) ^ s *
        (-deriv riemannZeta s / riemannZeta s) / s ^ 2 := by
  simp only [secondOrderExplicitFormulaIntegrand, explicitFormulaIntegrand,
    logDeriv_apply]
  ring

lemma simplePoleTerm_div_eq
    {z p r : ℂ} (hz : z ≠ 0) (hp : p ≠ 0) (hzp : z ≠ p) :
    ((z - p)⁻¹ * r) / z =
      (z - p)⁻¹ * (r / p) - z⁻¹ * (r / p) := by
  field_simp [hz, hp, sub_ne_zero.mpr hzp]
  ring

/-- On a rectangle contained in `Re(s) > 0`, the second-order explicit-formula
integrand has a finite simple-pole residue formula.  The poles are exactly
nonzero candidates inherited from zeta's divisor; division by `s` changes
each first-order residue `r p` to `r p / p`. -/
theorem exists_boundaryRectIntegral_secondOrderExplicitFormulaIntegrand_eq_residue_sum
    {x a c W : ℝ} (hx : 0 < x) (ha : 0 < a) (hac : a < c)
    (hboundary : ∀ p ∈ ([[a, c]] ×ℂ [[-W, W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      MathlibAux.boundaryRectIntegral
          (secondOrderExplicitFormulaIntegrand x) a c (-W) W =
        (2 * Real.pi * I) * ∑ p ∈ poles, residue p := by
  classical
  let K : Set ℂ := [[a, c]] ×ℂ [[-W, W]]
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_uIcc.reProdIm isCompact_uIcc
  rcases exists_finite_explicitFormulaIntegrand_analytic_regularized_remainder
      hx hKcompact with
    ⟨poles, residue, hpoles_mem, hpoles_classify, hoff_eq, hregular⟩
  let P : Finset ℂ := poles.erase 0
  let residue2 : ℂ → ℂ := fun p => residue p / p
  let r0 : ℂ := if 0 ∈ poles then residue 0 else 0
  let raw : ℂ → ℂ := fun z =>
    explicitFormulaIntegrand x z -
      ∑ p ∈ poles, (z - p)⁻¹ * residue p
  let g : ℂ → ℂ := toMeromorphicNFOn raw K
  let g2 : ℂ → ℂ := fun z =>
    g z / z + z⁻¹ * r0 / z - z⁻¹ * ∑ p ∈ P, residue2 p
  have hz0_of_mem {z : ℂ} (hzK : z ∈ K) : z ≠ 0 := by
    intro hz
    subst z
    have hzre := hzK.1
    rw [uIcc_of_le hac.le] at hzre
    simp at hzre
    linarith
  have hg2 : DifferentiableOn ℂ g2 K := by
    intro z hzK
    have hz0 := hz0_of_mem hzK
    have hg : AnalyticAt ℂ g z := by
      simpa [g, raw] using hregular z hzK
    have hinv : AnalyticAt ℂ (fun w : ℂ => w⁻¹) z := analyticAt_id.inv hz0
    have hquot : AnalyticAt ℂ (fun w : ℂ => g w / w) z :=
      hg.div analyticAt_id hz0
    have hzeroTerm : AnalyticAt ℂ (fun w : ℂ => w⁻¹ * r0 / w) z :=
      (hinv.mul analyticAt_const).div analyticAt_id hz0
    have hcorrection : AnalyticAt ℂ
        (fun w : ℂ => w⁻¹ * ∑ p ∈ P, residue2 p) z :=
      hinv.mul analyticAt_const
    exact (hquot.add hzeroTerm |>.sub hcorrection).differentiableWithinAt
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
  have hboundary_eq : ∀ z ∈ K,
      ¬(a < z.re ∧ z.re < c ∧ -W < z.im ∧ z.im < W) →
      secondOrderExplicitFormulaIntegrand x z =
        g2 z + ∑ p ∈ P, (z - p)⁻¹ * residue2 p := by
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
        ((z - p)⁻¹ * residue p) / z =
          (z - p)⁻¹ * residue2 p - z⁻¹ * residue2 p := by
      exact simplePoleTerm_div_eq hz0 (Finset.ne_of_mem_erase hp)
        (fun hzp => hz_not_P (by simpa [hzp] using hp))
    have hsum_div :
        (∑ p ∈ P, (z - p)⁻¹ * residue p) / z =
          (∑ p ∈ P, (z - p)⁻¹ * residue2 p) -
            z⁻¹ * ∑ p ∈ P, residue2 p := by
      rw [Finset.sum_div]
      calc
        (∑ p ∈ P, ((z - p)⁻¹ * residue p) / z) =
            ∑ p ∈ P,
              ((z - p)⁻¹ * residue2 p - z⁻¹ * residue2 p) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hterm p hp
        _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    dsimp [secondOrderExplicitFormulaIntegrand, g2]
    rw [hg_eq]
    dsimp [raw]
    rw [hsum_split]
    rw [show (explicitFormulaIntegrand x z -
          (z⁻¹ * r0 + ∑ p ∈ P, (z - p)⁻¹ * residue p)) / z =
        explicitFormulaIntegrand x z / z - z⁻¹ * r0 / z -
          (∑ p ∈ P, (z - p)⁻¹ * residue p) / z by ring]
    rw [hsum_div]
    ring
  refine ⟨P, residue2, hP_mem, hP_classify, ?_⟩
  calc
    MathlibAux.boundaryRectIntegral
        (secondOrderExplicitFormulaIntegrand x) a c (-W) W =
      MathlibAux.boundaryRectIntegral
        (fun z => g2 z + ∑ p ∈ P, (z - p)⁻¹ * residue2 p)
          a c (-W) W := by
      apply MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
      simpa [K] using hboundary_eq
    _ = (2 * Real.pi * I) * ∑ p ∈ P, residue2 p :=
      MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
        P residue2 hg2 hP_mem

lemma I_mul_verticalIntegral_eq_two_pi_I_mul_scaledIntegral
    (f : ℂ → ℂ) (c W : ℝ) :
    I * (∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
        f ((c : ℂ) + t * I)) =
      (2 * Real.pi * I) *
        (∫ w : ℝ in (-W)..W,
          f ((c : ℂ) + 2 * Real.pi * w * I)) := by
  let F : ℝ → ℂ := fun t => f ((c : ℂ) + t * I)
  have h := intervalIntegral.smul_integral_comp_mul_left
    (f := F) (a := -W) (b := W) (2 * Real.pi)
  change ((2 * Real.pi : ℝ) : ℂ) *
      (∫ w : ℝ in (-W)..W, F (2 * Real.pi * w)) =
    ∫ t : ℝ in (2 * Real.pi * (-W))..(2 * Real.pi * W), F t at h
  change I * (∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W), F t) = _
  rw [show -(2 * Real.pi * W) = 2 * Real.pi * (-W) by ring]
  rw [← h]
  have hfun : (fun w : ℝ => F (2 * Real.pi * w)) =
      fun w : ℝ => f ((c : ℂ) + 2 * Real.pi * w * I) := by
    funext w
    dsimp [F]
    congr 1
    push_cast
    ring
  rw [hfun]
  push_cast
  ring

/-- The normalized contribution of the bottom, top, and left edges when the
second-order Perron contour is shifted from `Re(s)=c` to `Re(s)=a`. -/
noncomputable def secondOrderContourRemainder
    (x a c W : ℝ) : ℂ :=
  ((∫ σ : ℝ in a..c,
      secondOrderExplicitFormulaIntegrand x
        ((σ : ℂ) + ((-(2 * Real.pi * W) : ℝ) : ℂ) * I)) -
    (∫ σ : ℝ in a..c,
      secondOrderExplicitFormulaIntegrand x
        ((σ : ℂ) + (((2 * Real.pi * W) : ℝ) : ℂ) * I)) -
    I * (∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
      secondOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I))) /
    (2 * Real.pi * I)

/-- Exact finite-height contour shift for the second-order Perron integral.
The right-line integral equals the finite residue sum minus the other three
normalized rectangle edges. -/
theorem exists_scaledRightIntegral_eq_residue_sum_sub_secondOrderContourRemainder
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
      (∫ w : ℝ in (-W)..W,
          secondOrderExplicitFormulaIntegrand x
            ((c : ℂ) + 2 * Real.pi * w * I)) =
        (∑ p ∈ poles, residue p) - secondOrderContourRemainder x a c W := by
  rcases
      exists_boundaryRectIntegral_secondOrderExplicitFormulaIntegrand_eq_residue_sum
        hx ha hac hboundary with
    ⟨poles, residue, hpoles, hclass, hrect⟩
  refine ⟨poles, residue, hpoles, hclass, ?_⟩
  have hright := I_mul_verticalIntegral_eq_two_pi_I_mul_scaledIntegral
    (secondOrderExplicitFormulaIntegrand x) c W
  unfold MathlibAux.boundaryRectIntegral at hrect
  simp only [smul_eq_mul] at hrect
  rw [hright] at hrect
  have hden : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  let B : ℂ := ∫ σ : ℝ in a..c,
    secondOrderExplicitFormulaIntegrand x
      ((σ : ℂ) + ((-(2 * Real.pi * W) : ℝ) : ℂ) * I)
  let T : ℂ := ∫ σ : ℝ in a..c,
    secondOrderExplicitFormulaIntegrand x
      ((σ : ℂ) + (((2 * Real.pi * W) : ℝ) : ℂ) * I)
  let L : ℂ := ∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
    secondOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)
  let R : ℂ := ∫ w : ℝ in (-W)..W,
    secondOrderExplicitFormulaIntegrand x
      ((c : ℂ) + 2 * Real.pi * w * I)
  let S : ℂ := ∑ p ∈ poles, residue p
  have hrect'' : (B - T + (2 * Real.pi * I) * R) - I * L =
      (2 * Real.pi * I) * S := by
    simpa [B, T, L, R, S] using hrect
  change R = S - (B - T - I * L) / (2 * Real.pi * I)
  field_simp [hden]
  linear_combination hrect''

/-- A genuine truncated explicit formula for the von Mangoldt first Riesz
mean: the finite residue sum minus the three shifted contour edges differs
from `smoothedChebyshevPsi` by the explicit full-Dirichlet-series Perron
truncation error. -/
theorem exists_norm_residue_sum_sub_contourRemainder_sub_smoothedPsi_le
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
      ‖((∑ p ∈ poles, residue p) - secondOrderContourRemainder x a c W) -
          (smoothedChebyshevPsi x : ℂ)‖ ≤
        ∑' n : ℕ,
          vonMangoldt n * (x / n) ^ c / (2 * Real.pi ^ 2 * W) := by
  rcases
      exists_scaledRightIntegral_eq_residue_sum_sub_secondOrderContourRemainder
        hx ha hac hboundary with
    ⟨poles, residue, hpoles, hclass, hshift⟩
  refine ⟨poles, residue, hpoles, hclass, ?_⟩
  have hperron :=
    norm_truncated_neg_logDeriv_riemannZeta_sub_smoothedPsi_le hx hc hW
  have hintegral :
      (∫ w : ℝ in (-W)..W,
        (x : ℂ) ^ perronLine c w *
          (-deriv riemannZeta (perronLine c w) /
            riemannZeta (perronLine c w)) /
              (perronLine c w) ^ 2) =
        ∫ w : ℝ in (-W)..W,
          secondOrderExplicitFormulaIntegrand x
            ((c : ℂ) + 2 * Real.pi * w * I) := by
    apply intervalIntegral.integral_congr
    intro w hw
    dsimp
    rw [secondOrderExplicitFormulaIntegrand_eq_neg_logDeriv_kernel]
    simp only [perronLine]
  rw [hintegral, hshift] at hperron
  exact hperron

end ExplicitFormulaResidues
end PrimeNumberTheorem
