import PrimeNumberTheorem.ExplicitFormulaResidues
import PrimeNumberTheorem.CentralHorizontalEdge
import PrimeNumberTheorem.VKEdgePiOverTwoPolynomialGaussian
import PrimeNumberTheorem.VKEdgePiOverTwoWeightedRectangle

open Complex Set Polynomial
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

open ExplicitFormulaResidues

noncomputable section

/-- The entire polynomial-Gaussian multiplier used when the logarithmic
derivative contour is centered at `w`. -/
def localizedGaussianWeight (A : ℂ[X]) (w : ℂ) (m : ℝ) (z : ℂ) : ℂ :=
  A.eval (z - w) *
    Complex.exp
      ((m : ℂ) * (z - w) ^ 2 +
        ((16 * m : ℝ) : ℂ) * (z - w))

theorem differentiable_localizedGaussianWeight
    (A : ℂ[X]) (w : ℂ) (m : ℝ) :
    Differentiable ℂ (localizedGaussianWeight A w m) := by
  unfold localizedGaussianWeight
  fun_prop

/--
Finite-height weighted contour identity for the concrete zeta logarithmic
derivative.

The assumptions say only that no zeta zero lies on the rectangle boundary.
The finite pole set and its residues are extracted from the already verified
explicit-formula principal-part decomposition.  In particular, zeta zeros
are counted by `analyticOrderNatAt`.
-/
theorem exists_weightedExplicitFormula_boundaryRectIntegral_eq_residue_sum
    (W : ℂ → ℂ) (hW : Differentiable ℂ W)
    {u T : ℝ} (hu : 0 < u) (hT : 0 < T)
    (hboundary :
      ∀ z ∈ ([[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]] : Set ℂ),
        ¬((-1 : ℝ) < z.re ∧ z.re < u + 2 ∧
          -T < z.im ∧ z.im < T) →
        riemannZeta z ≠ 0) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, residue p =
        if p = 1 then (1 : ℂ)
        else if p = 0 then
          -deriv riemannZeta 0 / riemannZeta 0
        else
          -(analyticOrderNatAt riemannZeta p : ℂ) / p) ∧
      MathlibAux.boundaryRectIntegral
          (fun z : ℂ =>
            (z * W z) *
              explicitFormulaIntegrand 1 z)
          (-1) (u + 2) (-T) T =
        (2 * Real.pi * I) *
          ∑ p ∈ poles, (p * W p) * residue p := by
  classical
  let K : Set ℂ :=
    [[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]]
  have hK : IsCompact K := by
    exact isCompact_uIcc.reProdIm isCompact_uIcc
  rcases
      exists_finite_explicitFormulaIntegrand_analytic_regularized_remainder
        (x := (1 : ℝ)) (by norm_num) hK with
    ⟨poles, residue, hpoles_mem, hpoles_classify, hpoles_complete,
      hresidue, hregularized, hanalytic⟩
  let g : ℂ → ℂ :=
    toMeromorphicNFOn
      (fun z : ℂ =>
        explicitFormulaIntegrand 1 z -
          ∑ p ∈ poles, (z - p)⁻¹ * residue p) K
  let H : ℂ → ℂ := fun z => z * W z
  have hH : Differentiable ℂ H := by
    intro z
    exact differentiableAt_id.mul (hW z)
  have hg : DifferentiableOn ℂ g K := by
    exact hanalytic.differentiableOn
  have hpolesInterior :
      ∀ p ∈ poles,
        (-1 : ℝ) < p.re ∧ p.re < u + 2 ∧
          -T < p.im ∧ p.im < T := by
    intro p hp
    rcases hpoles_classify p hp with hp0 | hp1 | hpzero
    · subst p
      simp only [Complex.zero_re, Complex.zero_im]
      constructor
      · norm_num
      constructor
      · linarith
      constructor <;> linarith
    · subst p
      simp only [Complex.one_re, Complex.one_im]
      constructor
      · norm_num
      constructor
      · linarith
      constructor <;> linarith
    · have hpK : p ∈ K := (hpoles_mem p hp).resolve_left (by
        intro hp0
        subst p
        rw [riemannZeta_zero] at hpzero
        norm_num at hpzero)
      have hpnotBoundary :
          (-1 : ℝ) < p.re ∧ p.re < u + 2 ∧
            -T < p.im ∧ p.im < T := by
        by_contra hpnot
        exact hboundary p hpK hpnot hpzero
      exact hpnotBoundary
  have hweighted :=
    MathlibAux.boundaryRectIntegral_mul_analyticWeight_eq_residue_sum
      poles residue hg hH hpolesInterior
  have hboundaryNotPole :
      ∀ z ∈ K,
        ¬((-1 : ℝ) < z.re ∧ z.re < u + 2 ∧
          -T < z.im ∧ z.im < T) →
        z ∉ poles := by
    intro z hzK hzBoundary hzPole
    exact hzBoundary (hpolesInterior z hzPole)
  have hcontour :
      MathlibAux.boundaryRectIntegral
          (fun z : ℂ =>
            H z * explicitFormulaIntegrand 1 z)
          (-1) (u + 2) (-T) T =
        MathlibAux.boundaryRectIntegral
          (fun z : ℂ =>
            H z *
              (g z +
                ∑ p ∈ poles, (z - p)⁻¹ * residue p))
          (-1) (u + 2) (-T) T := by
    apply MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
    intro z hzK hzBoundary
    have hzNotPole := hboundaryNotPole z hzK hzBoundary
    have hreg := hregularized z hzK hzNotPole
    dsimp [g]
    rw [hreg]
    ring
  refine ⟨poles, residue, hpoles_classify, ?_, ?_⟩
  · intro p
    rw [hresidue p]
    simp only [Complex.ofReal_one, Complex.one_cpow, mul_one]
  · change
      MathlibAux.boundaryRectIntegral
          (fun z : ℂ => H z * explicitFormulaIntegrand 1 z)
          (-1) (u + 2) (-T) T =
        (2 * Real.pi * I) *
          ∑ p ∈ poles, H p * residue p
    rw [hcontour]
    exact hweighted

/--
A good height excludes zeta zeros from all four sides of the fixed localized
rectangle.  The left edge `Re(s) = -1` avoids the negative even trivial
zeros, and the right edge lies in the Euler-product half-plane.
-/
theorem riemannZeta_ne_zero_on_localizedContourBoundary_of_goodHeight
    {u T : ℝ} (hu : 0 < u) (hT : 0 < T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    ∀ z ∈ ([[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]] : Set ℂ),
      ¬((-1 : ℝ) < z.re ∧ z.re < u + 2 ∧
        -T < z.im ∧ z.im < T) →
      riemannZeta z ≠ 0 := by
  intro z hzRectangle hzBoundary
  have hxle : (-1 : ℝ) ≤ u + 2 := by linarith
  have hyle : -T ≤ T := by linarith
  rw [mem_reProdIm, uIcc_of_le hxle, uIcc_of_le hyle] at hzRectangle
  by_cases hleft : z.re = -1
  · apply PrimeNumberTheorem.riemannZeta_ne_zero_of_re_le_zero
      (by linarith)
    intro n hn
    have hre := congrArg Complex.re hn
    have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    simp at hre
    linarith
  by_cases hright : z.re = u + 2
  · exact riemannZeta_ne_zero_of_one_le_re (by linarith)
  have hreInterior :
      (-1 : ℝ) < z.re ∧ z.re < u + 2 := by
    constructor
    · exact lt_of_le_of_ne hzRectangle.1.1 (Ne.symm hleft)
    · exact lt_of_le_of_ne hzRectangle.1.2 hright
  have himBoundary : z.im = -T ∨ z.im = T := by
    by_cases hbottom : z.im = -T
    · exact Or.inl hbottom
    by_cases htop : z.im = T
    · exact Or.inr htop
    exfalso
    apply hzBoundary
    exact ⟨hreInterior.1, hreInterior.2,
      lt_of_le_of_ne hzRectangle.2.1 (Ne.symm hbottom),
      lt_of_le_of_ne hzRectangle.2.2 htop⟩
  have habs : |z.im| = T := by
    rcases himBoundary with hbottom | htop
    · rw [hbottom, abs_neg, abs_of_nonneg hT.le]
    · rw [htop, abs_of_nonneg hT.le]
  have hzrepr : (z.re : ℂ) + I * z.im = z := by
    apply Complex.ext <;> simp
  rw [← hzrepr]
  exact
    ExplicitFormulaResidues.riemannZeta_ne_zero_on_goodHeight_horizontal
      hT habs hgood

/--
After subtracting the pole at `s = 1`, the weighted finite rectangle contains
only zeta-zero residues.  The residue at each zero is the negative analytic
multiplicity.
-/
theorem exists_regularizedLogDeriv_boundaryRectIntegral_eq_zero_sum
    (W : ℂ → ℂ) (hW : Differentiable ℂ W)
    {u T : ℝ} (hu : 0 < u) (hT : 0 < T)
    (hboundary :
      ∀ z ∈ ([[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]] : Set ℂ),
        ¬((-1 : ℝ) < z.re ∧ z.re < u + 2 ∧
          -T < z.im ∧ z.im < T) →
        riemannZeta z ≠ 0) :
    ∃ zeros : Finset ℂ,
      (∀ rho ∈ zeros,
        riemannZeta rho = 0 ∧
          (-1 : ℝ) < rho.re ∧ rho.re < u + 2 ∧
          -T < rho.im ∧ rho.im < T) ∧
      (∀ rho ∈
          ([[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]] : Set ℂ),
        riemannZeta rho = 0 → rho ∈ zeros) ∧
      MathlibAux.boundaryRectIntegral
          (fun z : ℂ =>
            W z *
              (-logDeriv riemannZeta z - z / (z - 1)))
          (-1) (u + 2) (-T) T =
        -(2 * Real.pi * I) *
          ∑ rho ∈ zeros,
            (analyticOrderNatAt riemannZeta rho : ℂ) * W rho := by
  classical
  let K : Set ℂ :=
    [[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]]
  have hK : IsCompact K :=
    isCompact_uIcc.reProdIm isCompact_uIcc
  rcases
      exists_finite_explicitFormulaIntegrand_analytic_regularized_remainder
        (x := (1 : ℝ)) (by norm_num) hK with
    ⟨poles, residue, hpoles_mem, hpoles_classify, hpoles_complete,
      hresidue, hregularized, hanalytic⟩
  let g : ℂ → ℂ :=
    toMeromorphicNFOn
      (fun z : ℂ =>
        explicitFormulaIntegrand 1 z -
          ∑ p ∈ poles, (z - p)⁻¹ * residue p) K
  let residueD : ℂ → ℂ := fun p =>
    p * residue p - if p = 1 then 1 else 0
  let G : ℂ → ℂ := fun z =>
    z * g z + ∑ p ∈ poles, residue p - 1
  let zeros : Finset ℂ := poles.filter fun p => riemannZeta p = 0
  have hxle : (-1 : ℝ) ≤ u + 2 := by linarith
  have hyle : -T ≤ T := by linarith
  have honeK : (1 : ℂ) ∈ K := by
    simp only [K, mem_reProdIm, uIcc_of_le hxle, uIcc_of_le hyle,
      mem_Icc, Complex.one_re, Complex.one_im]
    constructor
    · constructor <;> linarith
    · constructor <;> linarith
  have hzeroK : (0 : ℂ) ∈ K := by
    simp only [K, mem_reProdIm, uIcc_of_le hxle, uIcc_of_le hyle,
      mem_Icc, Complex.zero_re, Complex.zero_im]
    constructor
    · constructor <;> linarith
    · constructor <;> linarith
  have honePole : (1 : ℂ) ∈ poles :=
    hpoles_complete 1 honeK (Or.inr (Or.inl rfl))
  have hpolesInterior :
      ∀ p ∈ poles,
        (-1 : ℝ) < p.re ∧ p.re < u + 2 ∧
          -T < p.im ∧ p.im < T := by
    intro p hp
    rcases hpoles_classify p hp with hp0 | hp1 | hpzero
    · subst p
      simp only [Complex.zero_re, Complex.zero_im]
      constructor
      · norm_num
      constructor
      · linarith
      constructor <;> linarith
    · subst p
      simp only [Complex.one_re, Complex.one_im]
      constructor
      · norm_num
      constructor
      · linarith
      constructor <;> linarith
    · have hpK : p ∈ K := (hpoles_mem p hp).resolve_left (by
        intro hp0
        subst p
        rw [riemannZeta_zero] at hpzero
        norm_num at hpzero)
      by_contra hpnot
      exact hboundary p hpK hpnot hpzero
  have hg : DifferentiableOn ℂ g K :=
    hanalytic.differentiableOn
  have hG : DifferentiableOn ℂ G K := by
    intro z hz
    dsimp [G]
    exact
      (((differentiableAt_id.differentiableWithinAt.mul (hg z hz)).add
        (differentiableWithinAt_const
          (∑ p ∈ poles, residue p))).sub
            (differentiableWithinAt_const (1 : ℂ)))
  have hweighted :=
    MathlibAux.boundaryRectIntegral_mul_analyticWeight_eq_residue_sum
      poles residueD hG hW hpolesInterior
  have hboundaryNotPole :
      ∀ z ∈ K,
        ¬((-1 : ℝ) < z.re ∧ z.re < u + 2 ∧
          -T < z.im ∧ z.im < T) →
        z ∉ poles := by
    intro z hzK hzBoundary hzPole
    exact hzBoundary (hpolesInterior z hzPole)
  have hcontour :
      MathlibAux.boundaryRectIntegral
          (fun z : ℂ =>
            W z *
              (-logDeriv riemannZeta z - z / (z - 1)))
          (-1) (u + 2) (-T) T =
        MathlibAux.boundaryRectIntegral
          (fun z : ℂ =>
            W z *
              (G z +
                ∑ p ∈ poles, (z - p)⁻¹ * residueD p))
          (-1) (u + 2) (-T) T := by
    apply MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
    intro z hzK hzBoundary
    have hzNotPole := hboundaryNotPole z hzK hzBoundary
    have hz0 : z ≠ 0 := by
      intro hz
      subst z
      exact hzNotPole (by
        exact hpoles_complete 0 hzeroK (Or.inl rfl))
    have hz1 : z ≠ 1 := by
      intro hz
      subst z
      exact hzNotPole honePole
    have hreg := hregularized z hzK hzNotPole
    have hprincipal :
        ∑ p ∈ poles, z * ((z - p)⁻¹ * residue p) =
          ∑ p ∈ poles,
            (residue p + (z - p)⁻¹ * (p * residue p)) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hzp : z ≠ p := by
        intro h
        subst z
        exact hzNotPole hp
      field_simp [sub_ne_zero.mpr hzp]
      ring
    have hindicator :
        ∑ p ∈ poles,
            (z - p)⁻¹ * (if p = 1 then (1 : ℂ) else 0) =
          (z - 1)⁻¹ := by
      simp [honePole]
    have hresidueDPrincipal :
        ∑ p ∈ poles, (z - p)⁻¹ * residueD p =
          (∑ p ∈ poles, (z - p)⁻¹ * (p * residue p)) -
            (z - 1)⁻¹ := by
      dsimp [residueD]
      calc
        (∑ p ∈ poles,
            (z - p)⁻¹ *
              (p * residue p - if p = 1 then 1 else 0)) =
            ∑ p ∈ poles,
              ((z - p)⁻¹ * (p * residue p) -
                (z - p)⁻¹ *
                  (if p = 1 then (1 : ℂ) else 0)) := by
            apply Finset.sum_congr rfl
            intro p hp
            ring
        _ = (∑ p ∈ poles, (z - p)⁻¹ * (p * residue p)) -
              ∑ p ∈ poles,
                (z - p)⁻¹ *
                  (if p = 1 then (1 : ℂ) else 0) := by
            rw [Finset.sum_sub_distrib]
        _ = (∑ p ∈ poles, (z - p)⁻¹ * (p * residue p)) -
              (z - 1)⁻¹ := by rw [hindicator]
    dsimp [G, g]
    rw [hreg]
    simp only [explicitFormulaIntegrand, Complex.ofReal_one,
      Complex.one_cpow, mul_one]
    rw [hresidueDPrincipal]
    apply congrArg (fun q : ℂ => W z * q)
    rw [mul_sub, Finset.mul_sum, hprincipal,
      Finset.sum_add_distrib]
    field_simp [hz0, sub_ne_zero.mpr hz1]
    ring
  have hzeroMembers :
      ∀ rho ∈ zeros,
        riemannZeta rho = 0 ∧
          (-1 : ℝ) < rho.re ∧ rho.re < u + 2 ∧
          -T < rho.im ∧ rho.im < T := by
    intro rho hrho
    have hrho' := hrho
    simp only [zeros, Finset.mem_filter] at hrho'
    exact ⟨hrho'.2, hpolesInterior rho hrho'.1⟩
  have hzeroComplete :
      ∀ rho ∈ K, riemannZeta rho = 0 → rho ∈ zeros := by
    intro rho hrhoK hrhoZero
    have hrhoPole :=
      hpoles_complete rho hrhoK (Or.inr (Or.inr hrhoZero))
    exact Finset.mem_filter.2 ⟨hrhoPole, hrhoZero⟩
  have hresidueSum :
      ∑ p ∈ poles, W p * residueD p =
        -∑ rho ∈ zeros,
          (analyticOrderNatAt riemannZeta rho : ℂ) * W rho := by
    dsimp [zeros]
    rw [Finset.sum_filter]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rcases hpoles_classify p hp with hp0 | hp1 | hpzero
    · subst p
      simp [residueD, riemannZeta_zero]
    · subst p
      simp only [residueD]
      rw [hresidue (1 : ℂ)]
      simp [riemannZeta_one_ne_zero]
    · have hp0 : p ≠ 0 := by
        intro hp0
        subst p
        rw [riemannZeta_zero] at hpzero
        norm_num at hpzero
      have hp1 : p ≠ 1 := by
        intro hp1
        subst p
        exact riemannZeta_one_ne_zero hpzero
      rw [if_pos hpzero]
      simp only [residueD, hp1, if_false, sub_zero]
      rw [hresidue p]
      simp only [hp1, hp0, if_false, Complex.ofReal_one,
        Complex.one_cpow, mul_one]
      field_simp [hp0]
  refine ⟨zeros, hzeroMembers, hzeroComplete, ?_⟩
  rw [hcontour, hweighted, hresidueSum]
  ring

/-- Good heights provide the boundary nonvanishing input to the exact
regularized zeta contour identity. -/
theorem exists_regularizedLogDeriv_boundaryRectIntegral_eq_zero_sum_of_goodHeight
    (W : ℂ → ℂ) (hW : Differentiable ℂ W)
    {u T : ℝ} (hu : 0 < u) (hT : 0 < T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    ∃ zeros : Finset ℂ,
      (∀ rho ∈ zeros,
        riemannZeta rho = 0 ∧
          (-1 : ℝ) < rho.re ∧ rho.re < u + 2 ∧
          -T < rho.im ∧ rho.im < T) ∧
      (∀ rho ∈
          ([[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]] : Set ℂ),
        riemannZeta rho = 0 → rho ∈ zeros) ∧
      MathlibAux.boundaryRectIntegral
          (fun z : ℂ =>
            W z *
              (-logDeriv riemannZeta z - z / (z - 1)))
          (-1) (u + 2) (-T) T =
        -(2 * Real.pi * I) *
          ∑ rho ∈ zeros,
            (analyticOrderNatAt riemannZeta rho : ℂ) * W rho :=
  exists_regularizedLogDeriv_boundaryRectIntegral_eq_zero_sum
    W hW hu hT
      (riemannZeta_ne_zero_on_localizedContourBoundary_of_goodHeight
        hu hT hgood)

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
