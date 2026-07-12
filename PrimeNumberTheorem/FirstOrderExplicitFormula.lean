import MathlibAux.BoundaryRectResidue
import PrimeNumberTheorem.ExplicitFormulaResidues
import PrimeNumberTheorem.ExplicitFormulaAux
import PrimeNumberTheorem.FirstOrderLSeriesPerron
import PrimeNumberTheorem.SecondOrderExplicitFormula

open Complex Filter Topology Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open ExplicitFormulaAux

/-- Every member of the finite trivial-zero truncation is a simple zeta
zero. -/
theorem analyticOrderNatAt_riemannZeta_eq_one_of_mem_finiteTrivialZeroSum
    {ρ : ℂ} {T : ℝ} (hρ : ρ ∈ finiteTrivialZeroSum T) :
    analyticOrderNatAt riemannZeta ρ = 1 := by
  rcases mem_finiteTrivialZeroSum_iff.mp hρ with ⟨n, _hn, hnρ⟩
  rw [← hnρ]
  simpa only [Nat.cast_add, Nat.cast_one] using
    analyticOrderNatAt_riemannZeta_neg_even n

/-- On the finite trivial-zero truncation, the multiplicity-aware contour
residue sum is exactly the simple-residue sum. -/
theorem sum_finiteTrivialZeroSum_multiplicity_residues_eq
    {x T : ℝ} :
    (∑ ρ ∈ finiteTrivialZeroSum T,
        -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) =
      ∑ ρ ∈ finiteTrivialZeroSum T, -((x : ℂ) ^ ρ) / ρ := by
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [analyticOrderNatAt_riemannZeta_eq_one_of_mem_finiteTrivialZeroSum hρ]
  norm_num

/-- The multiplicity-aware trivial-zero truncations dictated by the contour
residue formula converge to the classical logarithmic correction. -/
theorem tendsto_finiteTrivialZeroSum_multiplicity_residues
    {x : ℝ} (hx : 1 < x) :
    Tendsto
      (fun N : ℕ => ∑ ρ ∈ finiteTrivialZeroSum (2 * (N : ℝ)),
        -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ)
      atTop
      (nhds (((-(1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))) := by
  convert ExplicitFormulaAux.tendsto_finiteTrivialZeroSum_residues hx using 1
  funext N
  exact sum_finiteTrivialZeroSum_multiplicity_residues_eq

/-- On an ordered rectangle containing `0` in its interior, the first-order
explicit-formula integrand satisfies the finite residue formula.  The right
edge can be fixed independently of the height, as required by Perron
inversion. -/
theorem exists_boundaryRectIntegral_explicitFormulaIntegrand_eq_residue_sum
    {x a c W : ℝ} (hx : 0 < x) (ha : a < 0) (hc : 0 < c)
    (hW : 0 < W)
    (hboundary : ∀ p ∈ ([[a, c]] ×ℂ [[-W, W]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈ ([[a, c]] ×ℂ [[-W, W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else if p = 0 then -deriv riemannZeta 0 / riemannZeta 0
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p) ∧
      MathlibAux.boundaryRectIntegral
          (explicitFormulaIntegrand x) a c (-W) W =
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
  let raw : ℂ → ℂ := fun z =>
    explicitFormulaIntegrand x z -
      ∑ p ∈ poles, (z - p)⁻¹ * residue p
  let g : ℂ → ℂ := toMeromorphicNFOn raw K
  have hregular' : AnalyticOnNhd ℂ g K := by
    simpa [g, raw] using hregular
  have hpoles : ∀ p ∈ poles,
      a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W := by
    intro p hp
    rcases hpoles_mem p hp with hp0 | hpK
    · subst p
      simpa using And.intro ha (And.intro hc
        (And.intro (neg_lt_zero.mpr hW) hW))
    · exact hboundary p hpK (hpoles_classify p hp)
  have hboundary_eq : ∀ z ∈ K,
      ¬(a < z.re ∧ z.re < c ∧ -W < z.im ∧ z.im < W) →
        explicitFormulaIntegrand x z =
          g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p := by
    intro z hzK hzboundary
    have hz_not_pole : z ∉ poles := by
      intro hzpoles
      exact hzboundary (hpoles z hzpoles)
    have hg_eq := hoff_eq z hzK hz_not_pole
    change g z = raw z at hg_eq
    rw [hg_eq]
    simp only [raw]
    ring
  refine ⟨poles, residue, hpoles, hpoles_classify, hpoles_complete,
    (fun p _hp => hresidue p), ?_⟩
  calc
    MathlibAux.boundaryRectIntegral (explicitFormulaIntegrand x) a c (-W) W =
        MathlibAux.boundaryRectIntegral
          (fun z : ℂ => g z +
            ∑ p ∈ poles, (z - p)⁻¹ * residue p) a c (-W) W := by
      apply MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
      simpa [K] using hboundary_eq
    _ = (2 * Real.pi * I) * ∑ p ∈ poles, residue p :=
      MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
        poles residue hregular'.differentiableOn hpoles

/-- The normalized contribution of the bottom, top, and left edges when the
ordinary Perron contour is shifted from `Re(s)=c` to `Re(s)=a`. -/
noncomputable def firstOrderContourRemainder
    (x a c W : ℝ) : ℂ :=
  ((∫ σ : ℝ in a..c,
      explicitFormulaIntegrand x
        ((σ : ℂ) + ((-(2 * Real.pi * W) : ℝ) : ℂ) * I)) -
    (∫ σ : ℝ in a..c,
      explicitFormulaIntegrand x
        ((σ : ℂ) + (((2 * Real.pi * W) : ℝ) : ℂ) * I)) -
    I * (∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
      explicitFormulaIntegrand x ((a : ℂ) + t * I))) /
    (2 * Real.pi * I)

/-- The fixed right edge in the first-order contour shift is exactly the
ordinary Perron integral, hence converges to `psi0`. -/
theorem tendsto_scaledRightIntegral_explicitFormulaIntegrand_atTop
    {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    Tendsto
      (fun W : ℝ => ∫ w : ℝ in (-W)..W,
        explicitFormulaIntegrand x
          ((c : ℂ) + 2 * Real.pi * w * I))
      atTop (nhds (chebyshevPsi0 x : ℂ)) := by
  have h := tendsto_truncated_neg_logDeriv_firstOrderPerron_atTop hx hc
  convert h using 1
  funext W
  apply intervalIntegral.integral_congr
  intro w _hw
  simp only [explicitFormulaIntegrand, perronLine, logDeriv_apply]
  ring

/-- Exact finite-height first-order contour shift.  The normalized right-line
Perron integral equals the finite residue sum minus the other three normalized
rectangle edges. -/
theorem exists_scaledRightIntegral_eq_residue_sum_sub_firstOrderContourRemainder
    {x a c W : ℝ} (hx : 0 < x) (ha : a < 0) (hc : 0 < c)
    (hW : 0 < W)
    (hboundary : ∀ p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else if p = 0 then -deriv riemannZeta 0 / riemannZeta 0
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p) ∧
      (∫ w : ℝ in (-W)..W,
          explicitFormulaIntegrand x
            ((c : ℂ) + 2 * Real.pi * w * I)) =
        (∑ p ∈ poles, residue p) -
          firstOrderContourRemainder x a c W := by
  have hheight : 0 < 2 * Real.pi * W := by positivity
  rcases exists_boundaryRectIntegral_explicitFormulaIntegrand_eq_residue_sum
      hx ha hc hheight hboundary with
    ⟨poles, residue, hpoles, hclass, hcomplete, hresidue, hrect⟩
  refine ⟨poles, residue, hpoles, hclass, hcomplete, hresidue, ?_⟩
  have hright := I_mul_verticalIntegral_eq_two_pi_I_mul_scaledIntegral
    (explicitFormulaIntegrand x) c W
  unfold MathlibAux.boundaryRectIntegral at hrect
  simp only [smul_eq_mul] at hrect
  rw [hright] at hrect
  have hden : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  let B : ℂ := ∫ σ : ℝ in a..c,
    explicitFormulaIntegrand x
      ((σ : ℂ) + ((-(2 * Real.pi * W) : ℝ) : ℂ) * I)
  let T : ℂ := ∫ σ : ℝ in a..c,
    explicitFormulaIntegrand x
      ((σ : ℂ) + (((2 * Real.pi * W) : ℝ) : ℂ) * I)
  let L : ℂ := ∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
    explicitFormulaIntegrand x ((a : ℂ) + t * I)
  let R : ℂ := ∫ w : ℝ in (-W)..W,
    explicitFormulaIntegrand x
      ((c : ℂ) + 2 * Real.pi * w * I)
  let S : ℂ := ∑ p ∈ poles, residue p
  have hrect' : (B - T + (2 * Real.pi * I) * R) - I * L =
      (2 * Real.pi * I) * S := by
    simpa [B, T, L, R, S] using hrect
  change R = S - (B - T - I * L) / (2 * Real.pi * I)
  field_simp [hden]
  linear_combination hrect'

/-- A good height gives an unconditional fixed first-order rectangle with
left edge `Re(s)=-1` and arbitrary fixed right edge `Re(s)=c>1`.  The left
edge contains no trivial zero, the right edge is zero-free, and `goodHeight`
excludes nontrivial zeros from the horizontal edges. -/
theorem
    exists_scaledRightIntegral_eq_residue_sum_sub_firstOrderContourRemainder_of_goodHeight
    {x c W : ℝ} (hx : 0 < x) (hc : 1 < c) (hW : 0 < W)
    (hgood : ExplicitFormulaAux.goodHeight (2 * Real.pi * W)) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        -1 < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[-1, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else if p = 0 then -deriv riemannZeta 0 / riemannZeta 0
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p) ∧
      (∫ w : ℝ in (-W)..W,
          explicitFormulaIntegrand x
            ((c : ℂ) + 2 * Real.pi * w * I)) =
        (∑ p ∈ poles, residue p) -
          firstOrderContourRemainder x (-1) c W := by
  have hH : 0 < 2 * Real.pi * W := by positivity
  apply exists_scaledRightIntegral_eq_residue_sum_sub_firstOrderContourRemainder
    hx (by norm_num) (one_pos.trans hc) hW
  intro p hp hclass
  rcases hclass with rfl | rfl | hpzero
  · simpa using And.intro (by norm_num : (-1 : ℝ) < 0)
      (And.intro (one_pos.trans hc)
        (And.intro (neg_lt_zero.mpr hH) hH))
  · simpa using And.intro (by norm_num : (-1 : ℝ) < 1)
      (And.intro hc (And.intro (neg_lt_zero.mpr hH) hH))
  · have hp' := hp
    simp only [Complex.mem_reProdIm] at hp'
    have hre_bounds := hp'.1
    rw [Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤ c)] at hre_bounds
    have him_bounds := hp'.2
    rw [Set.uIcc_of_le (by linarith : -(2 * Real.pi * W) ≤ 2 * Real.pi * W)]
      at him_bounds
    have htrivial : ∀ n : ℕ, p ≠ -2 * ((n : ℂ) + 1) := by
      intro n hn
      have hre := congrArg Complex.re hn
      simp at hre
      have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith [hre_bounds.1]
    have hre_pos : 0 < p.re := by
      by_contra hnot
      exact (riemannZeta_ne_zero_of_re_le_zero (le_of_not_gt hnot) htrivial)
        hpzero
    have hre_lt_one : p.re < 1 := by
      by_contra hnot
      exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hnot)) hpzero
    have habs_le : |p.im| ≤ 2 * Real.pi * W := abs_le.mpr him_bounds
    have habs_ne : |p.im| ≠ 2 * Real.pi * W :=
      hgood p ⟨hpzero, hre_pos, hre_lt_one⟩
    have him_strict := abs_lt.mp (lt_of_le_of_ne habs_le habs_ne)
    exact ⟨by linarith, by linarith, him_strict.1, him_strict.2⟩

end ExplicitFormulaResidues
end PrimeNumberTheorem
