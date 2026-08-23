import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderPerronKernel
import PrimeNumberTheorem.SecondOrderExplicitFormula

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace PrimeNumberTheorem.ExplicitFormulaResidues

/-- Dividing a finite simple-pole regularization by the identity preserves
analyticity away from zero and divides every residue by its pole location. -/
theorem exists_analyticOnNhd_div_id_regularization
    {K : Set ℂ} {f g : ℂ → ℂ} (poles : Finset ℂ) (residue : ℂ → ℂ)
    (hzero : ∀ z ∈ K, z ≠ 0)
    (hpolesZero : ∀ p ∈ poles, p ≠ 0)
    (hg : AnalyticOnNhd ℂ g K)
    (heq : ∀ z ∈ K, z ∉ poles →
      f z = g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p) :
    ∃ g' : ℂ → ℂ,
      AnalyticOnNhd ℂ g' K ∧
      ∀ z ∈ K, z ∉ poles →
        f z / z = g' z +
          ∑ p ∈ poles, (z - p)⁻¹ * (residue p / p) := by
  let total : ℂ := ∑ p ∈ poles, residue p / p
  let g' : ℂ → ℂ := fun z => g z / z - z⁻¹ * total
  refine ⟨g', ?_, ?_⟩
  · have hid : AnalyticOnNhd ℂ (fun z : ℂ => z) K := analyticOnNhd_id
    have hinv : AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) K := hid.inv hzero
    exact (hg.div hid hzero).sub (hinv.mul analyticOnNhd_const)
  · intro z hzK hzPoles
    have hz0 := hzero z hzK
    have hsum :
        (∑ p ∈ poles, ((z - p)⁻¹ * residue p) / z) =
          (∑ p ∈ poles, (z - p)⁻¹ * (residue p / p)) - z⁻¹ * total := by
      dsimp [total]
      rw [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      have hzp : z ≠ p := by
        intro h
        apply hzPoles
        simpa [h] using hp
      rw [simplePoleTerm_div_eq hz0 (hpolesZero p hp) hzp]
    rw [heq z hzK hzPoles, add_div, Finset.sum_div, hsum]
    dsimp [g']
    ring

noncomputable def thirdOrderExplicitFormulaIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  explicitFormulaIntegrand x s / s ^ 2

theorem thirdOrderExplicitFormulaIntegrand_eq_secondOrder_div
    (x : ℝ) (s : ℂ) :
    thirdOrderExplicitFormulaIntegrand x s =
      secondOrderExplicitFormulaIntegrand x s / s := by
  unfold thirdOrderExplicitFormulaIntegrand secondOrderExplicitFormulaIntegrand
  ring

/-- Remove the artificial pole at zero from the first-order regularization
when the compact set is separated from zero. -/
theorem exists_explicitFormula_regularization_without_zero
    {x : ℝ} (hx : 0 < x) {K : Set ℂ} (hK : IsCompact K)
    (hzero : ∀ z ∈ K, z ≠ 0) :
    ∃ (poles : Finset ℂ) (residue g : ℂ → ℂ),
      (∀ p ∈ poles, p ∈ K ∧ p ≠ 0) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p) ∧
      AnalyticOnNhd ℂ g K ∧
      ∀ z ∈ K, z ∉ poles →
        explicitFormulaIntegrand x z =
          g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p := by
  obtain ⟨poles0, residue0, hpolesK, hpolesType, hpolesComplete,
      hresidue, hraw, hanalytic⟩ :=
    exists_finite_explicitFormulaIntegrand_analytic_regularized_remainder hx hK
  let poles := poles0.erase 0
  let baseR : ℂ → ℂ :=
    toMeromorphicNFOn
      (fun z => explicitFormulaIntegrand x z -
        ∑ p ∈ poles0, (z - p)⁻¹ * residue0 p) K
  let g : ℂ → ℂ := fun z =>
    baseR z + if 0 ∈ poles0 then z⁻¹ * residue0 0 else 0
  refine ⟨poles, residue0, g, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hp0 : p ≠ 0 := Finset.ne_of_mem_erase hp
    have hpMem : p ∈ poles0 := (Finset.mem_erase.mp hp).2
    exact ⟨(hpolesK p hpMem).resolve_left hp0, hp0⟩
  · intro p hp
    have hp0 : p ≠ 0 := Finset.ne_of_mem_erase hp
    have hpMem : p ∈ poles0 := (Finset.mem_erase.mp hp).2
    exact (hpolesType p hpMem).resolve_left hp0
  · intro p hp
    have hp0 : p ≠ 0 := Finset.ne_of_mem_erase hp
    have hpMem : p ∈ poles0 := (Finset.mem_erase.mp hp).2
    rw [hresidue p]
    simp [hp0]
  · have hinv : AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) K :=
      analyticOnNhd_id.inv hzero
    by_cases h0 : 0 ∈ poles0
    · simpa [g, h0, baseR] using!
        hanalytic.add (hinv.mul analyticOnNhd_const)
    · simpa [g, h0, baseR] using hanalytic
  · intro z hzK hzPoles
    have hz0 := hzero z hzK
    have hzNotPoles0 : z ∉ poles0 := by
      intro hzMem
      by_cases hz : z = 0
      · exact hz0 hz
      · exact hzPoles (Finset.mem_erase.mpr ⟨hz, hzMem⟩)
    have hbase := hraw z hzK hzNotPoles0
    by_cases h0 : 0 ∈ poles0
    · have hsum := Finset.sum_erase_add poles0
        (fun p => (z - p)⁻¹ * residue0 p) h0
      dsimp [g, baseR, poles]
      rw [if_pos h0, hbase]
      have hterm : (z - 0)⁻¹ * residue0 0 = z⁻¹ * residue0 0 := by simp
      rw [← hterm, ← hsum]
      ring
    · dsimp [g, baseR, poles]
      rw [if_neg h0, hbase, Finset.erase_eq_of_notMem h0]
      ring

theorem exists_thirdOrderExplicitFormula_analytic_regularized_remainder
    {x : ℝ} (hx : 0 < x) {K : Set ℂ} (hK : IsCompact K)
    (hzero : ∀ z ∈ K, z ≠ 0) :
    ∃ (poles : Finset ℂ) (residue g : ℂ → ℂ),
      (∀ p ∈ poles, p ∈ K ∧ p ≠ 0) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      AnalyticOnNhd ℂ g K ∧
      ∀ z ∈ K, z ∉ poles →
        thirdOrderExplicitFormulaIntegrand x z =
          g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p := by
  obtain ⟨poles, residue, g1, hpolesK, hpolesType, hresidue,
      hg1, heq1⟩ :=
    exists_explicitFormula_regularization_without_zero hx hK hzero
  have hpolesZero : ∀ p ∈ poles, p ≠ 0 := fun p hp => (hpolesK p hp).2
  obtain ⟨g2, hg2, heq2⟩ :=
    exists_analyticOnNhd_div_id_regularization poles residue
      hzero hpolesZero hg1 heq1
  obtain ⟨g3, hg3, heq3⟩ :=
    exists_analyticOnNhd_div_id_regularization poles
      (fun p => residue p / p) hzero hpolesZero hg2 heq2
  let residue3 : ℂ → ℂ := fun p => residue p / p ^ 2
  refine ⟨poles, residue3, g3, hpolesK, hpolesType, ?_, hg3, ?_⟩
  · intro p hp
    have hp0 := hpolesZero p hp
    dsimp [residue3]
    rw [hresidue p hp]
    by_cases hp1 : p = 1
    · simp [hp1]
    · simp only [if_neg hp1]
      field_simp [hp0]
  · intro z hzK hzPoles
    have hz0 := hzero z hzK
    have h := heq3 z hzK hzPoles
    rw [show thirdOrderExplicitFormulaIntegrand x z =
        (explicitFormulaIntegrand x z / z) / z by
      unfold thirdOrderExplicitFormulaIntegrand
      field_simp [hz0]]
    rw [h]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 := hpolesZero p hp
    dsimp [residue3]
    field_simp [hp0]

theorem exists_boundaryRectIntegral_thirdOrderExplicitFormulaIntegrand_eq_residue_sum
    {x a c W : ℝ} (hx : 0 < x) (ha : 0 < a) (hac : a < c)
    (hboundary : ∀ p ∈ uIcc a c ×ℂ uIcc (-W) W,
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles, a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      MathlibAux.boundaryRectIntegral
          (thirdOrderExplicitFormulaIntegrand x) a c (-W) W =
        2 * Real.pi * Complex.I * ∑ p ∈ poles, residue p := by
  let K : Set ℂ := uIcc a c ×ℂ uIcc (-W) W
  have hK : IsCompact K := isCompact_uIcc.reProdIm isCompact_uIcc
  have hzero : ∀ z ∈ K, z ≠ 0 := by
    intro z hzK hz0
    have hzre : z.re ∈ uIcc a c := hzK.1
    rw [uIcc_of_le hac.le] at hzre
    subst z
    simp at hzre
    linarith
  obtain ⟨poles, residue, g, hpolesK, hpolesType, hresidue,
      hg, heq⟩ :=
    exists_thirdOrderExplicitFormula_analytic_regularized_remainder hx hK hzero
  have hpolesInterior : ∀ p ∈ poles,
      a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W := by
    intro p hp
    exact hboundary p (hpolesK p hp).1 (hpolesType p hp)
  refine ⟨poles, residue, hpolesInterior, hpolesType, hresidue, ?_⟩
  have hregularized :=
    MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
      poles residue hg.differentiableOn hpolesInterior
  have hcongr := MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
    (f := thirdOrderExplicitFormulaIntegrand x)
    (g := fun z => g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p)
    (x0 := a) (x1 := c) (y0 := -W) (y1 := W) (fun z hzK hzBoundary => by
      apply heq z hzK
      intro hzPole
      exact hzBoundary (hpolesInterior z hzPole))
  exact hcongr.trans hregularized

noncomputable def thirdOrderContourRemainder (x a c W : ℝ) : ℂ :=
  ((∫ σ : ℝ in a..c,
        thirdOrderExplicitFormulaIntegrand x
          ((σ : ℂ) + (-(2 * Real.pi * W) : ℝ) * Complex.I)) -
      (∫ σ : ℝ in a..c,
        thirdOrderExplicitFormulaIntegrand x
          ((σ : ℂ) + (2 * Real.pi * W : ℝ) * Complex.I)) -
    Complex.I *
      (∫ t : ℝ in -(2 * Real.pi * W)..2 * Real.pi * W,
        thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * Complex.I))) /
    (2 * Real.pi * Complex.I)

theorem exists_scaledRightIntegral_eq_residue_sum_sub_thirdOrderContourRemainder
    {x a c W : ℝ} (hx : 0 < x) (ha : 0 < a) (hac : a < c)
    (hboundary : ∀ p ∈ uIcc a c ×ℂ
        uIcc (-(2 * Real.pi * W)) (2 * Real.pi * W),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles, a < p.re ∧ p.re < c ∧
        -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      (∫ w : ℝ in -W..W,
        thirdOrderExplicitFormulaIntegrand x
          ((c : ℂ) + 2 * Real.pi * w * Complex.I)) =
        ∑ p ∈ poles, residue p - thirdOrderContourRemainder x a c W := by
  obtain ⟨poles, residue, hpoles, hpolesType, hresidue, hrect⟩ :=
    exists_boundaryRectIntegral_thirdOrderExplicitFormulaIntegrand_eq_residue_sum
      hx ha hac hboundary
  refine ⟨poles, residue, hpoles, hpolesType, hresidue, ?_⟩
  have hscale := I_mul_verticalIntegral_eq_two_pi_I_mul_scaledIntegral
    (thirdOrderExplicitFormulaIntegrand x) c W
  unfold MathlibAux.boundaryRectIntegral at hrect
  simp only [smul_eq_mul] at hrect
  rw [hscale] at hrect
  let B : ℂ := ∫ σ : ℝ in a..c,
    thirdOrderExplicitFormulaIntegrand x
      ((σ : ℂ) + (-(2 * Real.pi * W) : ℝ) * Complex.I)
  let T : ℂ := ∫ σ : ℝ in a..c,
    thirdOrderExplicitFormulaIntegrand x
      ((σ : ℂ) + (2 * Real.pi * W : ℝ) * Complex.I)
  let L : ℂ := ∫ t : ℝ in -(2 * Real.pi * W)..2 * Real.pi * W,
    thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * Complex.I)
  let R : ℂ := ∫ w : ℝ in -W..W,
    thirdOrderExplicitFormulaIntegrand x
      ((c : ℂ) + 2 * Real.pi * w * Complex.I)
  let S : ℂ := ∑ p ∈ poles, residue p
  let q : ℂ := 2 * Real.pi * Complex.I
  have hq : q ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  change B - T + q * R - Complex.I * L = q * S at hrect
  change R = S - (B - T - Complex.I * L) / q
  field_simp [hq]
  linear_combination hrect

end PrimeNumberTheorem.ExplicitFormulaResidues
