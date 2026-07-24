import PrimeNumberTheorem.SecondOrderExplicitFormula

open Complex Filter Topology Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- Moving the second-order Perron rectangle across `s = 0` produces one
zero-residue double pole and an ordinary finite simple-pole residue sum. -/
theorem exists_boundaryRectIntegral_secondOrderExplicitFormulaIntegrand_crossing_zero
    {x a c W : ℝ} (hx : 0 < x) (ha : a < 0) (hc : 0 < c) (hW : 0 < W)
    (hboundary : ∀ p ∈ ([[a, c]] ×ℂ [[-W, W]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈ ([[a, c]] ×ℂ [[-W, W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles) ∧
      (∀ p ∈ poles, p ≠ 0 → residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 2) ∧
      MathlibAux.boundaryRectIntegral
          (secondOrderExplicitFormulaIntegrand x) a c (-W) W =
        (2 * Real.pi * I) * ∑ p ∈ poles, residue p := by
  classical
  let K : Set ℂ := [[a, c]] ×ℂ [[-W, W]]
  have hac : a < c := ha.trans hc
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_uIcc.reProdIm isCompact_uIcc
  rcases exists_finite_explicitFormulaIntegrand_analytic_regularized_remainder
      hx hKcompact with
    ⟨oldPoles, oldResidue, holdPoles_mem, holdPoles_classify,
      holdPoles_complete, holdResidue, hoff_eq, hregular⟩
  let P : Finset ℂ := oldPoles.erase 0
  let residue2 : ℂ → ℂ := fun p => oldResidue p / p
  let r0 : ℂ := if 0 ∈ oldPoles then oldResidue 0 else 0
  let raw : ℂ → ℂ := fun z =>
    explicitFormulaIntegrand x z -
      ∑ p ∈ oldPoles, (z - p)⁻¹ * oldResidue p
  let g : ℂ → ℂ := toMeromorphicNFOn raw K
  let zeroResidue : ℂ := g 0 - ∑ p ∈ P, residue2 p
  let poles : Finset ℂ := insert 0 P
  let residue : ℂ → ℂ := fun p => if p = 0 then zeroResidue else residue2 p
  have h0K : (0 : ℂ) ∈ K := by
    simp only [K, mem_reProdIm, Complex.zero_re, Complex.zero_im]
    rw [uIcc_of_le hac.le, uIcc_of_le (by linarith : -W ≤ W)]
    constructor <;> constructor <;> linarith
  have hK_nhds : K ∈ 𝓝 (0 : ℂ) := by
    let U : Set ℂ := Ioo a c ×ℂ Ioo (-W) W
    have hUopen : IsOpen U := isOpen_Ioo.reProdIm isOpen_Ioo
    have h0U : (0 : ℂ) ∈ U := by
      simpa [U, mem_reProdIm] using
        (show (a < (0 : ℝ) ∧ 0 < c) ∧ (-W < 0 ∧ 0 < W) from
          ⟨⟨ha, hc⟩, ⟨by linarith, hW⟩⟩)
    apply mem_of_superset (hUopen.mem_nhds h0U)
    intro z hz
    rw [mem_reProdIm] at hz ⊢
    rw [uIcc_of_le hac.le, uIcc_of_le (by linarith : -W ≤ W)]
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  have hg : DifferentiableOn ℂ g K := by
    intro z hz
    exact (hregular z hz).differentiableAt.differentiableWithinAt
  have hdslope : DifferentiableOn ℂ (dslope g 0) K :=
    (Complex.differentiableOn_dslope hK_nhds).2 hg
  have hP_mem : ∀ p ∈ P,
      a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W := by
    intro p hp
    have hp' := Finset.mem_erase.mp hp
    have hp0 : p ≠ 0 := hp'.1
    have hpK : p ∈ K := (holdPoles_mem p hp'.2).resolve_left hp0
    have hpclass := holdPoles_classify p hp'.2
    exact hboundary p hpK (Or.inr (hpclass.resolve_left hp0))
  have hP_classify : ∀ p ∈ P, p = 1 ∨ riemannZeta p = 0 := by
    intro p hp
    have hp' := Finset.mem_erase.mp hp
    exact (holdPoles_classify p hp'.2).resolve_left hp'.1
  have hP_residue : ∀ p ∈ P, residue2 p =
      if p = 1 then (x : ℂ)
      else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 2 := by
    intro p hp
    have hp0 : p ≠ 0 := Finset.ne_of_mem_erase hp
    dsimp [residue2]
    rw [holdResidue p]
    by_cases hp1 : p = 1
    · subst p
      simp
    · simp only [hp1, if_false, hp0]
      field_simp [hp0]
  have hpoles_mem : ∀ p ∈ poles,
      a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simpa using
        (show a < (0 : ℝ) ∧ 0 < c ∧ -W < 0 ∧ 0 < W from
          ⟨ha, hc, by linarith, hW⟩)
    · exact hP_mem p hp
  have hpoles_classify : ∀ p ∈ poles,
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Or.inl rfl
    · exact Or.inr (hP_classify p hp)
  have hpoles_complete : ∀ p, p ∈ K →
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles := by
    intro p hpK hpclass
    by_cases hp0 : p = 0
    · subst p
      simp [poles]
    · apply Finset.mem_insert.mpr
      right
      exact Finset.mem_erase.mpr
        ⟨hp0, holdPoles_complete p hpK hpclass⟩
  have hpoles_residue : ∀ p ∈ poles, p ≠ 0 → residue p =
      if p = 1 then (x : ℂ)
      else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 2 := by
    intro p hp hp0
    have hpP : p ∈ P := (Finset.mem_insert.mp hp).resolve_left hp0
    simpa [residue, hp0] using hP_residue p hpP
  have hboundary_eq : ∀ z ∈ K,
      ¬(a < z.re ∧ z.re < c ∧ -W < z.im ∧ z.im < W) →
      secondOrderExplicitFormulaIntegrand x z =
        z⁻¹ / z * r0 +
          (dslope g 0 z +
            ∑ p ∈ poles, (z - p)⁻¹ * residue p) := by
    intro z hzK hzboundary
    have hz0 : z ≠ 0 := by
      intro hz
      subst z
      exact hzboundary (by simpa using hpoles_mem 0 (by simp [poles]))
    have hz_not_P : z ∉ P := by
      intro hzP
      exact hzboundary (hP_mem z hzP)
    have hz_not_oldPoles : z ∉ oldPoles := by
      intro hzpoles
      exact hz_not_P (Finset.mem_erase.mpr ⟨hz0, hzpoles⟩)
    have hg_eq := hoff_eq z hzK hz_not_oldPoles
    change g z = raw z at hg_eq
    have hsum_split :
        (∑ p ∈ oldPoles, (z - p)⁻¹ * oldResidue p) =
          z⁻¹ * r0 + ∑ p ∈ P, (z - p)⁻¹ * oldResidue p := by
      by_cases h0 : 0 ∈ oldPoles
      · rw [show (∑ p ∈ oldPoles, (z - p)⁻¹ * oldResidue p) =
            (∑ p ∈ oldPoles.erase 0, (z - p)⁻¹ * oldResidue p) +
              (z - 0)⁻¹ * oldResidue 0 by
            exact (Finset.sum_erase_add _ _ h0).symm]
        simp [P, r0, h0]
      · simp [P, r0, h0]
    have hterm (p : ℂ) (hp : p ∈ P) :
        ((z - p)⁻¹ * oldResidue p) / z =
          (z - p)⁻¹ * residue2 p - z⁻¹ * residue2 p := by
      exact simplePoleTerm_div_eq hz0 (Finset.ne_of_mem_erase hp)
        (fun hzp => hz_not_P (by simpa [hzp] using hp))
    have hsum_div :
        (∑ p ∈ P, (z - p)⁻¹ * oldResidue p) / z =
          (∑ p ∈ P, (z - p)⁻¹ * residue2 p) -
            z⁻¹ * ∑ p ∈ P, residue2 p := by
      rw [Finset.sum_div]
      calc
        (∑ p ∈ P, ((z - p)⁻¹ * oldResidue p) / z) =
            ∑ p ∈ P,
              ((z - p)⁻¹ * residue2 p - z⁻¹ * residue2 p) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hterm p hp
        _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hzero_not_P : (0 : ℂ) ∉ P := by simp [P]
    have hpoles_sum :
        (∑ p ∈ poles, (z - p)⁻¹ * residue p) =
          z⁻¹ * zeroResidue +
            ∑ p ∈ P, (z - p)⁻¹ * residue2 p := by
      rw [show poles = insert 0 P by rfl, Finset.sum_insert hzero_not_P]
      simp only [residue, if_pos, sub_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      rw [if_neg (Finset.ne_of_mem_erase hp)]
    dsimp [secondOrderExplicitFormulaIntegrand]
    rw [hpoles_sum, dslope_of_ne g hz0]
    simp only [slope, vsub_eq_sub, smul_eq_mul]
    have hexplicit :
        explicitFormulaIntegrand x z =
          g z + z⁻¹ * r0 +
            ∑ p ∈ P, (z - p)⁻¹ * oldResidue p := by
      rw [hg_eq]
      dsimp [raw]
      rw [hsum_split]
      ring
    rw [hexplicit]
    rw [show (g z + z⁻¹ * r0 +
          ∑ p ∈ P, (z - p)⁻¹ * oldResidue p) / z =
        g z / z + z⁻¹ * r0 / z +
          (∑ p ∈ P, (z - p)⁻¹ * oldResidue p) / z by ring]
    rw [hsum_div]
    simp only [sub_zero]
    dsimp [zeroResidue]
    field_simp [hz0]
    ring
  refine ⟨poles, residue, hpoles_mem, hpoles_classify,
    (by simpa [K] using hpoles_complete), hpoles_residue, ?_⟩
  calc
    MathlibAux.boundaryRectIntegral
        (secondOrderExplicitFormulaIntegrand x) a c (-W) W =
      MathlibAux.boundaryRectIntegral
        (fun z => z⁻¹ / z * r0 +
          (dslope g 0 z + ∑ p ∈ poles, (z - p)⁻¹ * residue p))
        a c (-W) W := by
      apply MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
      simpa [K] using hboundary_eq
    _ = (2 * Real.pi * I) * ∑ p ∈ poles, residue p := by
      exact
        MathlibAux.boundaryRectIntegral_eq_double_pole_add_finite_simple_pole_residue_sum
          r0 poles residue ha hc (by linarith) hW hdslope hpoles_mem

end ExplicitFormulaResidues
end PrimeNumberTheorem
