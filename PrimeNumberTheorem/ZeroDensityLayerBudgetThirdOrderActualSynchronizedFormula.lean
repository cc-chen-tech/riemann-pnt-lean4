import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderSynchronizedGoodHeight
import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderZeroResidueLSeriesBridge

open Complex Set Filter Topology
open scoped ArithmeticFunction BigOperators

namespace PrimeNumberTheorem

/-- A good height automatically puts the pole at one and every zeta zero in
the closed `[-1,c] x [-T,T]` rectangle strictly in its interior. -/
theorem thirdOrderExplicitFormulaBoundary_of_goodHeight
    {c T : ℝ} (hc : 1 < c) (hT : 0 < T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    ∀ p ∈ uIcc (-1 : ℝ) c ×ℂ uIcc (-T) T,
      p = 1 ∨ riemannZeta p = 0 →
        (-1 : ℝ) < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T := by
  intro p hp hpType
  have hcle : (-1 : ℝ) ≤ c := by linarith
  have hTle : -T ≤ T := by linarith
  rw [mem_reProdIm, uIcc_of_le hcle, uIcc_of_le hTle] at hp
  rcases hpType with hp1 | hpzero
  · subst p
    simp only [Complex.one_re, Complex.one_im]
    exact ⟨by norm_num, hc, by linarith, hT⟩
  · have hleft : p.re ≠ -1 := by
      intro hpre
      have hzeta := PrimeNumberTheorem.riemannZeta_ne_zero_of_re_le_zero
        (s := p) (by linarith)
      exact hzeta (by
        intro n hn
        have hre := congrArg Complex.re hn
        have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        simp at hre
        linarith) hpzero
    have hright : p.re ≠ c := by
      intro hpre
      exact (riemannZeta_ne_zero_of_one_le_re (by linarith)) hpzero
    have hbottom : p.im ≠ -T := by
      intro hpim
      have habs : |p.im| = T := by
        rw [hpim, abs_neg, abs_of_nonneg hT.le]
      have hzrepr : (p.re : ℂ) + I * p.im = p := by
        apply Complex.ext <;> simp
      have hzeta :=
        ExplicitFormulaResidues.riemannZeta_ne_zero_on_goodHeight_horizontal
          (T := T) (t := p.im) (σ := p.re) hT habs hgood
      rw [hzrepr] at hzeta
      exact hzeta hpzero
    have htop : p.im ≠ T := by
      intro hpim
      have habs : |p.im| = T := by
        rw [hpim, abs_of_nonneg hT.le]
      have hzrepr : (p.re : ℂ) + I * p.im = p := by
        apply Complex.ext <;> simp
      have hzeta :=
        ExplicitFormulaResidues.riemannZeta_ne_zero_on_goodHeight_horizontal
          (T := T) (t := p.im) (σ := p.re) hT habs hgood
      rw [hzrepr] at hzeta
      exact hzeta hpzero
    exact ⟨lt_of_le_of_ne hp.1.1 (Ne.symm hleft),
      lt_of_le_of_ne hp.1.2 hright,
      lt_of_le_of_ne hp.2.1 (Ne.symm hbottom),
      lt_of_le_of_ne hp.2.2 htop⟩

/-- At one good height in the `x^(3/4)` window, the genuine second-smoothed
Chebyshev explicit formula has both its contour term and its remaining Perron
error small, with the latter normalized at every target scale `x^beta` for
`beta > 2/3`. -/
theorem eventually_exists_goodHeight_thirdOrderActualPsiFormula_normalized_error_lt
    {beta c : ℝ} (hbeta : 2 / 3 < beta)
    (hc : 1 < c) (hcTwo : c ≤ 2) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in atTop,
        ∃ T ∈ Icc (x ^ (3 / 4 : ℝ)) (x ^ (3 / 4 : ℝ) + 1),
          ∃ (poles : Finset ℂ) (residue : ℂ → ℂ) (cubic : ℂ),
            ExplicitFormulaAux.goodHeight T ∧
            ‖ExplicitFormulaResidues.thirdOrderContourRemainder
                x (-1) c (T / (2 * Real.pi))‖ < ε ∧
            0 ∈ poles ∧
            (∀ p ∈ poles, (-1 : ℝ) < p.re ∧ p.re < c ∧
              -T < p.im ∧ p.im < T) ∧
            (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
            (∀ p ∈ poles, residue p =
              if p = 0 then residue 0
              else if p = 1 then (x : ℂ)
              else -(analyticOrderNatAt riemannZeta p : ℂ) *
                (x : ℂ) ^ p / p ^ 3) ∧
            residue 0 =
              iteratedDeriv 2
                (ExplicitFormulaResidues.thirdOrderZeroCore x) 0 / 2 ∧
            cubic = -deriv riemannZeta 0 / riemannZeta 0 ∧
            x ^ (-beta) *
                ‖(∑ p ∈ poles, residue p) -
                  ExplicitFormulaResidues.thirdOrderContourRemainder
                    x (-1) c (T / (2 * Real.pi)) -
                  (secondSmoothedChebyshevPsi x : ℂ)‖ < ε := by
  intro ε hε
  filter_upwards
      [eventually_exists_goodHeight_thirdOrderContour_and_normalizedPerron_lt
        hbeta hc hcTwo ε hε,
       eventually_ge_atTop (1 : ℝ)] with x hxSelected hxOne
  obtain ⟨T, hTwindow, hgood, hcontour, hperron⟩ := hxSelected
  have hxpos : 0 < x := zero_lt_one.trans_le hxOne
  have hbasePos : 0 < x ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hTpos : 0 < T := hbasePos.trans_le hTwindow.1
  have hscalePos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hWpos : 0 < T / (2 * Real.pi) := div_pos hTpos hscalePos
  have hscale : 2 * Real.pi * (T / (2 * Real.pi)) = T := by
    field_simp
  have hboundary :=
    thirdOrderExplicitFormulaBoundary_of_goodHeight hc hTpos hgood
  have hboundaryW :
      ∀ p ∈ uIcc (-1 : ℝ) c ×ℂ
          uIcc (-(2 * Real.pi * (T / (2 * Real.pi))))
            (2 * Real.pi * (T / (2 * Real.pi))),
        p = 1 ∨ riemannZeta p = 0 →
          (-1 : ℝ) < p.re ∧ p.re < c ∧
            -(2 * Real.pi * (T / (2 * Real.pi))) < p.im ∧
            p.im < 2 * Real.pi * (T / (2 * Real.pi)) := by
    simpa [hscale] using hboundary
  obtain ⟨poles, residue, cubic, hzero, hpoles, hpolesType,
      hresidue, hresidueZero, hcubic, hformula⟩ :=
    exists_thirdOrderExplicitZeroPoleFormula_secondSmoothedPsi_error_le
      hxpos (by norm_num) hc hWpos hboundaryW
  refine ⟨T, hTwindow, poles, residue, cubic, hgood, hcontour,
    hzero, ?_, hpolesType, hresidue, hresidueZero, hcubic, ?_⟩
  · simpa [hscale] using hpoles
  · have hformulaMajorant :
        ‖(∑ p ∈ poles, residue p) -
            ExplicitFormulaResidues.thirdOrderContourRemainder
              x (-1) c (T / (2 * Real.pi)) -
            (secondSmoothedChebyshevPsi x : ℂ)‖ ≤
          thirdOrderPerronErrorMajorant x c (T / (2 * Real.pi)) := by
      simpa [thirdOrderPerronErrorMajorant] using hformula
    exact
      (mul_le_mul_of_nonneg_left hformulaMajorant
        (Real.rpow_nonneg hxpos.le _)).trans_lt hperron

end PrimeNumberTheorem
