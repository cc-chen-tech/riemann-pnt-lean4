import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderZeroPoleRegularization
import MathlibAux.BoundaryRectHigherPrincipalParts

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

private lemma polePowerTerm_boundaryRectIntervalIntegrable
    (p A : ℂ) (n : ℕ) {x0 x1 y0 y1 : ℝ}
    (hx0p : x0 < p.re) (hpx1 : p.re < x1)
    (hy0p : y0 < p.im) (hpy1 : p.im < y1) :
    IntervalIntegrable
        (fun x : ℝ => (((x + y0 * I) - p)⁻¹) ^ n * A)
        MeasureTheory.volume x0 x1 ∧
      IntervalIntegrable
        (fun x : ℝ => (((x + y1 * I) - p)⁻¹) ^ n * A)
        MeasureTheory.volume x0 x1 ∧
      IntervalIntegrable
        (fun y : ℝ => (((x1 : ℂ) + y * I - p)⁻¹) ^ n * A)
        MeasureTheory.volume y0 y1 ∧
      IntervalIntegrable
        (fun y : ℝ => (((x0 : ℂ) + y * I - p)⁻¹) ^ n * A)
        MeasureTheory.volume y0 y1 := by
  have horizontal_continuous : ∀ y : ℝ, y ≠ p.im →
      Continuous (fun x : ℝ => (((x + y * I) - p)⁻¹) ^ n * A) := by
    intro y hy
    apply ((((Complex.continuous_ofReal.add
      (continuous_const.mul continuous_const)).sub continuous_const).inv₀ ?_).pow n).mul
      continuous_const
    intro x hx
    apply hy
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have vertical_continuous : ∀ x : ℝ, x ≠ p.re →
      Continuous (fun y : ℝ => ((((x : ℂ) + y * I) - p)⁻¹) ^ n * A) := by
    intro x hx
    apply ((((continuous_const.add
      (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const).inv₀ ?_).pow n).mul
      continuous_const
    intro y hy
    apply hx
    have hr' := congrArg Complex.re hy
    simp at hr'
    linarith
  exact ⟨
    (horizontal_continuous y0 (by linarith)).intervalIntegrable x0 x1,
    (horizontal_continuous y1 (by linarith)).intervalIntegrable x0 x1,
    (vertical_continuous x1 (by linarith)).intervalIntegrable y0 y1,
    (vertical_continuous x0 (by linarith)).intervalIntegrable y0 y1⟩

private lemma zeroPowerTerm_boundaryRectIntervalIntegrable
    (A : ℂ) (n : ℕ) {x0 x1 y0 y1 : ℝ}
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0)
    (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) :
    IntervalIntegrable
        (fun x : ℝ => ((x + y0 * I)⁻¹) ^ n * A)
        MeasureTheory.volume x0 x1 ∧
      IntervalIntegrable
        (fun x : ℝ => ((x + y1 * I)⁻¹) ^ n * A)
        MeasureTheory.volume x0 x1 ∧
      IntervalIntegrable
        (fun y : ℝ => (((x1 : ℂ) + y * I)⁻¹) ^ n * A)
        MeasureTheory.volume y0 y1 ∧
      IntervalIntegrable
        (fun y : ℝ => (((x0 : ℂ) + y * I)⁻¹) ^ n * A)
        MeasureTheory.volume y0 y1 := by
  have horizontal_continuous : ∀ y : ℝ, y ≠ 0 →
      Continuous (fun x : ℝ => ((x + y * I)⁻¹) ^ n * A) := by
    intro y hy
    apply (((Complex.continuous_ofReal.add
      (continuous_const.mul continuous_const)).inv₀ ?_).pow n).mul
      continuous_const
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    exact hy hi
  have vertical_continuous : ∀ x : ℝ, x ≠ 0 →
      Continuous (fun y : ℝ => (((x : ℂ) + y * I)⁻¹) ^ n * A) := by
    intro x hx
    apply (((continuous_const.add
      (Complex.continuous_ofReal.mul continuous_const)).inv₀ ?_).pow n).mul
      continuous_const
    intro y hy
    have hr := congrArg Complex.re hy
    simp at hr
    exact hx hr
  exact ⟨
    (horizontal_continuous y0 hy0).intervalIntegrable x0 x1,
    (horizontal_continuous y1 hy1).intervalIntegrable x0 x1,
    (vertical_continuous x1 hx1).intervalIntegrable y0 y1,
    (vertical_continuous x0 hx0).intervalIntegrable y0 y1⟩

namespace PrimeNumberTheorem.ExplicitFormulaResidues

/-- Residue formula for the genuine third-order kernel across zero. The zero
pole is retained in the simple-residue sum, while its quadratic and cubic
principal parts have vanishing closed boundary integral. -/
theorem exists_boundaryRectIntegral_thirdOrderExplicitFormulaIntegrand_eq_residue_sum_zeroPole
    {x a c W : ℝ} (hx : 0 < x) (ha : a < 0) (hc : 0 < c)
    (hW : 0 < W)
    (hboundary : ∀ p ∈ uIcc a c ×ℂ uIcc (-W) W,
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ)
        (cubic : ℂ),
      0 ∈ poles ∧
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 0 then residue 0
        else if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      cubic = -deriv riemannZeta 0 / riemannZeta 0 ∧
      MathlibAux.boundaryRectIntegral
          (thirdOrderExplicitFormulaIntegrand x) a c (-W) W =
        2 * Real.pi * Complex.I * ∑ p ∈ poles, residue p := by
  let K : Set ℂ := uIcc a c ×ℂ uIcc (-W) W
  have hac : a ≤ c := (ha.trans hc).le
  have hWW : -W ≤ W := by linarith
  have h0K : (0 : ℂ) ∈ K := by
    change (0 : ℝ) ∈ uIcc a c ∧ (0 : ℝ) ∈ uIcc (-W) W
    rw [uIcc_of_le hac, uIcc_of_le hWW]
    constructor <;> constructor <;> linarith
  have hK : IsCompact K := isCompact_uIcc.reProdIm isCompact_uIcc
  obtain ⟨poles, residue, quadratic, cubic, G, h0mem, hpolesK,
      hpolesType, hresidue, hcubic, hG, heq⟩ :=
    exists_thirdOrderExplicitFormula_zeroPole_regularization hx hK h0K
  have hpolesInterior : ∀ p ∈ poles,
      a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W := by
    intro p hp
    rcases hpolesK p hp with hp0 | hpK
    · subst p
      simp only [Complex.zero_re, Complex.zero_im]
      exact ⟨ha, hc, by linarith, hW⟩
    · rcases hpolesType p hp with hp0 | hptype
      · subst p
        simp only [Complex.zero_re, Complex.zero_im]
        exact ⟨ha, hc, by linarith, hW⟩
      · exact hboundary p hpK hptype
  refine ⟨poles, residue, cubic, h0mem, hpolesInterior,
    hpolesType, hresidue, hcubic, ?_⟩
  let term : ℂ → ℂ → ℂ := fun p z => (z - p)⁻¹ * residue p
  let principal : ℂ → ℂ := fun z => ∑ p ∈ poles, term p z
  let base : ℂ → ℂ := fun z => G z + principal z
  let quad : ℂ → ℂ := fun z => z⁻¹ ^ 2 * quadratic
  let cube : ℂ → ℂ := fun z => z⁻¹ ^ 3 * cubic
  have hG_edges :=
    MathlibAux.boundaryRectIntervalIntegrable_of_continuousOn hG.continuousOn
  have hterm_edges : ∀ p ∈ poles,
      IntervalIntegrable (fun t : ℝ => term p (t + ((-W : ℝ) : ℂ) * I))
          MeasureTheory.volume a c ∧
        IntervalIntegrable (fun t : ℝ => term p (t + W * I))
          MeasureTheory.volume a c ∧
        IntervalIntegrable (fun t : ℝ => term p ((c : ℂ) + t * I))
          MeasureTheory.volume (-W) W ∧
        IntervalIntegrable (fun t : ℝ => term p ((a : ℂ) + t * I))
          MeasureTheory.volume (-W) W := by
    intro p hp
    have h := hpolesInterior p hp
    simpa [term] using polePowerTerm_boundaryRectIntervalIntegrable
      p (residue p) 1 h.1 h.2.1 h.2.2.1 h.2.2.2
  have hprincipal_bottom : IntervalIntegrable
      (fun t : ℝ => principal (t + ((-W : ℝ) : ℂ) * I))
      MeasureTheory.volume a c := by
    have h := IntervalIntegrable.sum poles (fun p hp => (hterm_edges p hp).1)
    have heq' : (∑ p ∈ poles, fun t : ℝ => term p (t + ((-W : ℝ) : ℂ) * I)) =
        fun t : ℝ => principal (t + ((-W : ℝ) : ℂ) * I) := by
      funext t
      simp [principal]
    rw [← heq']
    exact h
  have hprincipal_top : IntervalIntegrable
      (fun t : ℝ => principal (t + W * I))
      MeasureTheory.volume a c := by
    have h := IntervalIntegrable.sum poles (fun p hp => (hterm_edges p hp).2.1)
    have heq' : (∑ p ∈ poles, fun t : ℝ => term p (t + W * I)) =
        fun t : ℝ => principal (t + W * I) := by
      funext t
      simp [principal]
    rw [← heq']
    exact h
  have hprincipal_right : IntervalIntegrable
      (fun t : ℝ => principal ((c : ℂ) + t * I))
      MeasureTheory.volume (-W) W := by
    have h := IntervalIntegrable.sum poles (fun p hp => (hterm_edges p hp).2.2.1)
    have heq' : (∑ p ∈ poles, fun t : ℝ => term p ((c : ℂ) + t * I)) =
        fun t : ℝ => principal ((c : ℂ) + t * I) := by
      funext t
      simp [principal]
    rw [← heq']
    exact h
  have hprincipal_left : IntervalIntegrable
      (fun t : ℝ => principal ((a : ℂ) + t * I))
      MeasureTheory.volume (-W) W := by
    have h := IntervalIntegrable.sum poles (fun p hp => (hterm_edges p hp).2.2.2)
    have heq' : (∑ p ∈ poles, fun t : ℝ => term p ((a : ℂ) + t * I)) =
        fun t : ℝ => principal ((a : ℂ) + t * I) := by
      funext t
      simp [principal]
    rw [← heq']
    exact h
  have hbase_edges :
      IntervalIntegrable (fun t : ℝ => base (t + ((-W : ℝ) : ℂ) * I))
          MeasureTheory.volume a c ∧
        IntervalIntegrable (fun t : ℝ => base (t + W * I))
          MeasureTheory.volume a c ∧
        IntervalIntegrable (fun t : ℝ => base ((c : ℂ) + t * I))
          MeasureTheory.volume (-W) W ∧
        IntervalIntegrable (fun t : ℝ => base ((a : ℂ) + t * I))
          MeasureTheory.volume (-W) W := by
    constructor
    · simpa [base] using hG_edges.1.add hprincipal_bottom
    constructor
    · simpa [base] using hG_edges.2.1.add hprincipal_top
    constructor
    · simpa [base] using hG_edges.2.2.1.add hprincipal_right
    · simpa [base] using hG_edges.2.2.2.add hprincipal_left
  have hquad_edges :
      IntervalIntegrable (fun t : ℝ => quad (t + ((-W : ℝ) : ℂ) * I))
          MeasureTheory.volume a c ∧
        IntervalIntegrable (fun t : ℝ => quad (t + W * I))
          MeasureTheory.volume a c ∧
        IntervalIntegrable (fun t : ℝ => quad ((c : ℂ) + t * I))
          MeasureTheory.volume (-W) W ∧
        IntervalIntegrable (fun t : ℝ => quad ((a : ℂ) + t * I))
          MeasureTheory.volume (-W) W := by
    dsimp only [quad]
    exact zeroPowerTerm_boundaryRectIntervalIntegrable quadratic 2
      (x0 := a) (x1 := c) (y0 := -W) (y1 := W)
      (by linarith) (by linarith) (by linarith) (by linarith)
  have hcube_edges :
      IntervalIntegrable (fun t : ℝ => cube (t + ((-W : ℝ) : ℂ) * I))
          MeasureTheory.volume a c ∧
        IntervalIntegrable (fun t : ℝ => cube (t + W * I))
          MeasureTheory.volume a c ∧
        IntervalIntegrable (fun t : ℝ => cube ((c : ℂ) + t * I))
          MeasureTheory.volume (-W) W ∧
        IntervalIntegrable (fun t : ℝ => cube ((a : ℂ) + t * I))
          MeasureTheory.volume (-W) W := by
    dsimp only [cube]
    exact zeroPowerTerm_boundaryRectIntervalIntegrable cubic 3
      (x0 := a) (x1 := c) (y0 := -W) (y1 := W)
      (by linarith) (by linarith) (by linarith) (by linarith)
  have hbase_formula :
      MathlibAux.boundaryRectIntegral base a c (-W) W =
        (2 * Real.pi * I) * ∑ p ∈ poles, residue p := by
    simpa [base, principal, term] using
      MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
        poles residue hG.differentiableOn hpolesInterior
  have hadd_quad :
      MathlibAux.boundaryRectIntegral (fun z => base z + quad z) a c (-W) W =
        MathlibAux.boundaryRectIntegral base a c (-W) W +
          MathlibAux.boundaryRectIntegral quad a c (-W) W :=
    MathlibAux.boundaryRectIntegral_add base quad a c (-W) W
      hbase_edges.1 hquad_edges.1
      hbase_edges.2.1 hquad_edges.2.1
      hbase_edges.2.2.1 hquad_edges.2.2.1
      hbase_edges.2.2.2 hquad_edges.2.2.2
  have hbase_quad_edges :
      IntervalIntegrable (fun t : ℝ => base (t + ((-W : ℝ) : ℂ) * I) + quad (t + ((-W : ℝ) : ℂ) * I))
          MeasureTheory.volume a c ∧
        IntervalIntegrable (fun t : ℝ => base (t + W * I) + quad (t + W * I))
          MeasureTheory.volume a c ∧
        IntervalIntegrable
          (fun t : ℝ => base ((c : ℂ) + t * I) + quad ((c : ℂ) + t * I))
          MeasureTheory.volume (-W) W ∧
        IntervalIntegrable
          (fun t : ℝ => base ((a : ℂ) + t * I) + quad ((a : ℂ) + t * I))
          MeasureTheory.volume (-W) W :=
    ⟨hbase_edges.1.add hquad_edges.1,
      hbase_edges.2.1.add hquad_edges.2.1,
      hbase_edges.2.2.1.add hquad_edges.2.2.1,
      hbase_edges.2.2.2.add hquad_edges.2.2.2⟩
  have hadd_cube :
      MathlibAux.boundaryRectIntegral
          (fun z => (base z + quad z) + cube z) a c (-W) W =
        MathlibAux.boundaryRectIntegral (fun z => base z + quad z) a c (-W) W +
          MathlibAux.boundaryRectIntegral cube a c (-W) W :=
    MathlibAux.boundaryRectIntegral_add (fun z => base z + quad z) cube
      a c (-W) W
      hbase_quad_edges.1 hcube_edges.1
      hbase_quad_edges.2.1 hcube_edges.2.1
      hbase_quad_edges.2.2.1 hcube_edges.2.2.1
      hbase_quad_edges.2.2.2 hcube_edges.2.2.2
  have hquad_zero :
      MathlibAux.boundaryRectIntegral quad a c (-W) W = 0 := by
    have h := MathlibAux.boundaryRectIntegral_mul_const
      (fun z : ℂ => z⁻¹ ^ 2) quadratic a c (-W) W
    rw [MathlibAux.boundaryRectIntegral_inv_sq_eq_zero
      (by linarith) (by linarith) (by linarith) (by linarith), zero_mul] at h
    simpa [quad] using h
  have hcube_zero :
      MathlibAux.boundaryRectIntegral cube a c (-W) W = 0 := by
    have h := MathlibAux.boundaryRectIntegral_mul_const
      (fun z : ℂ => z⁻¹ ^ 3) cubic a c (-W) W
    rw [MathlibAux.boundaryRectIntegral_inv_cube_eq_zero
      (by linarith) (by linarith) (by linarith) (by linarith), zero_mul] at h
    simpa [cube] using h
  have hassembled :
      MathlibAux.boundaryRectIntegral
          (fun z => (base z + quad z) + cube z) a c (-W) W =
        2 * Real.pi * I * ∑ p ∈ poles, residue p := by
    rw [hadd_cube, hadd_quad, hbase_formula, hquad_zero, hcube_zero]
    ring
  have hcongr := MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
    (f := thirdOrderExplicitFormulaIntegrand x)
    (g := fun z => (base z + quad z) + cube z)
    (x0 := a) (x1 := c) (y0 := -W) (y1 := W) (fun z hzK hzBoundary => by
      have hzPoles : z ∉ poles := by
        intro hzPole
        apply hzBoundary
        exact hpolesInterior z hzPole
      rw [heq z hzK hzPoles]
      dsimp [base, principal, term, quad, cube]
      ring)
  exact hcongr.trans hassembled

end PrimeNumberTheorem.ExplicitFormulaResidues
