import HardyTheorem.SelbergFourierThetaKernel
import MathlibAux.RectangleResidue
import ZeroFreeRegion.MeromorphicAux

open Complex Set Filter Topology
open scoped Interval

namespace HardyTheorem

/-!
# The finite-height contour identity in Selberg's S1 transform

This file isolates the unique pole at `s = 1` without using any `Zeta23`
input.  The pole unit `Q(s) = (s - 1) ζ(s)` is multiplied into the analytic
Selberg weight, and `Complex.dslope` supplies the removable analytic
remainder.  The resulting arbitrary-rectangle residue identity is the
finite-height contour shift underlying equation (7.2).
-/

/-- The analytic factor multiplying `ζ(s)` in Selberg's Mellin integral. -/
noncomputable def selbergMellinWeight (z : ℂ) (X : ℕ) (s : ℂ) : ℂ :=
  Gammaℝ s * selbergSqrtZetaPsi X s * selbergSqrtZetaPsi X (1 - s) * z ^ s

/-- The pole-free product obtained by replacing `ζ` with its analytic pole
unit `Q(s) = (s - 1) ζ(s)`. -/
noncomputable def selbergMellinPoleUnit (z : ℂ) (X : ℕ) (s : ℂ) : ℂ :=
  selbergMellinWeight z X s * ZeroFreeRegion.riemannZetaPoleUnitAtOne s

/-- The analytic removable part at `s = 1`. -/
noncomputable def selbergMellinRegularPart (z : ℂ) (X : ℕ) (s : ℂ) : ℂ :=
  dslope (selbergMellinPoleUnit z X) 1 s

/-- The globally defined simple-pole normal form on `Re(s) > 0`. -/
noncomputable def selbergMellinRegularizedIntegrand
    (z : ℂ) (X : ℕ) (s : ℂ) : ℂ :=
  selbergMellinRegularPart z X s +
    (s - 1)⁻¹ * selbergMellinWeight z X 1

/-- The original completed-zeta mollified Mellin integrand. -/
noncomputable def selbergMellinRawIntegrand
    (z : ℂ) (X : ℕ) (s : ℂ) : ℂ :=
  selbergMellinWeight z X s * riemannZeta s

private theorem analyticAt_Gammaℝ_of_re_pos
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Gammaℝ s := by
  have hinv : AnalyticAt ℂ (fun w : ℂ => (Gammaℝ w)⁻¹) s :=
    differentiable_Gammaℝ_inv.analyticAt s
  have hne : (Gammaℝ s)⁻¹ ≠ 0 :=
    inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs)
  have hfun : (fun w : ℂ => ((Gammaℝ w)⁻¹)⁻¹) = Gammaℝ := by
    funext w
    simp
  rw [← hfun]
  exact hinv.inv hne

private theorem analyticOnNhd_selbergSqrtZetaPsi (X : ℕ) :
    AnalyticOnNhd ℂ (selbergSqrtZetaPsi X) Set.univ := by
  unfold selbergSqrtZetaPsi selbergMollifier
  apply Finset.analyticOnNhd_fun_sum
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  have hpow : AnalyticOnNhd ℂ (fun s : ℂ => (n : ℂ) ^ s) Set.univ :=
    analyticOnNhd_const.cpow analyticOnNhd_id fun _ _ =>
      Complex.natCast_mem_slitPlane.mpr hn0
  have hinv : AnalyticOnNhd ℂ (fun s : ℂ => ((n : ℂ) ^ s)⁻¹) Set.univ :=
    hpow.inv fun _ _ => Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Nat.cast_ne_zero.mpr hn0))
  simpa only [one_div] using analyticOnNhd_const.mul hinv

/-- Selberg's complete analytic weight is holomorphic on the right
half-plane; only the Gamma factor requires excluding `Re(s) ≤ 0`. -/
theorem analyticOnNhd_selbergMellinWeight
    {z : ℂ} (hz : z ≠ 0) (X : ℕ) :
    AnalyticOnNhd ℂ (selbergMellinWeight z X) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hpsi : AnalyticOnNhd ℂ (selbergSqrtZetaPsi X) Set.univ :=
    analyticOnNhd_selbergSqrtZetaPsi X
  have hpsi_s : AnalyticAt ℂ (selbergSqrtZetaPsi X) s :=
    hpsi s (Set.mem_univ s)
  have hreflection : AnalyticAt ℂ
      (fun w : ℂ => selbergSqrtZetaPsi X (1 - w)) s :=
    AnalyticAt.comp
      (g := selbergSqrtZetaPsi X)
      (f := fun w : ℂ => 1 - w)
      (x := s)
      (hpsi (1 - s) (Set.mem_univ _))
      (analyticAt_const.sub analyticAt_id)
  have hpow : AnalyticAt ℂ (fun w : ℂ => z ^ w) s :=
    ((differentiable_id : Differentiable ℂ (fun w : ℂ => w)).const_cpow
      (Or.inl hz)).analyticAt s
  exact (((analyticAt_Gammaℝ_of_re_pos hs).mul hpsi_s).mul hreflection).mul hpow

/-- The residue coefficient before simplification. -/
theorem selbergMellinWeight_one (z : ℂ) (X : ℕ) :
    selbergMellinWeight z X 1 =
      z * selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0 := by
  simp only [selbergMellinWeight, Gammaℝ_one, one_mul, sub_self,
    cpow_one]
  ring

/-- The analytic pole-unit product is holomorphic throughout `Re(s) > 0`. -/
theorem analyticOnNhd_selbergMellinPoleUnit
    {z : ℂ} (hz : z ≠ 0) (X : ℕ) :
    AnalyticOnNhd ℂ (selbergMellinPoleUnit z X) {s : ℂ | 0 < s.re} := by
  intro s hs
  exact ((analyticOnNhd_selbergMellinWeight hz X) s hs).mul
    ((ZeroFreeRegion.analyticOnNhd_riemannZetaPoleUnitAtOne_re_gt
      (show (0 : ℝ) ≤ 0 by rfl)) s hs)

theorem selbergMellinPoleUnit_one (z : ℂ) (X : ℕ) :
    selbergMellinPoleUnit z X 1 = selbergMellinWeight z X 1 := by
  simp [selbergMellinPoleUnit,
    ZeroFreeRegion.riemannZetaPoleUnitAtOne_one]

/-- `dslope` fills in the removable value at one and is differentiable on
the whole right half-plane. -/
theorem differentiableOn_selbergMellinRegularPart
    {z : ℂ} (hz : z ≠ 0) (X : ℕ) :
    DifferentiableOn ℂ (selbergMellinRegularPart z X) {s : ℂ | 0 < s.re} := by
  let U : Set ℂ := {s : ℂ | 0 < s.re}
  have hUopen : IsOpen U :=
    isOpen_lt continuous_const Complex.continuous_re
  have h1U : (1 : ℂ) ∈ U := by simp [U]
  have hUnhds : U ∈ 𝓝 (1 : ℂ) := hUopen.mem_nhds h1U
  have hB : DifferentiableOn ℂ (selbergMellinPoleUnit z X) U :=
    (analyticOnNhd_selbergMellinPoleUnit hz X).differentiableOn
  change DifferentiableOn ℂ (dslope (selbergMellinPoleUnit z X) 1)
    {s : ℂ | 0 < s.re}
  exact (Complex.differentiableOn_dslope hUnhds).2 hB

/-- Away from the pole, the original integrand equals its analytic remainder
plus the exact simple principal part. -/
theorem selbergMellinRaw_eq_regularized
    {z s : ℂ} (hz : z ≠ 0) (X : ℕ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    selbergMellinRawIntegrand z X s =
      selbergMellinRegularizedIntegrand z X s := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  have hQ := ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
    hs0 hs1
  rw [selbergMellinRawIntegrand, selbergMellinRegularizedIntegrand,
    selbergMellinRegularPart, dslope_of_ne _ hs1]
  simp only [slope, vsub_eq_sub, smul_eq_mul]
  rw [selbergMellinPoleUnit, hQ, selbergMellinPoleUnit_one]
  field_simp [sub_ne_zero.mpr hs1]
  ring

/-- The finite-height contour of the regularized normal form sees only the
simple pole at one. -/
theorem boundaryRectIntegral_selbergMellinRegularized
    {z : ℂ} (hz : z ≠ 0) (X : ℕ) {c T : ℝ}
    (hc : 1 < c) (hT : 0 < T) :
    MathlibAux.boundaryRectIntegral (selbergMellinRegularizedIntegrand z X)
        (1 / 2) c (-T) T =
      (2 * Real.pi * I) *
        (z * selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0) := by
  have hhalf_c : (1 / 2 : ℝ) < c := by linarith
  have hregular : DifferentiableOn ℂ (selbergMellinRegularPart z X)
      ([[(1 / 2 : ℝ), c]] ×ℂ [[-T, T]]) := by
    apply (differentiableOn_selbergMellinRegularPart hz X).mono
    intro s hsrect
    rw [mem_reProdIm, uIcc_of_le hhalf_c.le] at hsrect
    exact lt_of_lt_of_le (by norm_num) hsrect.1.1
  have hres :=
    MathlibAux.boundaryRectIntegral_eq_simple_pole_residue_of_differentiableOn
      (g := selbergMellinRegularPart z X)
      (p := (1 : ℂ)) (a := selbergMellinWeight z X 1)
      hregular (by norm_num) (by simpa using hc)
        (by norm_num; linarith) (by simpa using hT)
  change MathlibAux.boundaryRectIntegral
      (fun s => selbergMellinRegularPart z X s +
        (s - 1)⁻¹ * selbergMellinWeight z X 1)
      (1 / 2) c (-T) T = _
  simpa only [selbergMellinWeight_one] using hres

/-- Finite-height Selberg contour identity for the original integrand.  The
pole lies strictly inside the rectangle, so raw and regularized integrands
agree on all four edges. -/
theorem boundaryRectIntegral_selbergMellinRaw
    {z : ℂ} (hz : z ≠ 0) (X : ℕ) {c T : ℝ}
    (hc : 1 < c) (hT : 0 < T) :
    MathlibAux.boundaryRectIntegral (selbergMellinRawIntegrand z X)
        (1 / 2) c (-T) T =
      (2 * Real.pi * I) *
        (z * selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0) := by
  have hhalf_c : (1 / 2 : ℝ) < c := by linarith
  rw [MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
    (g := selbergMellinRegularizedIntegrand z X) (by
      intro s hsrect hsboundary
      have hsrect' := hsrect
      rw [mem_reProdIm, uIcc_of_le hhalf_c.le,
        uIcc_of_le (by linarith : -T ≤ T)] at hsrect'
      have hsre : 0 < s.re :=
        lt_of_lt_of_le (by norm_num) hsrect'.1.1
      have hs1 : s ≠ 1 := by
        intro h
        subst s
        apply hsboundary
        exact ⟨by norm_num, hc, neg_lt_zero.mpr hT, hT⟩
      exact selbergMellinRaw_eq_regularized hz X hsre hs1)]
  exact boundaryRectIntegral_selbergMellinRegularized hz X hc hT

/-- With Selberg's `1/(4πi)` normalization, crossing the zeta pole contributes
exactly one half of its residue. -/
theorem normalized_boundaryRectIntegral_selbergMellinRaw
    {z : ℂ} (hz : z ≠ 0) (X : ℕ) {c T : ℝ}
    (hc : 1 < c) (hT : 0 < T) :
    (1 / (4 * Real.pi * I) : ℂ) *
        MathlibAux.boundaryRectIntegral (selbergMellinRawIntegrand z X)
          (1 / 2) c (-T) T =
      (1 / 2 : ℂ) *
        (z * selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0) := by
  rw [boundaryRectIntegral_selbergMellinRaw hz X hc hT]
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi, I_ne_zero]
  ring

end HardyTheorem
