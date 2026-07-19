import MathlibAux.BoundaryRectResidue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import ZeroFreeRegion.MeromorphicAux

open Complex Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Along a vertical line, the derivative of `log ‖f‖` is the negative
imaginary part of the logarithmic derivative of `f`. -/
theorem hasDerivAt_log_norm_vertical
    {f : ℂ → ℂ} {sigma t : ℝ}
    (hf : AnalyticAt ℂ f ((sigma : ℂ) + I * (t : ℂ)))
    (hne : f ((sigma : ℂ) + I * (t : ℂ)) ≠ 0) :
    HasDerivAt
      (fun u : ℝ => Real.log ‖f ((sigma : ℂ) + I * (u : ℂ))‖)
      (-(logDeriv f ((sigma : ℂ) + I * (t : ℂ))).im) t := by
  let s : ℂ := (sigma : ℂ) + I * (t : ℂ)
  have hparam :
      HasDerivAt (fun z : ℂ => (sigma : ℂ) + I * z) I (t : ℂ) := by
    simpa using
      ((hasDerivAt_id (t : ℂ)).const_mul I).const_add (sigma : ℂ)
  have hcompComplex :
      HasDerivAt (fun z : ℂ => f ((sigma : ℂ) + I * z))
        (deriv f s * I) (t : ℂ) := by
    simpa [s] using hf.differentiableAt.hasDerivAt.comp (t : ℂ) hparam
  have hvertical :
      HasDerivAt (fun u : ℝ => f ((sigma : ℂ) + I * (u : ℂ)))
        (deriv f s * I) t := by
    simpa using hcompComplex.comp_ofReal
  have hnormSq := hvertical.norm_sq
  have hnormSqNe : ‖f s‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (by simpa [s] using hne))
  have hlogNormSq := hnormSq.log hnormSqNe
  have hhalf := hlogNormSq.const_mul (2 : ℝ)⁻¹
  convert hhalf using 1
  · funext u
    rw [Real.log_pow]
    ring
  · rw [logDeriv_apply, hf.differentiableAt.hasDerivAt.deriv]
    simp only [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.div_im,
      Complex.normSq_eq_norm_sq]
    field_simp
    ring

/-- Integration by parts on a vertical edge.  This converts the imaginary
part of the logarithmic derivative into endpoint and `log ‖f‖` terms. -/
theorem intervalIntegral_mul_neg_im_logDeriv_vertical_eq
    {f : ℂ → ℂ} {sigma a b : ℝ}
    (hf : ∀ u ∈ [[a, b]],
      AnalyticAt ℂ f ((sigma : ℂ) + I * (u : ℂ)))
    (hne : ∀ u ∈ [[a, b]],
      f ((sigma : ℂ) + I * (u : ℂ)) ≠ 0)
    (hint : IntervalIntegrable
      (fun u : ℝ => -(logDeriv f ((sigma : ℂ) + I * (u : ℂ))).im)
      MeasureTheory.volume a b) :
    (∫ u in a..b,
        u * (-(logDeriv f ((sigma : ℂ) + I * (u : ℂ))).im)) =
      b * Real.log ‖f ((sigma : ℂ) + I * (b : ℂ))‖ -
        a * Real.log ‖f ((sigma : ℂ) + I * (a : ℂ))‖ -
          ∫ u in a..b,
            Real.log ‖f ((sigma : ℂ) + I * (u : ℂ))‖ := by
  simpa only [one_mul] using
    (intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun u : ℝ => u)
      (v := fun u : ℝ => Real.log ‖f ((sigma : ℂ) + I * (u : ℂ))‖)
      (u' := fun _ : ℝ => 1)
      (v' := fun u : ℝ =>
        -(logDeriv f ((sigma : ℂ) + I * (u : ℂ))).im)
      (fun u _ => hasDerivAt_id u)
      (fun u hu => hasDerivAt_log_norm_vertical (hf u hu) (hne u hu))
      intervalIntegrable_const hint)

/-- Weighted argument-principle identity on an axis-parallel rectangle.

The hypotheses identify all zeros in the closed rectangle and supply their
analytic multiplicities.  Strict interior containment excludes boundary
zeros.  Removing the finite logarithmic principal parts gives an analytic
remainder, so the weighted rectangle residue formula applies without any
simple-zero assumption. -/
theorem boundaryRectIntegral_weighted_logDeriv_eq_zeroMultiplicitySum
    {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (poles : Finset ℂ) (multiplicity : ℂ → ℕ) (anchor : ℂ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ),
      f z = 0 ↔ z ∈ poles)
    (horder : ∀ rho ∈ poles,
      analyticOrderAt f rho = multiplicity rho)
    (hpoles : ∀ rho ∈ poles,
      x0 < rho.re ∧ rho.re < x1 ∧ y0 < rho.im ∧ rho.im < y1) :
    MathlibAux.boundaryRectIntegral
        (fun z : ℂ => (z - anchor) * logDeriv f z)
        x0 x1 y0 y1 =
      (2 * Real.pi * I) *
        ∑ rho ∈ poles, (rho - anchor) * (multiplicity rho : ℂ) := by
  classical
  let U : Set ℂ := [[x0, x1]] ×ℂ [[y0, y1]]
  let raw : ℂ → ℂ := fun z =>
    logDeriv f z -
      ∑ rho ∈ poles, (multiplicity rho : ℂ) * (z - rho)⁻¹
  let regular : ℂ → ℂ := toMeromorphicNFOn raw U
  have hfU : AnalyticOnNhd ℂ f U := by
    simpa [U] using hf
  have hzeroU : ∀ z ∈ U, f z = 0 ↔ z ∈ poles := by
    simpa [U] using hzero
  have hrawMeromorphic : MeromorphicOn raw U := by
    simpa [raw] using
      ZeroFreeRegion.meromorphicOn_logDeriv_sub_finset_principalParts
        hfU.meromorphicOn poles multiplicity
  have hregular : AnalyticOnNhd ℂ regular U := by
    dsimp [regular]
    exact
      ZeroFreeRegion.analyticOnNhd_toMeromorphicNFOn_logDeriv_sub_finset_principalParts
        hfU poles multiplicity hzeroU horder
  have hboundaryNonzero : ∀ z ∈ U,
      ¬(x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) →
        f z ≠ 0 := by
    intro z hz hnot hzeroz
    exact hnot (hpoles z ((hzeroU z hz).mp hzeroz))
  have hrawAnalyticBoundary : ∀ z ∈ U,
      ¬(x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) →
        AnalyticAt ℂ raw z := by
    intro z hz hnot
    have hlog : AnalyticAt ℂ (logDeriv f) z :=
      (hfU z hz).deriv.div (hfU z hz) (hboundaryNonzero z hz hnot)
    have hsum : AnalyticAt ℂ
        (fun w : ℂ =>
          ∑ rho ∈ poles, (multiplicity rho : ℂ) * (w - rho)⁻¹) z := by
      apply Finset.analyticAt_fun_sum
      intro rho hrho
      have hzr : z ≠ rho := by
        intro heq
        subst z
        exact hnot (hpoles rho hrho)
      exact analyticAt_const.mul
        ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hzr))
    simpa [raw] using hlog.sub hsum
  have hregularEqBoundary : ∀ z ∈ U,
      ¬(x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) →
        regular z = raw z := by
    intro z hz hnot
    dsimp [regular]
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hrawMeromorphic hz]
    rw [toMeromorphicNFAt_eq_self.2
      (hrawAnalyticBoundary z hz hnot).meromorphicNFAt]
  have hcontour :
      MathlibAux.boundaryRectIntegral
          (fun z : ℂ => (z - anchor) * logDeriv f z)
          x0 x1 y0 y1 =
        MathlibAux.boundaryRectIntegral
          (fun z : ℂ =>
            (z - anchor) *
              (regular z +
                ∑ rho ∈ poles,
                  (z - rho)⁻¹ * (multiplicity rho : ℂ)))
          x0 x1 y0 y1 := by
    apply MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
    intro z hz hnot
    have hzU : z ∈ U := by simpa [U] using hz
    rw [hregularEqBoundary z hzU hnot]
    dsimp [raw]
    have hsumComm :
        (∑ rho ∈ poles,
            (multiplicity rho : ℂ) * (z - rho)⁻¹) =
          ∑ rho ∈ poles,
            (z - rho)⁻¹ * (multiplicity rho : ℂ) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      ring
    rw [hsumComm]
    ring
  rw [hcontour]
  exact
    MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_weighted_residue_sum_of_differentiableOn
      poles (fun rho => (multiplicity rho : ℂ)) anchor
      hregular.differentiableOn hpoles

end CarlsonZeroDensity
end PrimeNumberTheorem
