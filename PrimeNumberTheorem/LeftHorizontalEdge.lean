import PrimeNumberTheorem.RightHorizontalEdge
import PrimeNumberTheorem.DigammaBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

open Complex Filter Topology

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

private theorem normSq_sin_ofReal_add_mul_I (x y : ℝ) :
    Complex.normSq (Complex.sin ((x : ℂ) + (y : ℂ) * I)) =
      Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.sin_add_mul_I]
  simp [Complex.normSq_apply, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
    Complex.sinh_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im, sq]
  nlinarith [Real.sin_sq_add_cos_sq x, Real.cosh_sq_sub_sinh_sq y]

private theorem normSq_cos_ofReal_add_mul_I (x y : ℝ) :
    Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * I)) =
      Real.cos x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.cos_add_mul_I]
  simp [Complex.normSq_apply, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sinh_ofReal_re,
    Complex.sinh_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im, sq]
  nlinarith [Real.sin_sq_add_cos_sq x, Real.cosh_sq_sub_sinh_sq y]

/-- Complex tangent is uniformly bounded away from the real axis.  The
constant `2` is deliberately coarse but sufficient for contour decay. -/
theorem norm_tan_le_two_of_one_le_abs_im {z : ℂ} (hz : 1 ≤ |z.im|) :
    ‖Complex.tan z‖ ≤ 2 := by
  let x : ℝ := z.re
  let y : ℝ := z.im
  have hzxy : z = (x : ℂ) + (y : ℂ) * I := by
    exact (Complex.re_add_im z).symm
  have hsinh1 : 1 ≤ |Real.sinh y| := by
    rw [Real.abs_sinh]
    exact (Real.self_lt_sinh_iff.mpr zero_lt_one).le.trans
      (Real.sinh_le_sinh.mpr hz)
  have hsinhSq : 1 ≤ Real.sinh y ^ 2 := by
    rw [← sq_abs]
    have hsquare := (sq_le_sq₀ zero_le_one (abs_nonneg _)).2 hsinh1
    norm_num at hsquare ⊢
    exact hsquare
  have hsinSq := normSq_sin_ofReal_add_mul_I x y
  have hcosSq := normSq_cos_ofReal_add_mul_I x y
  rw [Complex.tan_eq_sin_div_cos, norm_div]
  apply (sq_le_sq₀ (div_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)).1
  rw [div_pow, Complex.sq_norm, Complex.sq_norm]
  rw [hzxy, hsinSq, hcosSq]
  have hsin : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
  have hcos : 0 ≤ Real.cos x ^ 2 := sq_nonneg _
  have hden : 0 < Real.cos x ^ 2 + Real.sinh y ^ 2 := by nlinarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- Complex cotangent has the same coarse high-imaginary-part bound. -/
theorem norm_cot_le_two_of_one_le_abs_im {z : ℂ} (hz : 1 ≤ |z.im|) :
    ‖Complex.cot z‖ ≤ 2 := by
  let x : ℝ := z.re
  let y : ℝ := z.im
  have hzxy : z = (x : ℂ) + (y : ℂ) * I := by
    exact (Complex.re_add_im z).symm
  have hsinh1 : 1 ≤ |Real.sinh y| := by
    rw [Real.abs_sinh]
    exact (Real.self_lt_sinh_iff.mpr zero_lt_one).le.trans
      (Real.sinh_le_sinh.mpr hz)
  have hsinhSq : 1 ≤ Real.sinh y ^ 2 := by
    rw [← sq_abs]
    have hsquare := (sq_le_sq₀ zero_le_one (abs_nonneg _)).2 hsinh1
    norm_num at hsquare ⊢
    exact hsquare
  have hsinSq := normSq_sin_ofReal_add_mul_I x y
  have hcosSq := normSq_cos_ofReal_add_mul_I x y
  rw [Complex.cot_eq_cos_div_sin, norm_div]
  apply (sq_le_sq₀ (div_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)).1
  rw [div_pow, Complex.sq_norm, Complex.sq_norm]
  rw [hzxy, hsinSq, hcosSq]
  have hcos : Real.cos x ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.sin x)]
  have hsin : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
  have hden : 0 < Real.sin x ^ 2 + Real.sinh y ^ 2 := by nlinarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- Logarithmic-derivative form of Euler's Gamma reflection formula, valid
off the real axis. -/
theorem digamma_eq_one_sub_sub_pi_mul_cot {s : ℂ} (hs : s.im ≠ 0) :
    Complex.digamma s = Complex.digamma (1 - s) -
      Real.pi * Complex.cot (Real.pi * s) := by
  have hsGamma : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hn
    apply hs
    have him := congrArg Complex.im hn
    simpa using him
  have h1sGamma : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := by
    intro n hn
    apply hs
    have him := congrArg Complex.im hn
    simp at him
    exact him
  have hGamma : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hsGamma
  have hGamma1 : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero h1sGamma
  have hsin : Complex.sin (Real.pi * s) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    apply hs
    have him := congrArg Complex.im hk
    simp at him
    exact him
  have hGdiff : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s hsGamma
  have hG1diff : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (1 - z)) s := by
    exact (Complex.differentiableAt_Gamma (1 - s) h1sGamma).comp s (by fun_prop)
  have hsinDiff : DifferentiableAt ℂ
      (fun z : ℂ => Complex.sin (Real.pi * z)) s := by fun_prop
  have hlhs :
      logDeriv (fun z : ℂ => Complex.Gamma z * Complex.Gamma (1 - z)) s =
        Complex.digamma s - Complex.digamma (1 - s) := by
    rw [logDeriv_mul s hGamma hGamma1 hGdiff hG1diff]
    have hcomp :
        logDeriv (fun z : ℂ => Complex.Gamma (1 - z)) s =
          -logDeriv Complex.Gamma (1 - s) := by
      change logDeriv (Complex.Gamma ∘ fun z : ℂ => 1 - z) s = _
      rw [logDeriv_comp (Complex.differentiableAt_Gamma (1 - s) h1sGamma)
        (by fun_prop)]
      rw [show deriv (fun z : ℂ => 1 - z) s = -1 by
        convert ((hasDerivAt_const s 1).sub (hasDerivAt_id s)).deriv using 1
        all_goals simp]
      ring
    rw [hcomp]
    rfl
  have hrhs :
      logDeriv (fun z : ℂ => (Real.pi : ℂ) /
          Complex.sin (Real.pi * z)) s =
        -(Real.pi : ℂ) * Complex.cot (Real.pi * s) := by
    rw [logDeriv_div s (ofReal_ne_zero.mpr Real.pi_ne_zero) hsin
      (differentiableAt_const _) hsinDiff]
    rw [logDeriv_const]
    have hcomp :
        logDeriv (fun z : ℂ => Complex.sin (Real.pi * z)) s =
          (Real.pi : ℂ) * Complex.cot (Real.pi * s) := by
      change logDeriv (Complex.sin ∘ fun z : ℂ => Real.pi * z) s = _
      rw [logDeriv_comp Complex.differentiableAt_sin (by fun_prop),
        Complex.logDeriv_sin]
      rw [show deriv (fun z : ℂ => Real.pi * z) s = (Real.pi : ℂ) by
        convert ((hasDerivAt_id s).const_mul (Real.pi : ℂ)).deriv using 1
        all_goals simp]
      ring
    rw [hcomp]
    simp
  have hreflection :
      (fun z : ℂ => Complex.Gamma z * Complex.Gamma (1 - z)) =
        fun z : ℂ => (Real.pi : ℂ) / Complex.sin (Real.pi * z) := by
    funext z
    exact Complex.Gamma_mul_Gamma_one_sub z
  rw [hreflection, hrhs] at hlhs
  linear_combination -hlhs

/-- Logarithmic derivative form of the zeta functional equation, oriented so
that a point on the left is related to `1 - s` in the Euler-product
half-plane. -/
theorem logDeriv_riemannZeta_eq_left_shift {s : ℂ}
    (hsGamma : ∀ n : ℕ, s ≠ -(n : ℂ)) (hs1 : s ≠ 1)
    (hzs : riemannZeta s ≠ 0) (hz1s : riemannZeta (1 - s) ≠ 0) :
    logDeriv riemannZeta s =
      -logDeriv riemannZeta (1 - s) + Complex.log (2 * Real.pi) -
        Complex.digamma s + (Real.pi / 2 : ℂ) * Complex.tan (Real.pi * s / 2) := by
  have hs0 : s ≠ 0 := by simpa using hsGamma 0
  have hGamma : Gamma s ≠ 0 := Gamma_ne_zero hsGamma
  have hbase : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpow : ((2 * (Real.pi : ℂ)) ^ (-s)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
  have hcos : Complex.cos (Real.pi * s / 2) ≠ 0 := by
    intro hzero
    apply hz1s
    rw [riemannZeta_one_sub hsGamma hs1, hzero, mul_zero, zero_mul]
  let A : ℂ → ℂ := fun z => (2 * (Real.pi : ℂ)) ^ (-z)
  let C : ℂ → ℂ := fun z => Complex.cos (Real.pi * z / 2)
  let F : ℂ → ℂ := fun z =>
    2 * A z * Gamma z * C z * riemannZeta z
  have hAdiff : DifferentiableAt ℂ A s := by
    dsimp [A]
    exact (hasDerivAt_neg s).const_cpow (Or.inl hbase) |>.differentiableAt
  have hCdiff : DifferentiableAt ℂ C s := by
    dsimp [C]
    fun_prop
  have hZdiff : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs1
  have hFE : (fun z : ℂ => riemannZeta (1 - z)) =ᶠ[𝓝 s] F := by
    have hGammaEventually : ∀ᶠ z : ℂ in 𝓝 s, Gamma z ≠ 0 :=
      (differentiableAt_Gamma s hsGamma).continuousAt.eventually_ne hGamma
    filter_upwards [hGammaEventually, eventually_ne_nhds hs1] with z hzGamma hz1
    dsimp [F, A, C]
    rw [riemannZeta_one_sub (fun n hn =>
      hzGamma ((Gamma_eq_zero_iff z).2 ⟨n, hn⟩)) hz1]
  have hlogFE : logDeriv (fun z : ℂ => riemannZeta (1 - z)) s = logDeriv F s := by
    simp only [logDeriv_apply]
    rw [hFE.deriv_eq]
    congr 1
    exact hFE.self_of_nhds
  have hlhs : logDeriv (fun z : ℂ => riemannZeta (1 - z)) s =
      -logDeriv riemannZeta (1 - s) := by
    have h1s1 : 1 - s ≠ 1 := by
      intro h
      apply hs0
      calc
        s = 1 - (1 - s) := by ring
        _ = 0 := by rw [h]; ring
    change logDeriv (riemannZeta ∘ fun z : ℂ => 1 - z) s = _
    rw [logDeriv_comp (differentiableAt_riemannZeta h1s1) (by fun_prop)]
    rw [show deriv (fun z : ℂ => 1 - z) s = -1 by
      convert ((hasDerivAt_const s 1).sub (hasDerivAt_id s)).deriv using 1
      all_goals simp]
    ring
  have hAlog : logDeriv A s = -Complex.log (2 * Real.pi) := by
    simp only [A, logDeriv_apply]
    rw [Complex.deriv_const_cpow (hasDerivAt_neg s).differentiableAt]
    rw [show deriv (fun z : ℂ => -z) s = -1 by
      exact (hasDerivAt_neg s).deriv]
    field_simp
  have hClog : logDeriv C s =
      -(Real.pi / 2 : ℂ) * Complex.tan (Real.pi * s / 2) := by
    change logDeriv (Complex.cos ∘ fun z : ℂ => Real.pi * z / 2) s = _
    rw [logDeriv_comp Complex.differentiableAt_cos (by fun_prop), Complex.logDeriv_cos]
    rw [show deriv (fun z : ℂ => Real.pi * z / 2) s = (Real.pi : ℂ) / 2 by
      convert (((hasDerivAt_id s).const_mul (Real.pi : ℂ)).div_const 2).deriv using 1
      all_goals simp]
    simp only [Pi.neg_apply]
    ring
  have hFlog : logDeriv F s =
      -Complex.log (2 * Real.pi) + Complex.digamma s -
        (Real.pi / 2 : ℂ) * Complex.tan (Real.pi * s / 2) +
          logDeriv riemannZeta s := by
    have h2A : (2 : ℂ) * A s ≠ 0 := mul_ne_zero (by norm_num) hpow
    have h2AG : (2 : ℂ) * A s * Gamma s ≠ 0 := mul_ne_zero h2A hGamma
    have h2AGC : (2 : ℂ) * A s * Gamma s * C s ≠ 0 := mul_ne_zero h2AG hcos
    have h2Adiff : DifferentiableAt ℂ (fun z => (2 : ℂ) * A z) s :=
      differentiableAt_const (c := (2 : ℂ)).mul hAdiff
    have h2AGdiff : DifferentiableAt ℂ (fun z => (2 : ℂ) * A z * Gamma z) s :=
      h2Adiff.mul (differentiableAt_Gamma s hsGamma)
    have h2AGCdiff : DifferentiableAt ℂ
        (fun z => (2 : ℂ) * A z * Gamma z * C z) s :=
      h2AGdiff.mul hCdiff
    dsimp [F]
    rw [logDeriv_mul s h2AGC hzs h2AGCdiff hZdiff,
      logDeriv_mul s h2AG hcos h2AGdiff hCdiff,
      logDeriv_mul s h2A hGamma h2Adiff (differentiableAt_Gamma s hsGamma),
      logDeriv_const_mul s (2 : ℂ) (by norm_num), hAlog, digamma_def, hClog]
    ring
  rw [hlhs, hFlog] at hlogFE
  linear_combination -hlogFE

/-- The part of the far-left explicit-formula integrand coming from the
Archimedean factor in the zeta functional equation. -/
noncomputable def farLeftGammaFactorIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  (Complex.digamma s - Complex.log (2 * Real.pi) -
      (Real.pi / 2 : ℂ) * Complex.tan (Real.pi * s / 2)) *
    (x : ℂ) ^ s / s

/-- The genuinely non-elementary part of the far-left Archimedean factor. -/
noncomputable def farLeftDigammaIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  Complex.digamma s * (x : ℂ) ^ s / s

/-- The digamma term after reflection into the right half-plane. -/
noncomputable def farLeftRightShiftedDigammaIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  Complex.digamma (1 - s) * (x : ℂ) ^ s / s

/-- The cotangent correction introduced by the digamma reflection formula. -/
noncomputable def farLeftCotCorrectionIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  (-(Real.pi : ℂ) * Complex.cot (Real.pi * s)) * (x : ℂ) ^ s / s

theorem farLeftDigammaIntegrand_eq_rightShifted_add_cot
    {x : ℝ} {s : ℂ} (hs : s.im ≠ 0) :
    farLeftDigammaIntegrand x s =
      farLeftRightShiftedDigammaIntegrand x s +
        farLeftCotCorrectionIntegrand x s := by
  simp only [farLeftDigammaIntegrand, farLeftRightShiftedDigammaIntegrand,
    farLeftCotCorrectionIntegrand]
  rw [digamma_eq_one_sub_sub_pi_mul_cot hs]
  ring

/-- The elementary constant and tangent terms in the far-left Archimedean
factor. -/
noncomputable def farLeftElementaryGammaIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  (-Complex.log (2 * Real.pi) -
      (Real.pi / 2 : ℂ) * Complex.tan (Real.pi * s / 2)) *
    (x : ℂ) ^ s / s

theorem farLeftGammaFactorIntegrand_eq_digamma_add_elementary
    (x : ℝ) (s : ℂ) :
    farLeftGammaFactorIntegrand x s =
      farLeftDigammaIntegrand x s + farLeftElementaryGammaIntegrand x s := by
  simp only [farLeftGammaFactorIntegrand, farLeftDigammaIntegrand,
    farLeftElementaryGammaIntegrand]
  ring

/-- On a nonreal point in the far-left half-plane, the complete first-order
integrand is exactly the sum of an Euler-product term and the Archimedean
Gamma-factor term. -/
theorem explicitFormulaIntegrand_eq_farLeft_euler_add_gamma
    {x ε σ T : ℝ} (hε : 0 < ε) (hσ : σ ≤ -ε) (hT : T ≠ 0) :
    explicitFormulaIntegrand x ((σ : ℂ) + T * I) =
      logDeriv riemannZeta (1 - ((σ : ℂ) + T * I)) *
          (x : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I) +
        farLeftGammaFactorIntegrand x ((σ : ℂ) + T * I) := by
  let s : ℂ := (σ : ℂ) + T * I
  have hsGamma : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hn
    apply hT
    have him := congrArg Complex.im hn
    simpa [s] using him
  have hs1 : s ≠ 1 := by
    intro hs
    apply hT
    have him := congrArg Complex.im hs
    simpa [s] using him
  have htrivial : ∀ n : ℕ, s ≠ -2 * ((n : ℂ) + 1) := by
    intro n hn
    apply hT
    have him := congrArg Complex.im hn
    simpa [s] using him
  have hzs : riemannZeta s ≠ 0 :=
    PrimeNumberTheorem.riemannZeta_ne_zero_of_re_le_zero
      (show s.re ≤ 0 by
        have hσ0 : σ ≤ 0 := by linarith [hσ]
        simpa [s] using hσ0) htrivial
  have hz1s : riemannZeta (1 - s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re
      (show 1 ≤ (1 - s).re by simp [s]; linarith)
  have hlog := logDeriv_riemannZeta_eq_left_shift hsGamma hs1 hzs hz1s
  change explicitFormulaIntegrand x s = _
  simp only [explicitFormulaIntegrand, farLeftGammaFactorIntegrand]
  rw [hlog]
  ring

private theorem intervalIntegrable_farLeft_explicit
    {x ε a T : ℝ} (hx : 1 < x) (hε : 0 < ε)
    (ha : a ≤ -ε) (hT : T ≠ 0) :
    IntervalIntegrable
      (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + T * I))
      MeasureTheory.volume a (-ε) := by
  apply ContinuousOn.intervalIntegrable
  intro σ hσ
  rw [Set.uIcc_of_le ha] at hσ
  let s : ℂ := (σ : ℂ) + T * I
  have hs0 : s ≠ 0 := by
    intro hs
    apply hT
    have him := congrArg Complex.im hs
    simpa [s] using him
  have hs1 : s ≠ 1 := by
    intro hs
    apply hT
    have him := congrArg Complex.im hs
    simpa [s] using him
  have htrivial : ∀ n : ℕ, s ≠ -2 * ((n : ℂ) + 1) := by
    intro n hn
    apply hT
    have him := congrArg Complex.im hn
    simpa [s] using him
  have hzs : riemannZeta s ≠ 0 :=
    PrimeNumberTheorem.riemannZeta_ne_zero_of_re_le_zero
      (show s.re ≤ 0 by
        have hσ0 : σ ≤ 0 := by linarith [hσ.2]
        simpa [s] using hσ0) htrivial
  have hmap : ContinuousAt (fun u : ℝ => (u : ℂ) + T * I) σ := by fun_prop
  have han := analyticAt_explicitFormulaIntegrand_of_ne_zero_of_ne_one_of_zeta_ne_zero
    (zero_lt_one.trans hx) hs0 hs1 hzs
  simpa [s, Function.comp_def] using
    (han.continuousAt.comp_of_eq hmap (by simp [s])).continuousWithinAt

private theorem intervalIntegrable_farLeft_eulerFactor
    {x ε a T : ℝ} (hx : 1 < x) (hε : 0 < ε)
    (ha : a ≤ -ε) (hT : T ≠ 0) :
    IntervalIntegrable
      (fun σ : ℝ =>
        logDeriv riemannZeta (1 - ((σ : ℂ) + T * I)) *
          (x : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I))
      MeasureTheory.volume a (-ε) := by
  apply ContinuousOn.intervalIntegrable
  intro σ hσ
  rw [Set.uIcc_of_le ha] at hσ
  let s : ℂ := (σ : ℂ) + T * I
  let u : ℂ := 1 - s
  have hs0 : s ≠ 0 := by
    intro hs
    apply hT
    have him := congrArg Complex.im hs
    simpa [s] using him
  have hu1 : u ≠ 1 := by
    intro hu
    apply hs0
    calc
      s = 1 - (1 - s) := by ring
      _ = 0 := by simpa [u] using congrArg (fun z : ℂ => 1 - z) hu
  have hzu : riemannZeta u ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re
      (show 1 ≤ u.re by simp [u, s]; linarith [hσ.2])
  have hmap : ContinuousAt (fun v : ℝ => (v : ℂ) + T * I) σ := by fun_prop
  have humap : ContinuousAt (fun v : ℝ => 1 - ((v : ℂ) + T * I)) σ := by fun_prop
  have hlog : ContinuousAt
      (fun v : ℝ => logDeriv riemannZeta (1 - ((v : ℂ) + T * I))) σ := by
    simpa [u, s, Function.comp_def] using
      ((ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
        u hu1 hzu).continuousAt.comp_of_eq humap (by simp [u, s]))
  have hpowBase : ContinuousAt (fun z : ℂ => (x : ℂ) ^ z) s :=
    (((differentiableAt_id : DifferentiableAt ℂ (fun z : ℂ => z) s).const_cpow
      (Or.inl (ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans hx))))).continuousAt)
  have hpow : ContinuousAt
      (fun v : ℝ => (x : ℂ) ^ ((v : ℂ) + T * I)) σ := by
    simpa [s, Function.comp_def] using hpowBase.comp_of_eq hmap (by simp [s])
  have hquot := (hlog.mul hpow).div hmap hs0
  simpa [s] using hquot.continuousWithinAt

/-- On a finite far-left horizontal segment, subtracting the Archimedean
Gamma-factor integral from the full explicit-formula integral leaves exactly
the Euler-product integral. -/
theorem integral_farLeft_explicit_sub_gamma_eq_euler
    {x ε a T : ℝ} (hx : 1 < x) (hε : 0 < ε)
    (ha : a ≤ -ε) (hT : T ≠ 0) :
    (∫ σ : ℝ in a..(-ε), explicitFormulaIntegrand x ((σ : ℂ) + T * I)) -
        (∫ σ : ℝ in a..(-ε),
          farLeftGammaFactorIntegrand x ((σ : ℂ) + T * I)) =
      ∫ σ : ℝ in a..(-ε),
        logDeriv riemannZeta (1 - ((σ : ℂ) + T * I)) *
          (x : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I) := by
  let full : ℝ → ℂ := fun σ =>
    explicitFormulaIntegrand x ((σ : ℂ) + T * I)
  let euler : ℝ → ℂ := fun σ =>
    logDeriv riemannZeta (1 - ((σ : ℂ) + T * I)) *
      (x : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I)
  let gamma : ℝ → ℂ := fun σ =>
    farLeftGammaFactorIntegrand x ((σ : ℂ) + T * I)
  have hfull : IntervalIntegrable full MeasureTheory.volume a (-ε) := by
    simpa [full] using intervalIntegrable_farLeft_explicit hx hε ha hT
  have heuler : IntervalIntegrable euler MeasureTheory.volume a (-ε) := by
    simpa [euler] using intervalIntegrable_farLeft_eulerFactor hx hε ha hT
  have hsplit : Set.EqOn full (fun σ => euler σ + gamma σ) (Set.uIcc a (-ε)) := by
    intro σ hσ
    rw [Set.uIcc_of_le ha] at hσ
    exact explicitFormulaIntegrand_eq_farLeft_euler_add_gamma hε hσ.2 hT
  have hgamma : IntervalIntegrable gamma MeasureTheory.volume a (-ε) := by
    apply (hfull.sub heuler).congr
    intro σ hσ
    have hs := hsplit (Set.uIoc_subset_uIcc hσ)
    dsimp [full, euler, gamma] at hs ⊢
    linear_combination hs
  have hcongr := intervalIntegral.integral_congr (μ := MeasureTheory.volume) hsplit
  rw [intervalIntegral.integral_add heuler hgamma] at hcongr
  dsimp [full, euler, gamma] at hcongr ⊢
  linear_combination hcongr

private theorem intervalIntegrable_farLeft_gammaFactor
    {x ε a T : ℝ} (hx : 1 < x) (hε : 0 < ε)
    (ha : a ≤ -ε) (hT : T ≠ 0) :
    IntervalIntegrable
      (fun σ : ℝ => farLeftGammaFactorIntegrand x ((σ : ℂ) + T * I))
      MeasureTheory.volume a (-ε) := by
  have hfull := intervalIntegrable_farLeft_explicit hx hε ha hT
  have heuler := intervalIntegrable_farLeft_eulerFactor hx hε ha hT
  apply (hfull.sub heuler).congr
  intro σ hσ
  have hσ' := Set.uIoc_subset_uIcc hσ
  rw [Set.uIcc_of_le ha] at hσ'
  have hsplit := explicitFormulaIntegrand_eq_farLeft_euler_add_gamma
    (x := x) hε hσ'.2 hT
  linear_combination hsplit

private theorem intervalIntegrable_farLeft_elementaryGamma
    {x ε a T : ℝ} (hx : 1 < x) (hT : T ≠ 0) :
    IntervalIntegrable
      (fun σ : ℝ => farLeftElementaryGammaIntegrand x ((σ : ℂ) + T * I))
      MeasureTheory.volume a (-ε) := by
  apply ContinuousOn.intervalIntegrable
  intro σ _hσ
  let s : ℂ := (σ : ℂ) + T * I
  let q : ℂ := Real.pi * s / 2
  have hs0 : s ≠ 0 := by
    intro hs
    apply hT
    have him := congrArg Complex.im hs
    simpa [s] using him
  have hqim : q.im ≠ 0 := by
    intro hzero
    apply hT
    have him : q.im = Real.pi * T / 2 := by
      dsimp [q]
      rw [show (Real.pi : ℂ) * s / 2 = ((Real.pi / 2 : ℝ) : ℂ) * s by
        push_cast
        ring]
      simp [s]
      ring
    rw [him] at hzero
    norm_num at hzero
    exact hzero
  have hcos : Complex.cos q ≠ 0 := by
    intro hzero
    rcases Complex.cos_eq_zero_iff.mp hzero with ⟨k, hk⟩
    apply hqim
    have him := congrArg Complex.im hk
    simpa using him
  have hmap : ContinuousAt (fun u : ℝ => (u : ℂ) + T * I) σ := by fun_prop
  have hqmap : ContinuousAt
      (fun u : ℝ => Real.pi * ((u : ℂ) + T * I) / 2) σ := by fun_prop
  have htan : ContinuousAt
      (fun u : ℝ => Complex.tan (Real.pi * ((u : ℂ) + T * I) / 2)) σ := by
    simpa [q, s, Function.comp_def] using
      (Complex.continuousAt_tan.mpr hcos).comp_of_eq hqmap (by simp [q, s])
  have hpowBase : ContinuousAt (fun z : ℂ => (x : ℂ) ^ z) s :=
    (((differentiableAt_id : DifferentiableAt ℂ (fun z : ℂ => z) s).const_cpow
      (Or.inl (ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans hx))))).continuousAt)
  have hpow : ContinuousAt
      (fun u : ℝ => (x : ℂ) ^ ((u : ℂ) + T * I)) σ := by
    simpa [s, Function.comp_def] using hpowBase.comp_of_eq hmap (by simp [s])
  have hcoeff : ContinuousAt
      (fun u : ℝ => -Complex.log (2 * Real.pi) -
        (Real.pi / 2 : ℂ) *
          Complex.tan (Real.pi * ((u : ℂ) + T * I) / 2)) σ := by fun_prop
  have hquot := (hcoeff.mul hpow).div hmap hs0
  simpa [farLeftElementaryGammaIntegrand, s] using hquot.continuousWithinAt

private theorem intervalIntegrable_farLeft_digamma
    {x ε a T : ℝ} (hx : 1 < x) (hε : 0 < ε)
    (ha : a ≤ -ε) (hT : T ≠ 0) :
    IntervalIntegrable
      (fun σ : ℝ => farLeftDigammaIntegrand x ((σ : ℂ) + T * I))
      MeasureTheory.volume a (-ε) := by
  have hgamma := intervalIntegrable_farLeft_gammaFactor hx hε ha hT
  have helem := intervalIntegrable_farLeft_elementaryGamma
    (a := a) (ε := ε) hx hT
  apply (hgamma.sub helem).congr
  intro σ _hσ
  have hsplit := farLeftGammaFactorIntegrand_eq_digamma_add_elementary
    x ((σ : ℂ) + T * I)
  linear_combination hsplit

private theorem intervalIntegrable_farLeft_cotCorrection
    {x ε a T : ℝ} (hx : 1 < x) (hT : T ≠ 0) :
    IntervalIntegrable
      (fun σ : ℝ => farLeftCotCorrectionIntegrand x ((σ : ℂ) + T * I))
      MeasureTheory.volume a (-ε) := by
  apply ContinuousOn.intervalIntegrable
  intro σ _hσ
  let s : ℂ := (σ : ℂ) + T * I
  let q : ℂ := Real.pi * s
  have hs0 : s ≠ 0 := by
    intro hs
    apply hT
    have him := congrArg Complex.im hs
    simpa [s] using him
  have hqim : q.im ≠ 0 := by
    dsimp [q, s]
    simp [Real.pi_ne_zero, hT]
  have hsin : Complex.sin q ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    apply hqim
    have him := congrArg Complex.im hk
    simpa using him
  have hmap : ContinuousAt (fun u : ℝ => (u : ℂ) + T * I) σ := by fun_prop
  have hqmap : ContinuousAt
      (fun u : ℝ => Real.pi * ((u : ℂ) + T * I)) σ := by fun_prop
  have hcot : ContinuousAt
      (fun u : ℝ => Complex.cot (Real.pi * ((u : ℂ) + T * I))) σ := by
    rw [show (fun u : ℝ => Complex.cot (Real.pi * ((u : ℂ) + T * I))) =
        fun u : ℝ => Complex.cos (Real.pi * ((u : ℂ) + T * I)) /
          Complex.sin (Real.pi * ((u : ℂ) + T * I)) by
      funext u
      rw [Complex.cot_eq_cos_div_sin]]
    simpa [Function.comp_def] using
      (Complex.differentiableAt_cos.continuousAt.comp hqmap).div
        (Complex.differentiableAt_sin.continuousAt.comp hqmap)
        (by simpa [q, s] using hsin)
  have hpowBase : ContinuousAt (fun z : ℂ => (x : ℂ) ^ z) s :=
    (((differentiableAt_id : DifferentiableAt ℂ (fun z : ℂ => z) s).const_cpow
      (Or.inl (ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans hx))))).continuousAt)
  have hpow : ContinuousAt
      (fun u : ℝ => (x : ℂ) ^ ((u : ℂ) + T * I)) σ := by
    simpa [s, Function.comp_def] using hpowBase.comp_of_eq hmap (by simp [s])
  have hcoeff : ContinuousAt
      (fun u : ℝ => -(Real.pi : ℂ) *
        Complex.cot (Real.pi * ((u : ℂ) + T * I))) σ := by fun_prop
  have hquot := (hcoeff.mul hpow).div hmap hs0
  exact hquot.continuousWithinAt

private theorem intervalIntegrable_farLeft_rightShiftedDigamma
    {x ε a T : ℝ} (hx : 1 < x) (hε : 0 < ε)
    (ha : a ≤ -ε) (hT : T ≠ 0) :
    IntervalIntegrable
      (fun σ : ℝ =>
        farLeftRightShiftedDigammaIntegrand x ((σ : ℂ) + T * I))
      MeasureTheory.volume a (-ε) := by
  have hdig := intervalIntegrable_farLeft_digamma hx hε ha hT
  have hcot := intervalIntegrable_farLeft_cotCorrection
    (a := a) (ε := ε) hx hT
  apply (hdig.sub hcot).congr
  intro σ _hσ
  have hsplit := farLeftDigammaIntegrand_eq_rightShifted_add_cot
    (x := x) (s := (σ : ℂ) + T * I) (by simpa using hT)
  linear_combination hsplit

/-- Reflection of digamma gives an exact finite-segment integral identity. -/
theorem integral_farLeft_digamma_sub_rightShifted_eq_cot
    {x ε a T : ℝ} (hx : 1 < x) (hε : 0 < ε)
    (ha : a ≤ -ε) (hT : T ≠ 0) :
    (∫ σ : ℝ in a..(-ε),
        farLeftDigammaIntegrand x ((σ : ℂ) + T * I)) -
      (∫ σ : ℝ in a..(-ε),
        farLeftRightShiftedDigammaIntegrand x ((σ : ℂ) + T * I)) =
      ∫ σ : ℝ in a..(-ε),
        farLeftCotCorrectionIntegrand x ((σ : ℂ) + T * I) := by
  have hright := intervalIntegrable_farLeft_rightShiftedDigamma hx hε ha hT
  have hcot := intervalIntegrable_farLeft_cotCorrection
    (a := a) (ε := ε) hx hT
  have hsplit : Set.EqOn
      (fun σ : ℝ => farLeftDigammaIntegrand x ((σ : ℂ) + T * I))
      (fun σ : ℝ =>
        farLeftRightShiftedDigammaIntegrand x ((σ : ℂ) + T * I) +
          farLeftCotCorrectionIntegrand x ((σ : ℂ) + T * I))
      (Set.uIcc a (-ε)) := by
    intro σ _hσ
    exact farLeftDigammaIntegrand_eq_rightShifted_add_cot
      (x := x) (s := (σ : ℂ) + T * I) (by simpa using hT)
  have hcongr := intervalIntegral.integral_congr (μ := MeasureTheory.volume) hsplit
  rw [intervalIntegral.integral_add hright hcot] at hcongr
  linear_combination hcongr

/-- On a finite far-left segment, the Gamma-factor integral differs from the
pure digamma integral by exactly the elementary constant-and-tangent
integral. -/
theorem integral_farLeft_gamma_sub_digamma_eq_elementary
    {x ε a T : ℝ} (hx : 1 < x) (hε : 0 < ε)
    (ha : a ≤ -ε) (hT : T ≠ 0) :
    (∫ σ : ℝ in a..(-ε),
        farLeftGammaFactorIntegrand x ((σ : ℂ) + T * I)) -
      (∫ σ : ℝ in a..(-ε),
        farLeftDigammaIntegrand x ((σ : ℂ) + T * I)) =
      ∫ σ : ℝ in a..(-ε),
        farLeftElementaryGammaIntegrand x ((σ : ℂ) + T * I) := by
  have hdig := intervalIntegrable_farLeft_digamma hx hε ha hT
  have helem := intervalIntegrable_farLeft_elementaryGamma
    (a := a) (ε := ε) hx hT
  have hsplit : Set.EqOn
      (fun σ : ℝ => farLeftGammaFactorIntegrand x ((σ : ℂ) + T * I))
      (fun σ : ℝ => farLeftDigammaIntegrand x ((σ : ℂ) + T * I) +
        farLeftElementaryGammaIntegrand x ((σ : ℂ) + T * I))
      (Set.uIcc a (-ε)) := by
    intro σ _hσ
    exact farLeftGammaFactorIntegrand_eq_digamma_add_elementary
      x ((σ : ℂ) + T * I)
  have hcongr := intervalIntegral.integral_congr (μ := MeasureTheory.volume) hsplit
  rw [intervalIntegral.integral_add hdig helem] at hcongr
  linear_combination hcongr

/-- On the far-left horizontal part of a contour, the factor transferred by
the functional equation to the Euler-product half-plane has size
`O(x^σ / |T|)`. -/
theorem norm_farLeft_eulerFactor_le {x ε T σ : ℝ}
    (hx : 1 < x) (hε : 0 < ε) (hσ : σ ≤ -ε) (hT : T ≠ 0) :
    ‖logDeriv riemannZeta (1 - ((σ : ℂ) + T * I)) *
        (x : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I)‖ ≤
      vonMangoldtLSeriesNorm ε * x ^ σ / |T| := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlog0 := norm_neg_logDeriv_riemannZeta_le_vonMangoldtLSeriesNorm
    hε (show 1 + ε ≤ 1 - σ by linarith) (t := -T)
  have hshift :
      (((1 - σ : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) =
        1 - ((σ : ℂ) + T * I) := by
    apply Complex.ext <;> simp
  rw [hshift, norm_neg] at hlog0
  have hC : 0 ≤ vonMangoldtLSeriesNorm ε :=
    tsum_nonneg fun n => norm_nonneg _
  have hline : |T| ≤ ‖((σ : ℂ) + T * I)‖ := by
    simpa using abs_im_le_norm ((σ : ℂ) + T * I)
  have hnum : 0 ≤ vonMangoldtLSeriesNorm ε * x ^ σ :=
    mul_nonneg hC (Real.rpow_nonneg hxpos.le σ)
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  simp only [Complex.add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  calc
    ‖logDeriv riemannZeta (1 - ((σ : ℂ) + T * I))‖ * x ^ σ /
        ‖(σ : ℂ) + T * I‖ ≤
      (vonMangoldtLSeriesNorm ε * x ^ σ) /
        ‖(σ : ℂ) + T * I‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right hlog0 (Real.rpow_nonneg hxpos.le σ)
    _ ≤ (vonMangoldtLSeriesNorm ε * x ^ σ) / |T| :=
      div_le_div_of_nonneg_left hnum (abs_pos.mpr hT) hline

/-- The elementary part of the Archimedean factor is also
`O(x^σ / |T|)` on high horizontal lines. -/
theorem norm_farLeft_elementaryGamma_le {x T σ : ℝ}
    (hx : 1 < x) (hT : 1 ≤ |T|) :
    ‖farLeftElementaryGammaIntegrand x ((σ : ℂ) + T * I)‖ ≤
      (‖Complex.log (2 * Real.pi)‖ + Real.pi) * x ^ σ / |T| := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  let s : ℂ := (σ : ℂ) + T * I
  have harg : 1 ≤ |(Real.pi * s / 2).im| := by
    have him : (Real.pi * s / 2).im = Real.pi * T / 2 := by
      rw [show (Real.pi : ℂ) * s / 2 = ((Real.pi / 2 : ℝ) : ℂ) * s by
        push_cast
        ring]
      simp [s]
      ring
    rw [him]
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
    nlinarith [Real.two_le_pi]
  have htan := norm_tan_le_two_of_one_le_abs_im harg
  have htanTerm :
      ‖(Real.pi / 2 : ℂ) * Complex.tan (Real.pi * s / 2)‖ ≤ Real.pi := by
    rw [norm_mul]
    have hnorm : ‖(Real.pi / 2 : ℂ)‖ = Real.pi / 2 := by
      rw [show (Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by
        push_cast
        ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos Real.pi_pos)]
    rw [hnorm]
    calc
      Real.pi / 2 * ‖Complex.tan (Real.pi * s / 2)‖ ≤ Real.pi / 2 * 2 :=
        mul_le_mul_of_nonneg_left htan (half_pos Real.pi_pos).le
      _ = Real.pi := by ring
  have hcoeff :
      ‖-Complex.log (2 * Real.pi) -
          (Real.pi / 2 : ℂ) * Complex.tan (Real.pi * s / 2)‖ ≤
        ‖Complex.log (2 * Real.pi)‖ + Real.pi := by
    calc
      _ ≤ ‖Complex.log (2 * Real.pi)‖ +
          ‖(Real.pi / 2 : ℂ) * Complex.tan (Real.pi * s / 2)‖ := by
        simpa only [norm_neg] using
          norm_sub_le (-Complex.log (2 * Real.pi))
            ((Real.pi / 2 : ℂ) * Complex.tan (Real.pi * s / 2))
      _ ≤ _ := add_le_add le_rfl htanTerm
  have hline : |T| ≤ ‖s‖ := by
    simpa [s] using abs_im_le_norm s
  have hC : 0 ≤ ‖Complex.log (2 * Real.pi)‖ + Real.pi := by positivity
  have hnum :
      0 ≤ (‖Complex.log (2 * Real.pi)‖ + Real.pi) * x ^ σ :=
    mul_nonneg hC (Real.rpow_nonneg hxpos.le σ)
  simp only [farLeftElementaryGammaIntegrand]
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  simp only [Complex.add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  calc
    ‖-Complex.log (2 * Real.pi) -
          (Real.pi / 2 : ℂ) * Complex.tan (Real.pi * s / 2)‖ * x ^ σ / ‖s‖ ≤
      ((‖Complex.log (2 * Real.pi)‖ + Real.pi) * x ^ σ) / ‖s‖ := by
        apply div_le_div_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hxpos.le σ)
    _ ≤ ((‖Complex.log (2 * Real.pi)‖ + Real.pi) * x ^ σ) / |T| :=
      div_le_div_of_nonneg_left hnum (lt_of_lt_of_le zero_lt_one hT) hline

/-- The cotangent correction from digamma reflection is
`O(x^σ / |T|)` on high horizontal lines. -/
theorem norm_farLeft_cotCorrection_le {x T σ : ℝ}
    (hx : 1 < x) (hT : 1 ≤ |T|) :
    ‖farLeftCotCorrectionIntegrand x ((σ : ℂ) + T * I)‖ ≤
      (2 * Real.pi) * x ^ σ / |T| := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  let s : ℂ := (σ : ℂ) + T * I
  have harg : 1 ≤ |(Real.pi * s).im| := by
    have him : (Real.pi * s).im = Real.pi * T := by simp [s]
    rw [him, abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.two_le_pi]
  have hcot := norm_cot_le_two_of_one_le_abs_im harg
  have hcoeff :
      ‖-(Real.pi : ℂ) * Complex.cot (Real.pi * s)‖ ≤ 2 * Real.pi := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    calc
      Real.pi * ‖Complex.cot (Real.pi * s)‖ ≤ Real.pi * 2 :=
        mul_le_mul_of_nonneg_left hcot Real.pi_pos.le
      _ = 2 * Real.pi := by ring
  have hline : |T| ≤ ‖s‖ := by
    simpa [s] using abs_im_le_norm s
  have hnum : 0 ≤ (2 * Real.pi) * x ^ σ :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hxpos.le σ)
  simp only [farLeftCotCorrectionIntegrand]
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  simp only [Complex.add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  calc
    ‖-(Real.pi : ℂ) * Complex.cot (Real.pi * s)‖ * x ^ σ / ‖s‖ ≤
        ((2 * Real.pi) * x ^ σ) / ‖s‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hxpos.le σ)
    _ ≤ ((2 * Real.pi) * x ^ σ) / |T| :=
      div_le_div_of_nonneg_left hnum (lt_of_lt_of_le zero_lt_one hT) hline

/-- Quantitative pointwise bound for the reflected digamma contribution.  It
retains logarithmic height growth and only linear dependence on the far-left
real coordinate, which remains integrable against `x^σ`. -/
theorem norm_farLeft_rightShiftedDigamma_le {x T σ : ℝ}
    (hx : 1 < x) (hσ : σ ≤ 0) (hT : T ≠ 0) :
    ‖farLeftRightShiftedDigammaIntegrand x ((σ : ℂ) + T * I)‖ ≤
      (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
          Real.log (1 + |T|) - σ) * x ^ σ / |T| := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  let s : ℂ := (σ : ℂ) + T * I
  let z : ℂ := 1 - s
  have hzre : z.re = 1 - σ := by simp [z, s]
  have hzim : z.im = -T := by simp [z, s]
  have hzre1 : 1 ≤ z.re := by rw [hzre]; linarith
  have hnormz : ‖z‖ + 1 ≤ (1 + |T|) * (2 - σ) := by
    have hreabs : |z.re| = 1 - σ := by
      rw [hzre, abs_of_nonneg (by linarith)]
    have himabs : |z.im| = |T| := by rw [hzim, abs_neg]
    calc
      ‖z‖ + 1 ≤ (|z.re| + |z.im|) + 1 :=
        add_le_add (Complex.norm_le_abs_re_add_abs_im z) le_rfl
      _ = |T| + (2 - σ) := by rw [hreabs, himabs]; ring
      _ ≤ (1 + |T|) * (2 - σ) := by
        nlinarith [abs_nonneg T]
  have hlogHeight : 0 ≤ Real.log (1 + |T|) :=
    Real.log_nonneg (by linarith [abs_nonneg T])
  have hlogReal : Real.log (2 - σ) ≤ 1 - σ := by
    have hpos : 0 < 2 - σ := by linarith
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlog : Real.log (‖z‖ + 1) ≤ Real.log (1 + |T|) + (1 - σ) := by
    have hpos1 : 0 < ‖z‖ + 1 := by positivity
    have hposT : 0 < 1 + |T| := by positivity
    have hposσ : 0 < 2 - σ := by linarith
    calc
      Real.log (‖z‖ + 1) ≤ Real.log ((1 + |T|) * (2 - σ)) :=
        Real.log_le_log hpos1 hnormz
      _ = Real.log (1 + |T|) + Real.log (2 - σ) :=
        Real.log_mul hposT.ne' hposσ.ne'
      _ ≤ Real.log (1 + |T|) + (1 - σ) :=
        add_le_add le_rfl hlogReal
  have hdig := PrimeNumberTheorem.norm_digamma_le_log hzre1
  have hdig' : ‖Complex.digamma z‖ ≤
      ‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
        Real.log (1 + |T|) - σ := by
    exact hdig.trans (by linarith)
  have hline : |T| ≤ ‖s‖ := by
    simpa [s] using abs_im_le_norm s
  have hC : 0 ≤ ‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
      Real.log (1 + |T|) - σ := by
    linarith [norm_nonneg (Real.eulerMascheroniConstant : ℂ)]
  have hnum : 0 ≤
      (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
        Real.log (1 + |T|) - σ) * x ^ σ :=
    mul_nonneg hC (Real.rpow_nonneg hxpos.le σ)
  simp only [farLeftRightShiftedDigammaIntegrand]
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  simp only [Complex.add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  change ‖Complex.digamma z‖ * x ^ σ / ‖s‖ ≤ _
  calc
    ‖Complex.digamma z‖ * x ^ σ / ‖s‖ ≤
        ((‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
          Real.log (1 + |T|) - σ) * x ^ σ) / ‖s‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right hdig' (Real.rpow_nonneg hxpos.le σ)
    _ ≤ ((‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
          Real.log (1 + |T|) - σ) * x ^ σ) / |T| :=
      div_le_div_of_nonneg_left hnum (abs_pos.mpr hT) hline

private theorem intervalIntegral_const_rpow_exponent {x a b : ℝ}
    (hx : 1 < x) :
    (∫ σ : ℝ in a..b, x ^ σ) = (x ^ b - x ^ a) / Real.log x := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  let F : ℝ → ℝ := fun σ => x ^ σ / Real.log x
  have hderiv : deriv F = fun σ : ℝ => x ^ σ := by
    funext σ
    have hd := ((hasDerivAt_id σ).const_rpow hxpos).div_const (Real.log x)
    change deriv F σ = x ^ σ
    rw [show deriv F σ = (Real.log x * 1 * x ^ σ) / Real.log x by
      exact hd.deriv]
    field_simp
  have hdiff : ∀ σ ∈ Set.uIcc a b, DifferentiableAt ℝ F σ := by
    intro σ _hσ
    exact (((hasDerivAt_id σ).const_rpow hxpos).div_const (Real.log x)).differentiableAt
  have hcont : ContinuousOn (fun σ : ℝ => x ^ σ) (Set.uIcc a b) :=
    (Real.continuous_const_rpow (ne_of_gt hxpos)).continuousOn
  have hfund := intervalIntegral.integral_deriv_eq_sub' F hderiv hdiff hcont
  calc
    (∫ σ : ℝ in a..b, x ^ σ) = x ^ b / Real.log x - x ^ a / Real.log x := by
      simpa [F] using hfund
    _ = (x ^ b - x ^ a) / Real.log x := by ring

private theorem intervalIntegral_neg_mul_rpow_exponent {x a b : ℝ}
    (hx : 1 < x) :
    (∫ σ : ℝ in a..b, (-σ) * x ^ σ) =
      x ^ b * (1 / Real.log x ^ 2 - b / Real.log x) -
        x ^ a * (1 / Real.log x ^ 2 - a / Real.log x) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  let F : ℝ → ℝ := fun σ =>
    x ^ σ * (1 / Real.log x ^ 2 - σ / Real.log x)
  have hderiv : deriv F = fun σ : ℝ => (-σ) * x ^ σ := by
    funext σ
    have hp := (hasDerivAt_id σ).const_rpow hxpos
    have hq : HasDerivAt
        (fun u : ℝ => 1 / Real.log x ^ 2 - u / Real.log x)
        (-1 / Real.log x) σ := by
      convert (hasDerivAt_const σ (1 / Real.log x ^ 2)).sub
        ((hasDerivAt_id σ).div_const (Real.log x)) using 1
      all_goals ring
    have hmul := hp.mul hq
    change deriv F σ = (-σ) * x ^ σ
    rw [show deriv F σ =
        (Real.log x * 1 * x ^ σ) *
            (1 / Real.log x ^ 2 - σ / Real.log x) +
          x ^ σ * (-1 / Real.log x) by exact hmul.deriv]
    field_simp [hlog]
    ring
  have hdiff : ∀ σ ∈ Set.uIcc a b, DifferentiableAt ℝ F σ := by
    intro σ _hσ
    apply DifferentiableAt.mul
    · exact ((hasDerivAt_id σ).const_rpow hxpos).differentiableAt
    · fun_prop
  have hcont : ContinuousOn (fun σ : ℝ => (-σ) * x ^ σ) (Set.uIcc a b) := by
    exact (continuous_neg.comp continuous_id).continuousOn.mul
      (Real.continuous_const_rpow (ne_of_gt hxpos)).continuousOn
  have hfund := intervalIntegral.integral_deriv_eq_sub' F hderiv hdiff hcont
  simpa [F] using hfund

/-- Uniform finite-segment bound for the reflected digamma contribution.  The
right side is independent of the moving left endpoint. -/
theorem norm_integral_farLeft_rightShiftedDigamma_le {x ε a T : ℝ}
    (hx : 1 < x) (hε : 0 < ε) (ha : a ≤ -ε) (hT : T ≠ 0) :
    ‖∫ σ : ℝ in a..(-ε),
        farLeftRightShiftedDigammaIntegrand x ((σ : ℂ) + T * I)‖ ≤
      (1 / |T|) *
        ((‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
            Real.log (1 + |T|)) * x ^ (-ε) / Real.log x +
          x ^ (-ε) *
            (1 / Real.log x ^ 2 + ε / Real.log x)) := by
  let C : ℝ := ‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
    Real.log (1 + |T|)
  let g : ℝ → ℝ := fun σ => (1 / |T|) * ((C - σ) * x ^ σ)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le
    (μ := MeasureTheory.volume)
    (f := fun σ : ℝ =>
      farLeftRightShiftedDigammaIntegrand x ((σ : ℂ) + T * I))
    (g := g) ha
    (Filter.Eventually.of_forall fun σ hσ => by
      have hσ0 : σ ≤ 0 := by linarith [hσ.2]
      have hpoint := norm_farLeft_rightShiftedDigamma_le
        (x := x) (T := T) (σ := σ) hx hσ0 hT
      convert hpoint using 1
      all_goals (dsimp [g, C]; ring))
    (by
      apply Continuous.intervalIntegrable
      apply Continuous.mul continuous_const
      apply Continuous.mul
      · fun_prop
      · exact Real.continuous_const_rpow
          (ne_of_gt (zero_lt_one.trans hx)))
  have hrewrite : g = fun σ : ℝ =>
      (C / |T|) * x ^ σ + (1 / |T|) * ((-σ) * x ^ σ) := by
    funext σ
    dsimp [g]
    ring
  rw [hrewrite, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral_const_rpow_exponent hx,
    intervalIntegral_neg_mul_rpow_exponent hx] at hbound
  · refine hbound.trans ?_
    have hxpos : 0 < x := zero_lt_one.trans hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hTabs : 0 < |T| := abs_pos.mpr hT
    have hC : 0 ≤ C := by
      dsimp [C]
      have hlogT : 0 ≤ Real.log (1 + |T|) :=
        Real.log_nonneg (by linarith [abs_nonneg T])
      positivity
    have hxa : 0 ≤ x ^ a := Real.rpow_nonneg hxpos.le _
    have hconstDiff : x ^ (-ε) - x ^ a ≤ x ^ (-ε) := by linarith
    have ha0 : a ≤ 0 := by linarith
    have hFa : 0 ≤ x ^ a *
        (1 / Real.log x ^ 2 - a / Real.log x) := by
      apply mul_nonneg (Real.rpow_nonneg hxpos.le _)
      have : 0 ≤ -a / Real.log x := div_nonneg (neg_nonneg.mpr ha0) hlog.le
      have hone : 0 ≤ 1 / Real.log x ^ 2 := one_div_nonneg.mpr (sq_nonneg _)
      rw [show 1 / Real.log x ^ 2 - a / Real.log x =
          1 / Real.log x ^ 2 + (-a) / Real.log x by ring]
      exact add_nonneg hone this
    dsimp [C] at hC ⊢
    have hconst :
        (C / |T|) * ((x ^ (-ε) - x ^ a) / Real.log x) ≤
          (1 / |T|) * (C * x ^ (-ε) / Real.log x) := by
      rw [show (C / |T|) * ((x ^ (-ε) - x ^ a) / Real.log x) =
          (1 / |T|) * (C * (x ^ (-ε) - x ^ a) / Real.log x) by ring]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hconstDiff hC) hlog.le)
        (one_div_nonneg.mpr hTabs.le)
    have hlinear :
        (1 / |T|) *
            (x ^ (-ε) * (1 / Real.log x ^ 2 - (-ε) / Real.log x) -
              x ^ a * (1 / Real.log x ^ 2 - a / Real.log x)) ≤
          (1 / |T|) *
            (x ^ (-ε) * (1 / Real.log x ^ 2 + ε / Real.log x)) := by
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hTabs.le)
      have heq : 1 / Real.log x ^ 2 - (-ε) / Real.log x =
          1 / Real.log x ^ 2 + ε / Real.log x := by ring
      rw [heq]
      linarith
    linarith
  · apply Continuous.intervalIntegrable
    exact continuous_const.mul
      (Real.continuous_const_rpow (ne_of_gt (zero_lt_one.trans hx)))
  · apply Continuous.intervalIntegrable
    exact continuous_const.mul ((continuous_neg.comp continuous_id).mul
      (Real.continuous_const_rpow (ne_of_gt (zero_lt_one.trans hx))))

private theorem tendsto_log_one_add_div_atTop :
    Tendsto (fun T : ℝ => Real.log (1 + T) / T) atTop (𝓝 0) := by
  have hshift : Tendsto (fun T : ℝ => T + 1) atTop atTop :=
    tendsto_id.atTop_add tendsto_const_nhds
  have h := (Real.tendsto_pow_log_div_mul_add_atTop
    1 (-1) 1 one_ne_zero).comp hshift
  convert h using 1
  funext T
  dsimp [Function.comp_def]
  rw [pow_one]
  congr 2 <;> ring

/-- The remaining reflected-digamma integral vanishes on the moving upper
far-left horizontal segment. -/
theorem tendsto_integral_farLeft_rightShiftedDigamma_atTop
    {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ => ∫ σ : ℝ in a T..(-ε),
        farLeftRightShiftedDigammaIntegrand x ((σ : ℂ) + T * I))
      atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simp only [sub_zero]
  let A : ℝ := x ^ (-ε) / Real.log x
  let B : ℝ := x ^ (-ε) *
    (1 / Real.log x ^ 2 + ε / Real.log x)
  let K : ℝ :=
    (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4) * A + B
  have hK : Tendsto (fun T : ℝ => K / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlog : Tendsto
      (fun T : ℝ => A * (Real.log (1 + T) / T)) atTop (𝓝 0) := by
    simpa using tendsto_log_one_add_div_atTop.const_mul A
  have hupper := hK.add hlog
  have hupper' : Tendsto
      (fun T : ℝ => K / T + A * (Real.log (1 + T) / T))
      atTop (𝓝 0) := by simpa only [add_zero] using hupper
  apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hupper'
  filter_upwards [ha, eventually_gt_atTop (1 : ℝ)] with T haT hT
  have hmain := norm_integral_farLeft_rightShiftedDigamma_le
    hx hε haT (zero_lt_one.trans hT).ne'
  rw [abs_of_pos (zero_lt_one.trans hT)] at hmain
  refine hmain.trans_eq ?_
  dsimp [A, B, K]
  ring

/-- The reflected-digamma integral also vanishes on the moving lower
far-left horizontal segment. -/
theorem tendsto_integral_farLeft_rightShiftedDigamma_neg_height_atTop
    {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ => ∫ σ : ℝ in a T..(-ε),
        farLeftRightShiftedDigammaIntegrand x ((σ : ℂ) - T * I))
      atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simp only [sub_zero]
  let A : ℝ := x ^ (-ε) / Real.log x
  let B : ℝ := x ^ (-ε) *
    (1 / Real.log x ^ 2 + ε / Real.log x)
  let K : ℝ :=
    (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4) * A + B
  have hK : Tendsto (fun T : ℝ => K / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlog : Tendsto
      (fun T : ℝ => A * (Real.log (1 + T) / T)) atTop (𝓝 0) := by
    simpa using tendsto_log_one_add_div_atTop.const_mul A
  have hupper := hK.add hlog
  have hupper' : Tendsto
      (fun T : ℝ => K / T + A * (Real.log (1 + T) / T))
      atTop (𝓝 0) := by simpa only [add_zero] using hupper
  apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hupper'
  filter_upwards [ha, eventually_gt_atTop (1 : ℝ)] with T haT hT
  have hmain := norm_integral_farLeft_rightShiftedDigamma_le
    (T := -T) hx hε haT (neg_ne_zero.mpr (zero_lt_one.trans hT).ne')
  have hmain' :
      ‖∫ σ : ℝ in a T..(-ε),
          farLeftRightShiftedDigammaIntegrand x ((σ : ℂ) - T * I)‖ ≤
        (1 / T) *
          ((‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
              Real.log (1 + T)) * x ^ (-ε) / Real.log x +
            x ^ (-ε) *
              (1 / Real.log x ^ 2 + ε / Real.log x)) := by
    simpa [sub_eq_add_neg, abs_of_pos (zero_lt_one.trans hT)] using hmain
  refine hmain'.trans_eq ?_
  dsimp [A, B, K]
  ring

/-- Uniform integral bound for the elementary Archimedean contribution on a
far-left horizontal segment. -/
theorem norm_integral_farLeft_elementaryGamma_le {x ε a T : ℝ}
    (hx : 1 < x) (ha : a ≤ -ε) (hT : 1 ≤ |T|) :
    ‖∫ σ : ℝ in a..(-ε),
        farLeftElementaryGammaIntegrand x ((σ : ℂ) + T * I)‖ ≤
      ((‖Complex.log (2 * Real.pi)‖ + Real.pi) / |T|) *
        (x ^ (-ε) - x ^ a) / Real.log x := by
  let C : ℝ := (‖Complex.log (2 * Real.pi)‖ + Real.pi) / |T|
  have hbound := intervalIntegral.norm_integral_le_of_norm_le
    (μ := MeasureTheory.volume)
    (f := fun σ : ℝ =>
      farLeftElementaryGammaIntegrand x ((σ : ℂ) + T * I))
    (g := fun σ : ℝ => C * x ^ σ) ha
    (Filter.Eventually.of_forall fun σ hσ => by
      have hpoint := norm_farLeft_elementaryGamma_le (σ := σ) hx hT
      convert hpoint using 1
      all_goals (dsimp [C]; ring))
    ((continuous_const.mul (Real.continuous_const_rpow
      (ne_of_gt (zero_lt_one.trans hx)))).intervalIntegrable
        (μ := MeasureTheory.volume) _ _)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral_const_rpow_exponent hx] at hbound
  convert hbound using 1
  all_goals (dsimp [C]; ring)

/-- The elementary constant and tangent terms vanish on the moving upper
far-left horizontal segment. -/
theorem tendsto_integral_farLeft_elementaryGamma_atTop {x ε : ℝ}
    (hx : 1 < x) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ => ∫ σ : ℝ in a T..(-ε),
        farLeftElementaryGammaIntegrand x ((σ : ℂ) + T * I))
      atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simp only [sub_zero]
  let K : ℝ :=
    (‖Complex.log (2 * Real.pi)‖ + Real.pi) * x ^ (-ε) / Real.log x
  have hKdiv : Tendsto (fun T : ℝ => K / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hKdiv
  filter_upwards [ha, eventually_gt_atTop (1 : ℝ)] with T haT hT
  have hmain := norm_integral_farLeft_elementaryGamma_le
    hx haT (by rw [abs_of_pos (zero_lt_one.trans hT)]; exact hT.le)
  rw [abs_of_pos (zero_lt_one.trans hT)] at hmain
  refine hmain.trans ?_
  have hC : 0 ≤ ‖Complex.log (2 * Real.pi)‖ + Real.pi := by positivity
  have hxa : 0 ≤ x ^ a T := Real.rpow_nonneg (zero_lt_one.trans hx).le _
  have hdiff : x ^ (-ε) - x ^ a T ≤ x ^ (-ε) := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  dsimp [K]
  rw [show
    ((‖Complex.log (2 * Real.pi)‖ + Real.pi) * x ^ (-ε) / Real.log x) / T =
      ((‖Complex.log (2 * Real.pi)‖ + Real.pi) / T) * x ^ (-ε) /
        Real.log x by ring]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdiff
      (div_nonneg hC (zero_lt_one.trans hT).le)) hlog.le

/-- The elementary constant and tangent terms also vanish on the moving lower
far-left horizontal segment. -/
theorem tendsto_integral_farLeft_elementaryGamma_neg_height_atTop
    {x ε : ℝ} (hx : 1 < x) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ => ∫ σ : ℝ in a T..(-ε),
        farLeftElementaryGammaIntegrand x ((σ : ℂ) - T * I))
      atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simp only [sub_zero]
  let K : ℝ :=
    (‖Complex.log (2 * Real.pi)‖ + Real.pi) * x ^ (-ε) / Real.log x
  have hKdiv : Tendsto (fun T : ℝ => K / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hKdiv
  filter_upwards [ha, eventually_gt_atTop (1 : ℝ)] with T haT hT
  have hmain := norm_integral_farLeft_elementaryGamma_le
    (T := -T) hx haT (by simpa [abs_of_pos (zero_lt_one.trans hT)] using hT.le)
  have hmain' :
      ‖∫ σ : ℝ in a T..(-ε),
          farLeftElementaryGammaIntegrand x ((σ : ℂ) - T * I)‖ ≤
        ((‖Complex.log (2 * Real.pi)‖ + Real.pi) / T) *
          (x ^ (-ε) - x ^ a T) / Real.log x := by
    simpa [sub_eq_add_neg, abs_of_pos (zero_lt_one.trans hT)] using hmain
  refine hmain'.trans ?_
  have hC : 0 ≤ ‖Complex.log (2 * Real.pi)‖ + Real.pi := by positivity
  have hxa : 0 ≤ x ^ a T := Real.rpow_nonneg (zero_lt_one.trans hx).le _
  have hdiff : x ^ (-ε) - x ^ a T ≤ x ^ (-ε) := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  dsimp [K]
  rw [show
    ((‖Complex.log (2 * Real.pi)‖ + Real.pi) * x ^ (-ε) / Real.log x) / T =
      ((‖Complex.log (2 * Real.pi)‖ + Real.pi) / T) * x ^ (-ε) /
        Real.log x by ring]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdiff
      (div_nonneg hC (zero_lt_one.trans hT).le)) hlog.le

/-- Uniform integral bound for the cotangent correction introduced by
digamma reflection. -/
theorem norm_integral_farLeft_cotCorrection_le {x ε a T : ℝ}
    (hx : 1 < x) (ha : a ≤ -ε) (hT : 1 ≤ |T|) :
    ‖∫ σ : ℝ in a..(-ε),
        farLeftCotCorrectionIntegrand x ((σ : ℂ) + T * I)‖ ≤
      ((2 * Real.pi) / |T|) *
        (x ^ (-ε) - x ^ a) / Real.log x := by
  let C : ℝ := (2 * Real.pi) / |T|
  have hbound := intervalIntegral.norm_integral_le_of_norm_le
    (μ := MeasureTheory.volume)
    (f := fun σ : ℝ =>
      farLeftCotCorrectionIntegrand x ((σ : ℂ) + T * I))
    (g := fun σ : ℝ => C * x ^ σ) ha
    (Filter.Eventually.of_forall fun σ hσ => by
      have hpoint := norm_farLeft_cotCorrection_le (σ := σ) hx hT
      convert hpoint using 1
      all_goals (dsimp [C]; ring))
    ((continuous_const.mul (Real.continuous_const_rpow
      (ne_of_gt (zero_lt_one.trans hx)))).intervalIntegrable
        (μ := MeasureTheory.volume) _ _)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral_const_rpow_exponent hx] at hbound
  convert hbound using 1
  all_goals (dsimp [C]; ring)

/-- The cotangent correction vanishes on the moving upper far-left
horizontal segment. -/
theorem tendsto_integral_farLeft_cotCorrection_atTop {x ε : ℝ}
    (hx : 1 < x) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ => ∫ σ : ℝ in a T..(-ε),
        farLeftCotCorrectionIntegrand x ((σ : ℂ) + T * I))
      atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simp only [sub_zero]
  let K : ℝ := (2 * Real.pi) * x ^ (-ε) / Real.log x
  have hKdiv : Tendsto (fun T : ℝ => K / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hKdiv
  filter_upwards [ha, eventually_gt_atTop (1 : ℝ)] with T haT hT
  have hmain := norm_integral_farLeft_cotCorrection_le
    hx haT (by rw [abs_of_pos (zero_lt_one.trans hT)]; exact hT.le)
  rw [abs_of_pos (zero_lt_one.trans hT)] at hmain
  refine hmain.trans ?_
  have hxa : 0 ≤ x ^ a T := Real.rpow_nonneg (zero_lt_one.trans hx).le _
  have hdiff : x ^ (-ε) - x ^ a T ≤ x ^ (-ε) := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  dsimp [K]
  rw [show
    ((2 * Real.pi) * x ^ (-ε) / Real.log x) / T =
      ((2 * Real.pi) / T) * x ^ (-ε) / Real.log x by ring]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdiff
      (div_nonneg (by positivity) (zero_lt_one.trans hT).le)) hlog.le

/-- The cotangent correction also vanishes on the moving lower far-left
horizontal segment. -/
theorem tendsto_integral_farLeft_cotCorrection_neg_height_atTop
    {x ε : ℝ} (hx : 1 < x) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ => ∫ σ : ℝ in a T..(-ε),
        farLeftCotCorrectionIntegrand x ((σ : ℂ) - T * I))
      atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simp only [sub_zero]
  let K : ℝ := (2 * Real.pi) * x ^ (-ε) / Real.log x
  have hKdiv : Tendsto (fun T : ℝ => K / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hKdiv
  filter_upwards [ha, eventually_gt_atTop (1 : ℝ)] with T haT hT
  have hmain := norm_integral_farLeft_cotCorrection_le
    (T := -T) hx haT (by simpa [abs_of_pos (zero_lt_one.trans hT)] using hT.le)
  have hmain' :
      ‖∫ σ : ℝ in a T..(-ε),
          farLeftCotCorrectionIntegrand x ((σ : ℂ) - T * I)‖ ≤
        ((2 * Real.pi) / T) *
          (x ^ (-ε) - x ^ a T) / Real.log x := by
    simpa [sub_eq_add_neg, abs_of_pos (zero_lt_one.trans hT)] using hmain
  refine hmain'.trans ?_
  have hxa : 0 ≤ x ^ a T := Real.rpow_nonneg (zero_lt_one.trans hx).le _
  have hdiff : x ^ (-ε) - x ^ a T ≤ x ^ (-ε) := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  dsimp [K]
  rw [show
    ((2 * Real.pi) * x ^ (-ε) / Real.log x) / T =
      ((2 * Real.pi) / T) * x ^ (-ε) / Real.log x by ring]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdiff
      (div_nonneg (by positivity) (zero_lt_one.trans hT).le)) hlog.le

/-- The Euler-product part of the functional-equation decomposition makes a
uniformly vanishing contribution on the whole far-left horizontal segment.
The bound is independent of how far the left endpoint has moved. -/
theorem norm_integral_farLeft_eulerFactor_le {x ε a T : ℝ}
    (hx : 1 < x) (hε : 0 < ε) (ha : a ≤ -ε) (hT : T ≠ 0) :
    ‖∫ σ : ℝ in a..(-ε),
        logDeriv riemannZeta (1 - ((σ : ℂ) + T * I)) *
          (x : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I)‖ ≤
      (vonMangoldtLSeriesNorm ε / |T|) *
        (x ^ (-ε) - x ^ a) / Real.log x := by
  let C : ℝ := vonMangoldtLSeriesNorm ε / |T|
  have hbound := intervalIntegral.norm_integral_le_of_norm_le
    (μ := MeasureTheory.volume)
    (f := fun σ : ℝ =>
      logDeriv riemannZeta (1 - ((σ : ℂ) + T * I)) *
        (x : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I))
    (g := fun σ : ℝ => C * x ^ σ) ha
    (Filter.Eventually.of_forall fun σ hσ => by
      have hσle : σ ≤ -ε := by
        rw [Set.mem_Ioc] at hσ
        exact hσ.2
      have hpoint := norm_farLeft_eulerFactor_le hx hε hσle hT
      convert hpoint using 1
      all_goals (dsimp [C]; ring))
    ((continuous_const.mul (Real.continuous_const_rpow
      (ne_of_gt (zero_lt_one.trans hx)))).intervalIntegrable
        (μ := MeasureTheory.volume) _ _)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral_const_rpow_exponent hx] at hbound
  convert hbound using 1
  all_goals (dsimp [C]; ring)

/-- Even if the left endpoint moves arbitrarily far to the left, the entire
Euler-product part of the upper far-left horizontal edge tends to zero as its
height tends to infinity. -/
theorem tendsto_integral_farLeft_eulerFactor_atTop {x ε : ℝ}
    (hx : 1 < x) (hε : 0 < ε) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ => ∫ σ : ℝ in a T..(-ε),
        logDeriv riemannZeta (1 - ((σ : ℂ) + T * I)) *
          (x : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I))
      atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simp only [sub_zero]
  let K : ℝ :=
    vonMangoldtLSeriesNorm ε * x ^ (-ε) / Real.log x
  have hKdiv : Tendsto (fun T : ℝ => K / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hKdiv
  filter_upwards [ha, eventually_gt_atTop (0 : ℝ)] with T haT hT
  have hmain := norm_integral_farLeft_eulerFactor_le hx hε haT hT.ne'
  rw [abs_of_pos hT] at hmain
  refine hmain.trans ?_
  have hM : 0 ≤ vonMangoldtLSeriesNorm ε :=
    tsum_nonneg fun n => norm_nonneg _
  have hxa : 0 ≤ x ^ a T := Real.rpow_nonneg (zero_lt_one.trans hx).le _
  have hxε : 0 ≤ x ^ (-ε) := Real.rpow_nonneg (zero_lt_one.trans hx).le _
  have hpowle : x ^ a T ≤ x ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_le hx.le haT
  have hdiff0 : 0 ≤ x ^ (-ε) - x ^ a T := by linarith
  have hdiff : x ^ (-ε) - x ^ a T ≤ x ^ (-ε) := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  dsimp [K]
  rw [show
    (vonMangoldtLSeriesNorm ε * x ^ (-ε) / Real.log x) / T =
      (vonMangoldtLSeriesNorm ε / T) * x ^ (-ε) / Real.log x by ring]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdiff (div_nonneg hM hT.le)) hlog.le

/-- The lower far-left horizontal edge has the same vanishing Euler-product
contribution as the upper edge. -/
theorem tendsto_integral_farLeft_eulerFactor_neg_height_atTop {x ε : ℝ}
    (hx : 1 < x) (hε : 0 < ε) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ => ∫ σ : ℝ in a T..(-ε),
        logDeriv riemannZeta (1 - ((σ : ℂ) - T * I)) *
          (x : ℂ) ^ ((σ : ℂ) - T * I) / ((σ : ℂ) - T * I))
      atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simp only [sub_zero]
  let K : ℝ :=
    vonMangoldtLSeriesNorm ε * x ^ (-ε) / Real.log x
  have hKdiv : Tendsto (fun T : ℝ => K / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hKdiv
  filter_upwards [ha, eventually_gt_atTop (0 : ℝ)] with T haT hT
  have hmain := norm_integral_farLeft_eulerFactor_le
    (T := -T) hx hε haT (neg_ne_zero.mpr hT.ne')
  have hmain' :
      ‖∫ σ : ℝ in a T..(-ε),
          logDeriv riemannZeta (1 - ((σ : ℂ) - T * I)) *
            (x : ℂ) ^ ((σ : ℂ) - T * I) / ((σ : ℂ) - T * I)‖ ≤
        (vonMangoldtLSeriesNorm ε / T) *
          (x ^ (-ε) - x ^ a T) / Real.log x := by
    simpa [sub_eq_add_neg, abs_of_pos hT] using hmain
  refine hmain'.trans ?_
  have hM : 0 ≤ vonMangoldtLSeriesNorm ε :=
    tsum_nonneg fun n => norm_nonneg _
  have hxa : 0 ≤ x ^ a T := Real.rpow_nonneg (zero_lt_one.trans hx).le _
  have hdiff : x ^ (-ε) - x ^ a T ≤ x ^ (-ε) := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  dsimp [K]
  rw [show
    (vonMangoldtLSeriesNorm ε * x ^ (-ε) / Real.log x) / T =
      (vonMangoldtLSeriesNorm ε / T) * x ^ (-ε) / Real.log x by ring]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdiff (div_nonneg hM hT.le)) hlog.le

/-- On the moving upper far-left horizontal segment, the full contour
integral is asymptotic to the explicit Archimedean Gamma-factor integral. -/
theorem tendsto_integral_farLeft_explicit_sub_gamma_atTop {x ε : ℝ}
    (hx : 1 < x) (hε : 0 < ε) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ =>
        (∫ σ : ℝ in a T..(-ε),
          explicitFormulaIntegrand x ((σ : ℂ) + T * I)) -
        ∫ σ : ℝ in a T..(-ε),
          farLeftGammaFactorIntegrand x ((σ : ℂ) + T * I))
      atTop (𝓝 0) := by
  apply (tendsto_integral_farLeft_eulerFactor_atTop hx hε a ha).congr'
  filter_upwards [ha, eventually_gt_atTop (0 : ℝ)] with T haT hT
  exact (integral_farLeft_explicit_sub_gamma_eq_euler hx hε haT hT.ne').symm

/-- The same Gamma-factor reduction holds on the moving lower far-left
horizontal segment. -/
theorem tendsto_integral_farLeft_explicit_sub_gamma_neg_height_atTop
    {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ =>
        (∫ σ : ℝ in a T..(-ε),
          explicitFormulaIntegrand x ((σ : ℂ) - T * I)) -
        ∫ σ : ℝ in a T..(-ε),
          farLeftGammaFactorIntegrand x ((σ : ℂ) - T * I))
      atTop (𝓝 0) := by
  apply (tendsto_integral_farLeft_eulerFactor_neg_height_atTop hx hε a ha).congr'
  filter_upwards [ha, eventually_gt_atTop (0 : ℝ)] with T haT hT
  have heq := integral_farLeft_explicit_sub_gamma_eq_euler
    (T := -T) hx hε haT (neg_ne_zero.mpr hT.ne')
  simpa [sub_eq_add_neg] using heq.symm

/-- On the upper far-left horizontal segment, the full contour integral is
asymptotic to the pure digamma integral.  Thus all zeta and elementary
Archimedean terms on this segment have been eliminated. -/
theorem tendsto_integral_farLeft_explicit_sub_digamma_atTop
    {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ =>
        (∫ σ : ℝ in a T..(-ε),
          explicitFormulaIntegrand x ((σ : ℂ) + T * I)) -
        ∫ σ : ℝ in a T..(-ε),
          farLeftDigammaIntegrand x ((σ : ℂ) + T * I))
      atTop (𝓝 0) := by
  have hgamma := tendsto_integral_farLeft_explicit_sub_gamma_atTop hx hε a ha
  have helem := tendsto_integral_farLeft_elementaryGamma_atTop hx a ha
  have hsum := hgamma.add helem
  simpa only [add_zero] using hsum.congr' (by
    filter_upwards [ha, eventually_gt_atTop (1 : ℝ)] with T haT hT
    have hsplit := integral_farLeft_gamma_sub_digamma_eq_elementary
      hx hε haT (zero_lt_one.trans hT).ne'
    linear_combination -hsplit)

/-- The corresponding lower far-left horizontal integral is also asymptotic
to its pure digamma contribution. -/
theorem tendsto_integral_farLeft_explicit_sub_digamma_neg_height_atTop
    {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ =>
        (∫ σ : ℝ in a T..(-ε),
          explicitFormulaIntegrand x ((σ : ℂ) - T * I)) -
        ∫ σ : ℝ in a T..(-ε),
          farLeftDigammaIntegrand x ((σ : ℂ) - T * I))
      atTop (𝓝 0) := by
  have hgamma :=
    tendsto_integral_farLeft_explicit_sub_gamma_neg_height_atTop hx hε a ha
  have helem := tendsto_integral_farLeft_elementaryGamma_neg_height_atTop hx a ha
  have hsum := hgamma.add helem
  simpa only [add_zero] using hsum.congr' (by
    filter_upwards [ha, eventually_gt_atTop (1 : ℝ)] with T haT hT
    have hsplit := integral_farLeft_gamma_sub_digamma_eq_elementary
      (T := -T) hx hε haT (neg_ne_zero.mpr (zero_lt_one.trans hT).ne')
    have hsplit' :
        (∫ σ : ℝ in a T..(-ε),
            farLeftGammaFactorIntegrand x ((σ : ℂ) - T * I)) -
          (∫ σ : ℝ in a T..(-ε),
            farLeftDigammaIntegrand x ((σ : ℂ) - T * I)) =
          ∫ σ : ℝ in a T..(-ε),
            farLeftElementaryGammaIntegrand x ((σ : ℂ) - T * I) := by
      simpa [sub_eq_add_neg] using hsplit
    linear_combination -hsplit')

/-- Digamma reflection moves the only remaining upper far-left contribution
to `digamma (1 - s)` in the right half-plane; its cotangent correction
vanishes uniformly in the moving left endpoint. -/
theorem tendsto_integral_farLeft_explicit_sub_rightShiftedDigamma_atTop
    {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ =>
        (∫ σ : ℝ in a T..(-ε),
          explicitFormulaIntegrand x ((σ : ℂ) + T * I)) -
        ∫ σ : ℝ in a T..(-ε),
          farLeftRightShiftedDigammaIntegrand x ((σ : ℂ) + T * I))
      atTop (𝓝 0) := by
  have hdig := tendsto_integral_farLeft_explicit_sub_digamma_atTop
    hx hε a ha
  have hcot := tendsto_integral_farLeft_cotCorrection_atTop hx a ha
  have hsum := hdig.add hcot
  simpa only [add_zero] using hsum.congr' (by
    filter_upwards [ha, eventually_gt_atTop (1 : ℝ)] with T haT hT
    have hsplit := integral_farLeft_digamma_sub_rightShifted_eq_cot
      hx hε haT (zero_lt_one.trans hT).ne'
    linear_combination -hsplit)

/-- The same right-half-plane digamma reduction holds on the lower far-left
horizontal segment. -/
theorem tendsto_integral_farLeft_explicit_sub_rightShiftedDigamma_neg_height_atTop
    {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ =>
        (∫ σ : ℝ in a T..(-ε),
          explicitFormulaIntegrand x ((σ : ℂ) - T * I)) -
        ∫ σ : ℝ in a T..(-ε),
          farLeftRightShiftedDigammaIntegrand x ((σ : ℂ) - T * I))
      atTop (𝓝 0) := by
  have hdig := tendsto_integral_farLeft_explicit_sub_digamma_neg_height_atTop
    hx hε a ha
  have hcot := tendsto_integral_farLeft_cotCorrection_neg_height_atTop hx a ha
  have hsum := hdig.add hcot
  simpa only [add_zero] using hsum.congr' (by
    filter_upwards [ha, eventually_gt_atTop (1 : ℝ)] with T haT hT
    have hsplit := integral_farLeft_digamma_sub_rightShifted_eq_cot
      (T := -T) hx hε haT (neg_ne_zero.mpr (zero_lt_one.trans hT).ne')
    have hsplit' :
        (∫ σ : ℝ in a T..(-ε),
            farLeftDigammaIntegrand x ((σ : ℂ) - T * I)) -
          (∫ σ : ℝ in a T..(-ε),
            farLeftRightShiftedDigammaIntegrand x ((σ : ℂ) - T * I)) =
          ∫ σ : ℝ in a T..(-ε),
            farLeftCotCorrectionIntegrand x ((σ : ℂ) - T * I) := by
      simpa [sub_eq_add_neg] using hsplit
    linear_combination -hsplit')

/-- The complete moving upper far-left horizontal contribution to the
first-order explicit-formula contour tends to zero. -/
theorem tendsto_integral_farLeft_explicit_atTop
    {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ => ∫ σ : ℝ in a T..(-ε),
        explicitFormulaIntegrand x ((σ : ℂ) + T * I))
      atTop (𝓝 0) := by
  have hsub :=
    tendsto_integral_farLeft_explicit_sub_rightShiftedDigamma_atTop
      hx hε a ha
  have hright :=
    tendsto_integral_farLeft_rightShiftedDigamma_atTop hx hε a ha
  have hsum := hsub.add hright
  simpa only [add_zero] using hsum.congr' (Eventually.of_forall fun T => by ring)

/-- The complete moving lower far-left horizontal contribution also tends to
zero. -/
theorem tendsto_integral_farLeft_explicit_neg_height_atTop
    {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) (a : ℝ → ℝ)
    (ha : ∀ᶠ T in atTop, a T ≤ -ε) :
    Tendsto
      (fun T : ℝ => ∫ σ : ℝ in a T..(-ε),
        explicitFormulaIntegrand x ((σ : ℂ) - T * I))
      atTop (𝓝 0) := by
  have hsub :=
    tendsto_integral_farLeft_explicit_sub_rightShiftedDigamma_neg_height_atTop
      hx hε a ha
  have hright :=
    tendsto_integral_farLeft_rightShiftedDigamma_neg_height_atTop hx hε a ha
  have hsum := hsub.add hright
  simpa only [add_zero] using hsum.congr' (Eventually.of_forall fun T => by ring)

end ExplicitFormulaResidues
end PrimeNumberTheorem
