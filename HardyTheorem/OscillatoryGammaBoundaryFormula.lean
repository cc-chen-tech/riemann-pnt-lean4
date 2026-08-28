import HardyTheorem.OscillatoryGammaAbelLimit
import HardyTheorem.SelbergComplexGaussianMellin

open Real Complex Set MeasureTheory Filter Topology

namespace HardyTheorem.OscillatoryGammaBoundaryFormula

/-!
# Boundary value of the oscillatory Gamma integral

The rotated Mellin identity is rescaled so that its oscillatory frequency is
one.  The Abel limit then moves the ray to angle `pi/2`.
-/

open HardyTheorem.OscillatoryGammaAbelLimit

private theorem normalizedRotatedExponential_eq
    {eps t : ℝ} (heps0 : 0 < eps) (hepsPi : eps < Real.pi / 2) :
    Complex.exp (-(Real.tan eps * (Real.cos eps * t))) *
        Complex.exp (-I * (Real.cos eps * t)) =
      selbergRotatedExponential (Real.pi / 2 - eps) t := by
  have hcos : Real.cos eps ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hepsPi⟩)
  have htanCos : Real.tan eps * Real.cos eps = Real.sin eps := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos]
  have htanCosC :
      (Real.tan eps : ℂ) * (Real.cos eps : ℂ) = (Real.sin eps : ℂ) := by
    exact_mod_cast htanCos
  rw [selbergRotatedExponential, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Real.cos_sub, Real.sin_sub]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul,
    zero_add, sub_zero]
  rw [← Complex.exp_add]
  congr 1
  calc
    -((Real.tan eps : ℂ) * ((Real.cos eps : ℂ) * (t : ℂ))) +
        -I * ((Real.cos eps : ℂ) * (t : ℂ)) =
      -((Real.tan eps : ℂ) * (Real.cos eps : ℂ)) * (t : ℂ) -
        I * (Real.cos eps : ℂ) * (t : ℂ) := by ring
    _ = -(Real.sin eps : ℂ) * (t : ℂ) -
        I * (Real.cos eps : ℂ) * (t : ℂ) := by rw [htanCosC]
    _ = -((Real.sin eps : ℂ) + (Real.cos eps : ℂ) * I) * (t : ℂ) := by ring

/-- The damped frequency-one integral is the positive-real rescaling of the
rotated Mellin/Gamma identity. -/
theorem dampedGammaNegWhole_tan_eq
    {z : ℂ} {eps : ℝ} (heps0 : 0 < eps) (hepsPi : eps < Real.pi / 2)
    (hz0 : 0 < z.re) :
    dampedGammaNegWhole z 1 (Real.tan eps) =
      (Real.cos eps : ℂ) ^ z *
        (Complex.exp (-I * ((Real.pi / 2 - eps : ℝ) : ℂ) * z) *
          Complex.Gamma z) := by
  let f : ℝ → ℂ := fun t =>
    Complex.exp (-(Real.tan eps * t)) * Complex.exp (-I * t)
  have hcos : 0 < Real.cos eps :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hepsPi⟩
  have hphi0 : 0 ≤ Real.pi / 2 - eps := by linarith
  have hphiPi : Real.pi / 2 - eps < Real.pi / 2 := by linarith
  have hfun : (fun t : ℝ => f (Real.cos eps * t)) =
      selbergRotatedExponential (Real.pi / 2 - eps) := by
    funext t
    simpa [f] using normalizedRotatedExponential_eq
      (t := t) heps0 hepsPi
  have hscale := mellin_comp_mul_left f z hcos
  rw [hfun] at hscale
  have hfMellin : mellin f z = dampedGammaNegWhole z 1 (Real.tan eps) := by
    unfold mellin dampedGammaNegWhole
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [f, smul_eq_mul, ofReal_one, one_mul]
    ring
  rw [hfMellin] at hscale
  have hrotated := mellin_selbergRotatedExponential hphi0 hphiPi hz0
  rw [hrotated] at hscale
  simp only [smul_eq_mul] at hscale
  have hcos0 : (Real.cos eps : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hcos.ne'
  have hcancel :
      (Real.cos eps : ℂ) ^ z * (Real.cos eps : ℂ) ^ (-z) = 1 := by
    rw [Complex.cpow_neg]
    exact mul_inv_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl hcos0))
  calc
    dampedGammaNegWhole z 1 (Real.tan eps) =
        1 * dampedGammaNegWhole z 1 (Real.tan eps) := by ring
    _ = ((Real.cos eps : ℂ) ^ z * (Real.cos eps : ℂ) ^ (-z)) *
        dampedGammaNegWhole z 1 (Real.tan eps) := by rw [hcancel]
    _ = (Real.cos eps : ℂ) ^ z *
        ((Real.cos eps : ℂ) ^ (-z) *
          dampedGammaNegWhole z 1 (Real.tan eps)) := by ring
    _ = (Real.cos eps : ℂ) ^ z *
        (Complex.exp (-I * ((Real.pi / 2 - eps : ℝ) : ℂ) * z) *
          Complex.Gamma z) := by rw [← hscale]

/-- The canonical negative-phase boundary integral equals the rotated Gamma
value at angle `pi/2`. -/
theorem oscillatoryGammaNegWhole_eq
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    oscillatoryGammaNegWhole z 1 =
      Complex.exp (-I * ((Real.pi / 2 : ℝ) : ℂ) * z) *
        Complex.Gamma z := by
  let F : Filter ℝ := nhdsWithin 0 (Ioi 0)
  let R : ℝ → ℂ := fun eps =>
    (Real.cos eps : ℂ) ^ z *
      (Complex.exp (-I * ((Real.pi / 2 - eps : ℝ) : ℂ) * z) *
        Complex.Gamma z)
  have hhalf : 0 < Real.pi / 2 := half_pos Real.pi_pos
  have hepsPi : ∀ᶠ eps : ℝ in F, eps < Real.pi / 2 := by
    dsimp only [F]
    exact (eventually_lt_nhds hhalf).filter_mono nhdsWithin_le_nhds
  have htanNhds : Tendsto Real.tan F (nhds 0) := by
    have hcont : ContinuousAt Real.tan 0 :=
      Real.continuousAt_tan.mpr (by simp)
    simpa [F] using hcont.mono_left nhdsWithin_le_nhds
  have htanPos : ∀ᶠ eps : ℝ in F, Real.tan eps ∈ Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin, hepsPi] with eps heps0 hepsUpper
    exact Real.tan_pos_of_pos_of_lt_pi_div_two heps0 hepsUpper
  have htanWithin : Tendsto Real.tan F (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨htanNhds, htanPos⟩
  have hleft : Tendsto
      (fun eps : ℝ => dampedGammaNegWhole z 1 (Real.tan eps)) F
      (nhds (oscillatoryGammaNegWhole z 1)) :=
    (tendsto_dampedGammaNegWhole_nhdsWithin_zero hz0 hz1
      (by norm_num : (0 : ℝ) < 1)).comp htanWithin
  have heq :
      (fun eps : ℝ => dampedGammaNegWhole z 1 (Real.tan eps)) =ᶠ[F] R := by
    filter_upwards [self_mem_nhdsWithin, hepsPi] with eps heps0 hepsUpper
    exact dampedGammaNegWhole_tan_eq heps0 hepsUpper hz0
  have hcpow : ContinuousAt (fun eps : ℝ => (Real.cos eps : ℂ) ^ z) 0 := by
    have hpow := Complex.continuousAt_ofReal_cpow_const (1 : ℝ) z
      (Or.inr (by norm_num : (1 : ℝ) ≠ 0))
    change ContinuousAt ((fun a : ℝ => (a : ℂ) ^ z) ∘ Real.cos) 0
    exact ContinuousAt.comp_of_eq hpow Real.continuous_cos.continuousAt (by simp)
  have hrightCont : ContinuousAt R 0 := by
    dsimp only [R]
    have hphase : ContinuousAt
        (fun eps : ℝ =>
          Complex.exp (-I * ((Real.pi / 2 - eps : ℝ) : ℂ) * z)) 0 := by
      fun_prop
    exact hcpow.mul (hphase.mul continuousAt_const)
  have hright : Tendsto R F
      (nhds (Complex.exp (-I * ((Real.pi / 2 : ℝ) : ℂ) * z) *
        Complex.Gamma z)) := by
    have h : Tendsto R F (nhds (R 0)) := by
      dsimp only [F]
      exact hrightCont.mono_left nhdsWithin_le_nhds
    simpa [R] using h
  have hleftR : Tendsto R F (nhds (oscillatoryGammaNegWhole z 1)) :=
    hleft.congr' heq
  exact tendsto_nhds_unique hleftR hright

end HardyTheorem.OscillatoryGammaBoundaryFormula
