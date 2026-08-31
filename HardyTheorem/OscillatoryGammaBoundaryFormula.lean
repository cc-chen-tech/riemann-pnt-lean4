import HardyTheorem.OscillatoryGammaAbelLimit
import HardyTheorem.SelbergComplexGaussianMellin

open Real Complex Set MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace HardyTheorem.OscillatoryGammaBoundaryFormula

/-!
# Boundary value of the oscillatory Gamma integral

The rotated Mellin identity is rescaled so that its oscillatory frequency is
one.  The Abel limit then moves the ray to angle `pi/2`.
-/

open HardyTheorem.OscillatoryGammaAbelLimit
open HardyTheorem.OscillatoryGammaAbelTail
open HardyTheorem.OscillatoryGammaTail

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

/-- Positive-real frequency scaling for the absolutely convergent damped
whole-ray integral. -/
theorem dampedGammaNegWhole_scale
    {z : ℂ} {r c : ℝ} (hc : 0 < c) :
    dampedGammaNegWhole z c r =
      (c : ℂ) ^ (-z) * dampedGammaNegWhole z 1 (r / c) := by
  let f : ℝ → ℂ := fun t =>
    Complex.exp (-((r / c) * t)) * Complex.exp (-I * t)
  have hfun : (fun t : ℝ => f (c * t)) =
      fun t : ℝ => Complex.exp (-(r * t)) * Complex.exp (-I * (c * t)) := by
    funext t
    dsimp only [f]
    congr 2
    · push_cast
      field_simp [hc.ne']
    · push_cast
      ring
  have hscale := mellin_comp_mul_left f z hc
  rw [hfun] at hscale
  have hleft :
      mellin (fun t : ℝ =>
        Complex.exp (-(r * t)) * Complex.exp (-I * (c * t))) z =
        dampedGammaNegWhole z c r := by
    unfold mellin dampedGammaNegWhole
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [smul_eq_mul]
    ring
  have hright : mellin f z = dampedGammaNegWhole z 1 (r / c) := by
    unfold mellin dampedGammaNegWhole
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [f, smul_eq_mul, ofReal_one, one_mul]
    simp [div_eq_mul_inv]
    ring
  rw [hleft, hright] at hscale
  simpa only [smul_eq_mul] using hscale

/-- Arbitrary positive frequency follows from the unit-frequency boundary
formula by positive-real scaling and Abel-limit uniqueness. -/
theorem oscillatoryGammaNegWhole_eq_of_pos
    {z : ℂ} {c : ℝ} (hz0 : 0 < z.re) (hz1 : z.re < 1) (hc : 0 < c) :
    oscillatoryGammaNegWhole z c =
      (c : ℂ) ^ (-z) *
        (Complex.exp (-I * ((Real.pi / 2 : ℝ) : ℂ) * z) *
          Complex.Gamma z) := by
  let F : Filter ℝ := nhdsWithin 0 (Ioi 0)
  have hdivNhds : Tendsto (fun r : ℝ => r / c) F (nhds 0) := by
    have hcont : ContinuousAt (fun r : ℝ => r / c) 0 := by fun_prop
    have h : Tendsto (fun r : ℝ => r / c) F
        (nhds ((fun r : ℝ => r / c) 0)) := by
      dsimp only [F]
      exact hcont.mono_left nhdsWithin_le_nhds
    simpa using h
  have hdivPos : ∀ᶠ r : ℝ in F, r / c ∈ Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_pos hr hc
  have hdivWithin : Tendsto (fun r : ℝ => r / c) F
      (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hdivNhds, hdivPos⟩
  have hleft : Tendsto (dampedGammaNegWhole z c) F
      (nhds (oscillatoryGammaNegWhole z c)) := by
    simpa [F] using tendsto_dampedGammaNegWhole_nhdsWithin_zero hz0 hz1 hc
  have hunit : Tendsto
      (fun r : ℝ => dampedGammaNegWhole z 1 (r / c)) F
      (nhds (oscillatoryGammaNegWhole z 1)) :=
    (tendsto_dampedGammaNegWhole_nhdsWithin_zero hz0 hz1
      (by norm_num : (0 : ℝ) < 1)).comp hdivWithin
  have hscaled : Tendsto
      (fun r : ℝ => (c : ℂ) ^ (-z) *
        dampedGammaNegWhole z 1 (r / c)) F
      (nhds ((c : ℂ) ^ (-z) * oscillatoryGammaNegWhole z 1)) :=
    tendsto_const_nhds.mul hunit
  have heq : dampedGammaNegWhole z c =ᶠ[F]
      fun r : ℝ => (c : ℂ) ^ (-z) *
        dampedGammaNegWhole z 1 (r / c) := by
    exact Eventually.of_forall fun r => dampedGammaNegWhole_scale hc
  have hscaledLeft : Tendsto
      (fun r : ℝ => (c : ℂ) ^ (-z) *
        dampedGammaNegWhole z 1 (r / c)) F
      (nhds (oscillatoryGammaNegWhole z c)) :=
    hleft.congr' heq
  have hboundary : oscillatoryGammaNegWhole z c =
      (c : ℂ) ^ (-z) * oscillatoryGammaNegWhole z 1 :=
    tendsto_nhds_unique hscaledLeft hscaled
  rw [hboundary, oscillatoryGammaNegWhole_eq hz0 hz1]

/-- The positive-phase canonical whole-ray value, defined by conjugating the
negative-phase boundary value at the conjugate exponent. -/
noncomputable def oscillatoryGammaPosWhole (z : ℂ) (c : ℝ) : ℂ :=
  conj (oscillatoryGammaNegWhole (conj z) c)

/-- The positive-phase Gamma boundary formula at arbitrary positive
frequency. -/
theorem oscillatoryGammaPosWhole_eq_of_pos
    {z : ℂ} {c : ℝ} (hz0 : 0 < z.re) (hz1 : z.re < 1) (hc : 0 < c) :
    oscillatoryGammaPosWhole z c =
      (c : ℂ) ^ (-z) *
        (Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ) * z) *
          Complex.Gamma z) := by
  have hneg := oscillatoryGammaNegWhole_eq_of_pos
    (z := conj z) (c := c) (by simpa) (by simpa) hc
  have harg : (c : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hc.le]
    exact ne_of_lt Real.pi_pos
  have hpow : conj ((c : ℂ) ^ (-conj z)) = (c : ℂ) ^ (-z) := by
    have h := congrArg conj
      (Complex.cpow_conj (c : ℂ) (-z) harg)
    simpa using h
  have hphase_general (a : ℝ) :
      conj (Complex.exp (-I * (a : ℂ) * conj z)) =
        Complex.exp (I * (a : ℂ) * z) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, conj_I, Complex.conj_ofReal,
      Complex.conj_conj]
    ring
  have hphase := hphase_general (Real.pi / 2)
  unfold oscillatoryGammaPosWhole
  rw [hneg, map_mul, map_mul, hpow, hphase, Complex.Gamma_conj]
  simp

private theorem intervalIntegral_gammaPos_eq_conj_neg
    {z : ℂ} {c a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ u in a..b,
      (u : ℂ) ^ (z - 1) * Complex.exp (I * (c * u))) =
      conj (∫ u in a..b,
        (u : ℂ) ^ (conj z - 1) * Complex.exp (-I * (c * u))) := by
  rw [← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with u
  intro hu
  have huIoc : u ∈ Ioc a b := by
    simpa [uIoc_of_le hab] using hu
  have hupos : 0 < u := lt_of_le_of_lt ha huIoc.1
  have harg : (u : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hupos.le]
    exact Real.pi_ne_zero.symm
  have hpow : conj ((u : ℂ) ^ (conj z - 1)) = (u : ℂ) ^ (z - 1) := by
    have h := congrArg conj
      (Complex.cpow_conj (u : ℂ) (z - 1) harg)
    simpa [Complex.conj_ofReal] using h
  have hphase : conj (Complex.exp (-I * (c * u))) =
      Complex.exp (I * (c * u)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, conj_I, Complex.conj_ofReal]
    ring
  rw [map_mul, hpow, hphase]

/-- Actual natural truncations of the positive-phase whole-ray integral. -/
noncomputable def oscillatoryGammaPosFullPartial
    (z : ℂ) (c : ℝ) (N : ℕ) : ℂ :=
  (∫ u in (0 : ℝ)..1,
    (u : ℂ) ^ (z - 1) * Complex.exp (I * (c * u))) +
      oscillatoryGammaPartial z c N

/-- The natural positive-phase truncations converge to the canonical
positive boundary value, so the conjugate definition has the intended
improper-integral semantics. -/
theorem tendsto_oscillatoryGammaPosFullPartial_atTop
    {z : ℂ} {c : ℝ} (hz1 : z.re < 1) (hc : 0 < c) :
    Tendsto (oscillatoryGammaPosFullPartial z c) atTop
      (nhds (oscillatoryGammaPosWhole z c)) := by
  have hnegTail := tendsto_oscillatoryGammaNegPartial_atTop
    (z := conj z) (c := c) (by simpa) hc
  have hnegFull : Tendsto
      (fun N : ℕ =>
        (∫ u in (0 : ℝ)..1,
          (u : ℂ) ^ (conj z - 1) * Complex.exp (-I * (c * u))) +
          oscillatoryGammaNegPartial (conj z) c N) atTop
      (nhds (oscillatoryGammaNegWhole (conj z) c)) := by
    simpa [oscillatoryGammaNegWhole] using tendsto_const_nhds.add hnegTail
  have hconj : Tendsto
      (fun N : ℕ => conj
        ((∫ u in (0 : ℝ)..1,
          (u : ℂ) ^ (conj z - 1) * Complex.exp (-I * (c * u))) +
          oscillatoryGammaNegPartial (conj z) c N)) atTop
      (nhds (oscillatoryGammaPosWhole z c)) := by
    simpa [oscillatoryGammaPosWhole, Function.comp_def] using
      (Complex.continuous_conj.tendsto
        (oscillatoryGammaNegWhole (conj z) c)).comp hnegFull
  have heq :
      (fun N : ℕ => conj
        ((∫ u in (0 : ℝ)..1,
          (u : ℂ) ^ (conj z - 1) * Complex.exp (-I * (c * u))) +
          oscillatoryGammaNegPartial (conj z) c N)) =ᶠ[atTop]
        oscillatoryGammaPosFullPartial z c := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hzero := intervalIntegral_gammaPos_eq_conj_neg
      (z := z) (c := c) (a := 0) (b := 1) (by norm_num) (by norm_num)
    have hone := intervalIntegral_gammaPos_eq_conj_neg
      (z := z) (c := c) (a := 1) (b := (N : ℝ))
      (by norm_num) (by exact_mod_cast hN)
    unfold oscillatoryGammaPosFullPartial oscillatoryGammaPartial
    rw [map_add, ← hzero]
    change _ + conj (∫ u in (1 : ℝ)..(N : ℝ),
      (u : ℂ) ^ (conj z - 1) * Complex.exp (-I * (c * u))) = _
    rw [← hone]
  exact hconj.congr' heq

end HardyTheorem.OscillatoryGammaBoundaryFormula
