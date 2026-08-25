import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import HardyTheorem.SelbergGammaRayBound

open Real Complex Set MeasureTheory Filter Topology
open scoped FourierTransform

namespace HardyTheorem

/-!
# Complex Gaussian inverse Mellin transform

The Gaussian parameter on Selberg's right contour lies in the first
quadrant.  We therefore rotate Euler's Gamma ray before applying the
real-radius Mellin inversion theorem.  The rotation phase cancels the
principal-power phase exactly.
-/

/-- The exponential whose Mellin transform is a phase times `Gamma`. -/
noncomputable def selbergRotatedExponential (phi x : ℝ) : ℂ :=
  Complex.exp (-Complex.exp ((phi : ℂ) * I) * (x : ℂ))

/-- Rotation of Euler's ray identifies the Mellin transform of the rotated
exponential. -/
theorem mellin_selbergRotatedExponential
    {phi : ℝ} {s : ℂ} (hphi0 : 0 ≤ phi)
    (hphiPi : phi < Real.pi / 2) (hs : 0 < s.re) :
    mellin (selbergRotatedExponential phi) s =
      Complex.exp (-I * (phi : ℂ) * s) * Complex.Gamma s := by
  rw [mellin_eq_fourier, Real.fourier_eq']
  rw [← MeasureTheory.integral_neg_eq_self _ volume]
  calc
    (∫ x : ℝ, Complex.exp
          ((-2 * Real.pi * inner ℝ (-x) (s.im / (2 * Real.pi)) : ℝ) * I) •
        (Real.exp (-s.re * (-x)) •
          selbergRotatedExponential phi (Real.exp (-(-x))))) =
      ∫ x : ℝ, Complex.exp (-I * (phi : ℂ) * s) *
        gammaLogKernel s ((x : ℂ) + (phi : ℂ) * I) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp [selbergRotatedExponential, gammaLogKernel, smul_eq_mul, inner]
      simp only [← Complex.exp_add]
      congr 1
      field_simp [Real.pi_ne_zero]
      apply Complex.ext <;> norm_num <;> ring
    _ = Complex.exp (-I * (phi : ℂ) * s) *
        (∫ x : ℝ, gammaLogKernel s ((x : ℂ) + (phi : ℂ) * I)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = Complex.exp (-I * (phi : ℂ) * s) * Complex.Gamma s := by
      rw [integral_gammaLogKernel_shift_eq_Gamma s hphi0 hphiPi hs]

/-- A two-sided real exponential is integrable. -/
theorem integrable_exp_neg_mul_abs {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => Real.exp (-b * |t|)) := by
  have hleft0 := integrableOn_exp_mul_Iic (a := b) hb 0
  have hleft : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|))
      (Set.Iic 0) := by
    apply hleft0.congr_fun
    · intro t ht
      simp only [mem_Iic] at ht
      change Real.exp (b * t) = Real.exp (-b * |t|)
      rw [abs_of_nonpos ht]
      congr 1
      ring
    · exact measurableSet_Iic
  have hright0 := integrableOn_exp_mul_Ioi (a := -b) (by linarith) 0
  have hright : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|))
      (Set.Ioi 0) := by
    apply hright0.congr_fun
    · intro t ht
      change Real.exp (-b * t) = Real.exp (-b * |t|)
      rw [abs_of_pos (Set.mem_Ioi.mp ht)]
    · exact measurableSet_Ioi
  have hunion : Set.Iic (0 : ℝ) ∪ Set.Ioi 0 = Set.univ := by
    ext t
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt t 0
  rw [← integrableOn_univ, ← hunion]
  exact hleft.union hright

/-- Principal logarithm of a polar point in the principal angular range. -/
theorem log_polar
    {r phi : ℝ} (hr : 0 < r)
    (hphiLow : -Real.pi < phi) (hphiHigh : phi ≤ Real.pi) :
    Complex.log
      ((r : ℂ) * Complex.exp ((phi : ℂ) * I)) =
      (Real.log r : ℂ) + (phi : ℂ) * I := by
  have hexp :
      (r : ℂ) * Complex.exp ((phi : ℂ) * I) =
        Complex.exp ((Real.log r : ℂ) + (phi : ℂ) * I) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
  rw [hexp, Complex.log_exp]
  · simpa using hphiLow
  · simpa using hphiHigh

/-- Principal powers split into radial and angular factors in the principal
angular range. -/
theorem polar_cpow_neg
    {r phi : ℝ} (hr : 0 < r)
    (hphiLow : -Real.pi < phi) (hphiHigh : phi ≤ Real.pi)
    (s : ℂ) :
    ((r : ℂ) * Complex.exp ((phi : ℂ) * I)) ^ (-s) =
      (r : ℂ) ^ (-s) * Complex.exp (-I * (phi : ℂ) * s) := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hpolar0 : (r : ℂ) * Complex.exp ((phi : ℂ) * I) ≠ 0 :=
    mul_ne_zero hr0 (Complex.exp_ne_zero _)
  rw [Complex.cpow_def_of_ne_zero hpolar0,
    Complex.cpow_def_of_ne_zero hr0,
    log_polar hr hphiLow hphiHigh]
  rw [← Complex.ofReal_log hr.le]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The Mellin transform of the rotated exponential is absolutely integrable
on the line `Re(s)=1`. -/
theorem verticalIntegrable_mellin_selbergRotatedExponential
    {phi : ℝ} (hphi0 : 0 ≤ phi)
    (hphiPi : phi < Real.pi / 2) :
    Complex.VerticalIntegrable
      (mellin (selbergRotatedExponential phi)) 1 := by
  let eta : ℝ := (phi + Real.pi / 2) / 2
  let b : ℝ := eta - phi
  let C : ℝ := Real.Gamma 1 * (Real.cos eta) ^ (-1 : ℝ)
  have heta0 : 0 ≤ eta := by
    dsimp [eta]
    linarith [Real.pi_pos]
  have hetaPi : eta < Real.pi / 2 := by
    dsimp [eta]
    linarith
  have hb : 0 < b := by
    dsimp [b, eta]
    linarith
  have hcos : 0 < Real.cos eta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hetaPi⟩
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  let g : ℝ → ℂ := fun t =>
    Complex.exp (-I * (phi : ℂ) * ((1 : ℂ) + I * t)) *
      Complex.Gamma ((1 : ℂ) + I * t)
  have hgContinuous : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro t
    have hline : ContinuousAt (fun u : ℝ => (1 : ℂ) + I * u) t := by
      fun_prop
    have hGamma : ContinuousAt Complex.Gamma ((1 : ℂ) + I * t) :=
      (Complex.differentiableAt_Gamma _ (fun m h => by
        have hre := congrArg Complex.re h
        norm_num at hre
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith)).continuousAt
    exact (by fun_prop : ContinuousAt
      (fun u : ℝ => Complex.exp (-I * (phi : ℂ) *
        ((1 : ℂ) + I * u))) t).mul
          (ContinuousAt.comp
            (f := fun u : ℝ => (1 : ℂ) + I * u) hGamma hline)
  have henv : Integrable (fun t : ℝ => C * Real.exp (-b * |t|)) :=
    (integrable_exp_neg_mul_abs hb).const_mul C
  have hg : Integrable g := by
    apply henv.mono' hgContinuous.aestronglyMeasurable
    filter_upwards with t
    let s : ℂ := (1 : ℂ) + I * t
    have hsre : s.re = 1 := by simp [s]
    have hsim : s.im = t := by simp [s]
    have hgamma :=
      norm_Gamma_le_real_Gamma_mul_cos_rpow_mul_exp_neg_abs_im
        s heta0 hetaPi (by simp [s])
    rw [hsre, hsim] at hgamma
    have hphase :
        ‖Complex.exp (-I * (phi : ℂ) * s)‖ =
          Real.exp (phi * t) := by
      rw [Complex.norm_exp]
      congr 1
      simp [s, Complex.mul_re]
    have hphaseLe : Real.exp (phi * t) ≤ Real.exp (phi * |t|) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (le_abs_self t) hphi0
    change ‖Complex.exp (-I * (phi : ℂ) * s) * Complex.Gamma s‖ ≤
      C * Real.exp (-b * |t|)
    rw [norm_mul, hphase]
    calc
      Real.exp (phi * t) * ‖Complex.Gamma s‖ ≤
          Real.exp (phi * |t|) *
            (Real.Gamma 1 * (Real.cos eta) ^ (-1 : ℝ) *
              Real.exp (-eta * |t|)) := by gcongr
      _ = C * Real.exp (-b * |t|) := by
        calc
          Real.exp (phi * |t|) *
              (Real.Gamma 1 * (Real.cos eta) ^ (-1 : ℝ) *
                Real.exp (-eta * |t|)) =
            C * (Real.exp (phi * |t|) *
              Real.exp (-eta * |t|)) := by
              dsimp [C]
              ring
          _ = C * Real.exp (-b * |t|) := by
            rw [← Real.exp_add]
            congr 2
            dsimp [b]
            ring
  apply hg.congr
  filter_upwards with t
  simpa [g, mul_comm] using
    (mellin_selbergRotatedExponential hphi0 hphiPi
      (show 0 < ((1 : ℂ) + I * t).re by simp)).symm

/-- Complex Gaussian inverse Mellin formula in polar coordinates. -/
theorem integral_Gamma_polar_cpow
    {phi r : ℝ} (hphi0 : 0 ≤ phi)
    (hphiPi : phi < Real.pi / 2) (hr : 0 < r) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ,
          Complex.Gamma ((1 : ℂ) + I * t) *
            (((r : ℂ) * Complex.exp ((phi : ℂ) * I)) ^
              (-((1 : ℂ) + I * t)))) =
      Complex.exp (-((r : ℂ) * Complex.exp ((phi : ℂ) * I))) := by
  let f := selbergRotatedExponential phi
  have hconv : MellinConvergent f (1 : ℂ) := by
    rw [MellinConvergent]
    have hcos : 0 < Real.cos phi :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hphiPi⟩
    have hInt := integrableOn_exp_mul_complex_Ioi
      (a := -Complex.exp ((phi : ℂ) * I)) (by
        rw [Complex.exp_mul_I, ← Complex.ofReal_cos,
          ← Complex.ofReal_sin]
        simp only [Complex.neg_re, Complex.add_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, one_mul, sub_zero]
        linarith) 0
    simpa [f, selbergRotatedExponential] using hInt
  have hvert : Complex.VerticalIntegrable (mellin f) 1 :=
    verticalIntegrable_mellin_selbergRotatedExponential hphi0 hphiPi
  have hinv := mellinInv_mellin_eq (1 : ℝ) f hr hconv hvert
    (by
      dsimp [f]
      unfold selbergRotatedExponential
      fun_prop)
  rw [mellinInv] at hinv
  have hphiLow : -Real.pi < phi := by linarith [Real.pi_pos]
  have hphiHigh : phi ≤ Real.pi := by linarith [Real.pi_pos]
  have htarget :
      Complex.exp (-((r : ℂ) * Complex.exp ((phi : ℂ) * I))) = f r := by
    dsimp [f, selbergRotatedExponential]
    congr 1
    ring
  rw [htarget]
  rw [← hinv]
  rw [Complex.real_smul]
  push_cast
  apply congrArg ((1 / (2 * Real.pi) : ℂ) * ·)
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp only [f, smul_eq_mul]
  rw [show (1 : ℂ) + (t : ℂ) * I = (1 : ℂ) + I * t by ring]
  rw [mellin_selbergRotatedExponential hphi0 hphiPi
      (show 0 < ((1 : ℂ) + I * t).re by simp),
    polar_cpow_neg hr hphiLow hphiHigh]
  ring

/-- The form used on Selberg's line `Re(s)=2`, obtained from the preceding
formula by the substitution `s/2 = 1 + i t/2`. -/
theorem integral_Gamma_half_vertical_polar_cpow
    {phi r : ℝ} (hphi0 : 0 ≤ phi)
    (hphiPi : phi < Real.pi / 2) (hr : 0 < r) :
    (1 / (4 * Real.pi) : ℂ) *
        (∫ t : ℝ,
          Complex.Gamma (((2 : ℂ) + I * t) / 2) *
            (((r : ℂ) * Complex.exp ((phi : ℂ) * I)) ^
              (-(((2 : ℂ) + I * t) / 2)))) =
      Complex.exp (-((r : ℂ) * Complex.exp ((phi : ℂ) * I))) := by
  let w : ℂ := (r : ℂ) * Complex.exp ((phi : ℂ) * I)
  let g : ℝ → ℂ := fun u =>
    Complex.Gamma ((1 : ℂ) + I * u) *
      w ^ (-((1 : ℂ) + I * u))
  have hbase : (1 / (2 * Real.pi) : ℂ) * (∫ u : ℝ, g u) =
      Complex.exp (-w) := by
    simpa [w, g] using integral_Gamma_polar_cpow hphi0 hphiPi hr
  have hscale := MeasureTheory.Measure.integral_comp_mul_left g (1 / 2 : ℝ)
  have hscale' : (∫ t : ℝ, g ((1 / 2 : ℝ) * t)) =
      (2 : ℝ) • (∫ u : ℝ, g u) := by
    norm_num at hscale ⊢
    exact hscale
  have hintegral :
      (∫ t : ℝ,
        Complex.Gamma (((2 : ℂ) + I * t) / 2) *
          w ^ (-(((2 : ℂ) + I * t) / 2))) =
        (2 : ℂ) * (∫ u : ℝ, g u) := by
    calc
      _ = ∫ t : ℝ, g ((1 / 2 : ℝ) * t) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        dsimp [g]
        congr 2 <;> push_cast <;> ring
      _ = (2 : ℝ) • (∫ u : ℝ, g u) := hscale'
      _ = (2 : ℂ) * (∫ u : ℝ, g u) := by
        rw [Complex.real_smul]
        norm_num
  change (1 / (4 * Real.pi) : ℂ) *
      (∫ t : ℝ,
        Complex.Gamma (((2 : ℂ) + I * t) / 2) *
          w ^ (-(((2 : ℂ) + I * t) / 2))) = Complex.exp (-w)
  rw [hintegral, ← hbase]
  ring

end HardyTheorem
