import HardyTheorem.SelbergRightLineExpansion
import HardyTheorem.SelbergFourierMellinVertical
import HardyTheorem.SelbergCompletedMollified

open Complex MeasureTheory

namespace HardyTheorem

/-! # Selberg's exact S1 Fourier--Mellin identity -/

/-- The inverse unitary Fourier integral of Selberg's real completed
mollified function. -/
noncomputable def selbergInverseFourierIntegral
    (delta : ℝ) (X : ℕ) (y : ℝ) : ℂ :=
  (1 / Real.sqrt (2 * Real.pi) : ℂ) *
    (∫ t : ℝ, (selbergCompletedMollifiedF delta X t : ℂ) *
      Complex.exp (-I * (y * t : ℝ)))

/-- On the critical line, the raw Mellin integrand is exactly a constant
multiple of the inverse-Fourier integrand. -/
theorem selbergMellinRaw_criticalLine_eq_fourierIntegrand
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ) (t : ℝ) :
    selbergMellinRawIntegrand (selbergFourierZ delta y) X
        ((1 / 2 : ℂ) + I * t) =
      (-2 * Real.sqrt (2 * Real.pi) : ℂ) *
        selbergFourierZ delta y ^ (1 / 2 : ℂ) *
        (selbergCompletedMollifiedF delta X t : ℂ) *
        Complex.exp (-I * (y * t : ℝ)) := by
  let s : ℂ := (1 / 2 : ℂ) + I * t
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have hgamma0 : Gammaℝ s ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by norm_num [s])
  obtain ⟨r, hr⟩ := HardyTheorem.completedRiemannZeta_critical_line_real t
  have hcompleted : completedRiemannZeta s =
      (hardyCompletedCriticalLine t : ℂ) := by
    dsimp [hardyCompletedCriticalLine]
    rw [hr]
    norm_num [s] at hr ⊢
  have hzsplit : selbergFourierZ delta y ^ s =
      selbergFourierZ delta y ^ (1 / 2 : ℂ) *
        selbergFourierZ delta y ^ (I * t) := by
    rw [← Complex.cpow_add _ _ (selbergFourierZ_ne_zero delta y)]
  unfold selbergMellinRawIntegrand selbergMellinWeight
  rw [riemannZeta_def_of_ne_zero hs0]
  rw [div_eq_mul_inv]
  change Gammaℝ s * selbergSqrtZetaPsi X s *
      selbergSqrtZetaPsi X (1 - s) * selbergFourierZ delta y ^ s *
      (completedRiemannZeta s * (Gammaℝ s)⁻¹) = _
  rw [show Gammaℝ s * selbergSqrtZetaPsi X s *
      selbergSqrtZetaPsi X (1 - s) * selbergFourierZ delta y ^ s *
      (completedRiemannZeta s * (Gammaℝ s)⁻¹) =
      completedRiemannZeta s *
        (selbergSqrtZetaPsi X s * selbergSqrtZetaPsi X (1 - s)) *
        selbergFourierZ delta y ^ s by
    field_simp [hgamma0]]
  rw [show s = (1 / 2 : ℂ) + I * t by rfl]
  rw [show 1 - ((1 / 2 : ℂ) + I * t) =
      (1 / 2 : ℂ) - I * t by ring]
  unfold selbergSqrtZetaPsi
  rw [selbergCompletedSqrtZetaMollifier_mul_reflection_eq_normSq]
  rw [hcompleted, hzsplit,
    selbergFourierZ_cpow_I hdelta0 hdeltaPi y t]
  unfold selbergCompletedMollifiedF
  push_cast
  have hq : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)
  field_simp [hq.ne']
  unfold selbergFourierAngle
  push_cast
  ring_nf

/-- The normalized critical vertical integral is `-z^(1/2)` times the
inverse unitary Fourier integral. -/
theorem normalized_integral_selbergMellinRaw_criticalLine_eq
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ) :
    (1 / (4 * Real.pi) : ℂ) *
        (∫ t : ℝ, selbergMellinRawIntegrand
          (selbergFourierZ delta y) X ((1 / 2 : ℂ) + I * t)) =
      -selbergFourierZ delta y ^ (1 / 2 : ℂ) *
        selbergInverseFourierIntegral delta X y := by
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
    (selbergMellinRaw_criticalLine_eq_fourierIntegrand
      hdelta0 hdeltaPi y X))]
  rw [show (fun t : ℝ =>
      (-2 * Real.sqrt (2 * Real.pi) : ℂ) *
        selbergFourierZ delta y ^ (1 / 2 : ℂ) *
        (selbergCompletedMollifiedF delta X t : ℂ) *
        Complex.exp (-I * (y * t : ℝ))) =
      fun t : ℝ =>
        ((-2 * Real.sqrt (2 * Real.pi) : ℂ) *
          selbergFourierZ delta y ^ (1 / 2 : ℂ)) *
          ((selbergCompletedMollifiedF delta X t : ℂ) *
            Complex.exp (-I * (y * t : ℝ))) by
    funext t
    ring]
  rw [MeasureTheory.integral_const_mul]
  unfold selbergInverseFourierIntegral
  let q : ℝ := Real.sqrt (2 * Real.pi)
  have hq : 0 < q := by
    dsimp [q]
    exact Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)
  have hq2 : q ^ 2 = 2 * Real.pi := by
    dsimp [q]
    rw [Real.sq_sqrt]
    positivity
  have hcoef : (1 / (4 * Real.pi) : ℝ) * (-2 * q) = -1 / q := by
    field_simp [hq.ne', Real.pi_ne_zero]
    nlinarith
  have hcoefC : (1 / (4 * Real.pi) : ℂ) * (-2 * q : ℂ) =
      (-1 / q : ℝ) := by
    exact_mod_cast hcoef
  change (1 / (4 * Real.pi) : ℂ) *
      ((-2 * q : ℂ) * selbergFourierZ delta y ^ (1 / 2 : ℂ) *
        (∫ t : ℝ, (selbergCompletedMollifiedF delta X t : ℂ) *
          Complex.exp (-I * (y * t : ℝ)))) = _
  calc
    (1 / (4 * Real.pi) : ℂ) *
        ((-2 * q : ℂ) * selbergFourierZ delta y ^ (1 / 2 : ℂ) *
          (∫ t : ℝ, (selbergCompletedMollifiedF delta X t : ℂ) *
            Complex.exp (-I * (y * t : ℝ)))) =
      ((1 / (4 * Real.pi) : ℂ) * (-2 * q : ℂ)) *
        selbergFourierZ delta y ^ (1 / 2 : ℂ) *
          (∫ t : ℝ, (selbergCompletedMollifiedF delta X t : ℂ) *
            Complex.exp (-I * (y * t : ℝ))) := by ring
    _ = _ := by
      rw [hcoefC]
      rw [show Real.sqrt (2 * Real.pi) = q by rfl]
      push_cast
      ring

/-- Selberg's exact S1 inverse-Fourier formula, obtained by combining the
critical-line identity, the infinite contour shift, and the absolutely
convergent right-line theta evaluation. -/
theorem selbergS1_inverseFourier_identity
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ) :
    selbergInverseFourierIntegral delta X y =
      selbergExplicitInverseFourierKernel delta X y := by
  have hshift := normalized_integral_selbergMellinRaw_vertical_sub
    hdelta0 hdeltaPi y X
  have hright :=
    normalized_integral_selbergMellinRaw_rightLine_eq_thetaKernel
      hdelta0 hdeltaPi y X
  have hleft := normalized_integral_selbergMellinRaw_criticalLine_eq
    hdelta0 hdeltaPi y X
  have hrel :
      selbergNonconstantThetaKernel delta X y -
          (-selbergFourierZ delta y ^ (1 / 2 : ℂ) *
            selbergInverseFourierIntegral delta X y) =
        (1 / 2 : ℂ) *
          (selbergFourierZ delta y * selbergSqrtZetaPsi X 1 *
            selbergSqrtZetaPsi X 0) := by
    calc
      selbergNonconstantThetaKernel delta X y -
          (-selbergFourierZ delta y ^ (1 / 2 : ℂ) *
            selbergInverseFourierIntegral delta X y) =
        (1 / (4 * Real.pi) : ℂ) *
          ((∫ t : ℝ, selbergMellinRawIntegrand
              (selbergFourierZ delta y) X ((2 : ℂ) + I * t)) -
            (∫ t : ℝ, selbergMellinRawIntegrand
              (selbergFourierZ delta y) X
                ((1 / 2 : ℂ) + I * t))) := by
          rw [← hright, ← hleft]
          ring
      _ = _ := hshift
  let z : ℂ := selbergFourierZ delta y
  let a : ℂ := z ^ (1 / 2 : ℂ)
  have hz : z ≠ 0 := selbergFourierZ_ne_zero delta y
  have ha : a ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hz)
  have hsq : a * a = z := by
    calc
      a * a = z ^ ((1 / 2 : ℂ) + (1 / 2 : ℂ)) := by
        dsimp [a]
        rw [Complex.cpow_add _ _ hz]
      _ = z ^ (1 : ℂ) := by norm_num
      _ = z := Complex.cpow_one z
  have hneg : z ^ (-1 / 2 : ℂ) = a⁻¹ := by
    dsimp [a]
    simpa only [neg_div] using Complex.cpow_neg z (1 / 2 : ℂ)
  unfold selbergExplicitInverseFourierKernel
  change selbergInverseFourierIntegral delta X y =
    (1 / 2 : ℂ) * a * selbergSqrtZetaPsi X 1 *
      selbergSqrtZetaPsi X 0 - z ^ (-1 / 2 : ℂ) *
        selbergNonconstantThetaKernel delta X y
  rw [hneg]
  apply mul_left_cancel₀ ha
  have hrhs :
      a * ((1 / 2 : ℂ) * a * selbergSqrtZetaPsi X 1 *
          selbergSqrtZetaPsi X 0 - a⁻¹ *
            selbergNonconstantThetaKernel delta X y) =
        (1 / 2 : ℂ) * z * selbergSqrtZetaPsi X 1 *
          selbergSqrtZetaPsi X 0 -
            selbergNonconstantThetaKernel delta X y := by
    rw [mul_sub]
    rw [show a * ((1 / 2 : ℂ) * a * selbergSqrtZetaPsi X 1 *
        selbergSqrtZetaPsi X 0) =
      (1 / 2 : ℂ) * (a * a) * selbergSqrtZetaPsi X 1 *
        selbergSqrtZetaPsi X 0 by ring]
    rw [hsq]
    field_simp [ha]
  rw [hrhs]
  dsimp [a, z] at hrel ⊢
  linear_combination hrel

end HardyTheorem
