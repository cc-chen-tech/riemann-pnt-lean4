import HardyTheorem.HardyPhaseLinearizedEnergy
import HardyTheorem.VerticalGammaAsymptotic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.NumberTheory.Harmonic.Bounds

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

/-- The slowly varying rectangular-window coefficient left after removing
the common theta phase and the logarithmic Dirichlet frequency. -/
noncomputable def hardyPhaseWindowCoeff
    (n : ℕ) (delta t : ℝ) : ℂ :=
  ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
    ∫ v in (0 : ℝ)..delta,
      Complex.exp
        (I * (((deriv thetaModel t - Real.log n) * v : ℝ) : ℂ))

namespace OscillatoryIntegral

/-- The Hardy phase is the common theta model minus the logarithmic
Dirichlet frequency. -/
theorem hardyPhase_eq_thetaModel_sub_log
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    hardyPhase n t = thetaModel t - Real.log n * t := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : 0 < t / (2 * Real.pi) := by positivity
  have hnSq : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hlog :
      Real.log (t / (2 * Real.pi * (n : ℝ) ^ 2)) =
        Real.log (t / (2 * Real.pi)) - 2 * Real.log n := by
    rw [show t / (2 * Real.pi * (n : ℝ) ^ 2) =
        (t / (2 * Real.pi)) / ((n : ℝ) ^ 2) by ring]
    rw [Real.log_div (ne_of_gt hbase) (ne_of_gt hnSq), Real.log_pow]
    norm_num
  simp only [hardyPhase, thetaModel]
  rw [hlog]
  ring

/-- The tangent frequency has the same logarithmic decomposition. -/
theorem deriv_hardyPhase_eq_deriv_thetaModel_sub_log
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    deriv (hardyPhase n) t = deriv thetaModel t - Real.log n := by
  rw [deriv_hardyPhase (Nat.ne_of_gt hn) ht, deriv_thetaModel ht]
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : 0 < t / (2 * Real.pi) := by positivity
  have hnSq : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  rw [show t / (2 * Real.pi * (n : ℝ) ^ 2) =
      (t / (2 * Real.pi)) / ((n : ℝ) ^ 2) by ring]
  rw [Real.log_div (ne_of_gt hbase) (ne_of_gt hnSq), Real.log_pow]
  norm_num
  ring

end OscillatoryIntegral

/-- Exact separation of the rapidly rotating common theta phase, the fixed
logarithmic Dirichlet frequency, and the slowly varying window coefficient. -/
theorem hardyPhaseLinearizedCoeff_eq_commonPhase_mul_windowCoeff
    {n : ℕ} (hn : 0 < n) {delta t : ℝ} (ht : 0 < t) :
    hardyPhaseLinearizedCoeff n delta t =
      Complex.exp (I * thetaModel t) *
        Complex.exp (-I * (Real.log n * t)) *
          hardyPhaseWindowCoeff n delta t := by
  rw [hardyPhaseLinearizedCoeff, hardyPhaseWindowCoeff,
    hardyPhaseLinearizedShortIntegral,
    OscillatoryIntegral.hardyPhase_eq_thetaModel_sub_log hn ht,
    OscillatoryIntegral.deriv_hardyPhase_eq_deriv_thetaModel_sub_log hn ht]
  have hexp :
      Complex.exp (I * ((thetaModel t - Real.log n * t : ℝ) : ℂ)) =
        Complex.exp (I * thetaModel t) *
          Complex.exp (-I * (Real.log n * t)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  push_cast
  ring

/-- The theta-model velocity has derivative `1 / (2t)` at positive height. -/
theorem hasDerivAt_deriv_thetaModel {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => deriv thetaModel x) (1 / (2 * t)) t := by
  let g : ℝ → ℝ := fun x =>
    (1 / 2 : ℝ) * Real.log (x / (2 * Real.pi))
  have heq : (fun x => deriv thetaModel x) =ᶠ[𝓝 t] g := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact deriv_thetaModel hx
  rw [EventuallyEq.hasDerivAt_iff heq]
  have hden : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have harg :
      HasDerivAt (fun x : ℝ => x / (2 * Real.pi))
        (1 / (2 * Real.pi)) t := by
    simpa using (hasDerivAt_id t).div_const (2 * Real.pi)
  have harg_ne : t / (2 * Real.pi) ≠ 0 :=
    div_ne_zero ht.ne' hden
  have hlog := (harg.log harg_ne).const_mul (1 / 2 : ℝ)
  convert hlog using 1
  field_simp [ht.ne', hden]

/-- The exact derivative value of the slowly varying window coefficient. -/
noncomputable def hardyPhaseWindowCoeffDerivValue
    (n : ℕ) (delta t : ℝ) : ℂ :=
  ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
    ∫ v in (0 : ℝ)..delta,
      (I * ((v / (2 * t) : ℝ) : ℂ)) *
        Complex.exp
          (I * (((deriv thetaModel t - Real.log n) * v : ℝ) : ℂ))

/-- Differentiate the slowly varying rectangular window under the integral.
The only time variation is the universal theta acceleration `1 / (2t)`. -/
theorem hasDerivAt_hardyPhaseWindowCoeff
    (n : ℕ) {delta t : ℝ} (ht : 0 < t) :
    HasDerivAt (hardyPhaseWindowCoeff n delta)
      (hardyPhaseWindowCoeffDerivValue n delta t) t := by
  let F : ℝ → ℝ → ℂ := fun x v =>
    Complex.exp
      (I * (((deriv thetaModel x - Real.log n) * v : ℝ) : ℂ))
  let F' : ℝ → ℝ → ℂ := fun x v =>
    (I * ((v / (2 * x) : ℝ) : ℂ)) * F x v
  let bound : ℝ → ℝ := fun v => |v| / t
  have hs : Ioi (t / 2) ∈ 𝓝 t := by
    apply Ioi_mem_nhds
    linarith
  have hF_meas : ∀ᶠ x in 𝓝 t,
      AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc (0 : ℝ) delta)) := by
    filter_upwards [] with x
    exact Continuous.aestronglyMeasurable (by fun_prop)
  have hF_int : IntervalIntegrable (F t) volume 0 delta := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hF'_meas :
      AEStronglyMeasurable (F' t) (volume.restrict (Set.uIoc (0 : ℝ) delta)) := by
    exact Continuous.aestronglyMeasurable (by fun_prop)
  have hbound : ∀ᵐ v ∂volume, v ∈ Set.uIoc (0 : ℝ) delta →
      ∀ x ∈ Ioi (t / 2), ‖F' x v‖ ≤ bound v := by
    filter_upwards [] with v _hv x hx
    have hxpos : 0 < x := (half_pos ht).trans hx
    dsimp only [F', F, bound]
    have hnormexp :
        ‖Complex.exp
          (I * (((deriv thetaModel x - Real.log n) * v : ℝ) : ℂ))‖ = 1 :=
      Complex.norm_exp_I_mul_ofReal _
    rw [norm_mul, hnormexp]
    have hnorm : ‖I * ((v / (2 * x) : ℝ) : ℂ)‖ = |v| / (2 * x) := by
      rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_div, abs_of_pos (by positivity : 0 < 2 * x)]
    rw [hnorm, mul_one]
    have hdenle : t ≤ 2 * x := by
      have hxt : t / 2 < x := hx
      linarith
    exact div_le_div_of_nonneg_left (abs_nonneg v) ht hdenle
  have hbound_int : IntervalIntegrable bound volume 0 delta := by
    apply Continuous.intervalIntegrable
    exact continuous_abs.div_const t
  have hdiff : ∀ᵐ v ∂volume, v ∈ Set.uIoc (0 : ℝ) delta →
      ∀ x ∈ Ioi (t / 2), HasDerivAt (fun x => F x v) (F' x v) x := by
    filter_upwards [] with v _hv x hx
    have hxpos : 0 < x := (half_pos ht).trans hx
    have hvel := (hasDerivAt_deriv_thetaModel hxpos).sub_const (Real.log n)
    have hreal := (hvel.mul_const v).ofReal_comp
    have harg :
        HasDerivAt
          (fun y : ℝ => I * (((deriv thetaModel y - Real.log n) * v : ℝ) : ℂ))
          (I * ((v / (2 * x) : ℝ) : ℂ)) x := by
      convert hreal.const_mul I using 1
      · push_cast
        ring
    simpa only [F, F', mul_comm, mul_left_comm, mul_assoc] using harg.cexp
  have hparam :=
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := bound) hs hF_meas hF_int hF'_meas
      hbound hbound_int hdiff).2
  have hmul := hparam.const_mul (((n : ℂ) ^ (1 / 2 : ℂ))⁻¹)
  exact hmul

private theorem norm_inv_nat_cpow_half {n : ℕ} (hn : 0 < n) :
    ‖((n : ℂ) ^ (1 / 2 : ℂ))⁻¹‖ = (Real.sqrt n)⁻¹ := by
  rw [norm_inv, Complex.norm_natCast_cpow_of_pos hn]
  norm_num [Real.sqrt_eq_rpow]

private theorem inv_sqrt_sq_nat {n : ℕ} (hn : 0 < n) :
    ((Real.sqrt n)⁻¹) ^ 2 = ((n : ℝ))⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by exact_mod_cast hn.le : (0 : ℝ) ≤ n)]

/-- The derivative of one window coefficient is quadratically small in the
window length and decays like the reciprocal height. -/
theorem norm_deriv_hardyPhaseWindowCoeff_le
    {n : ℕ} (hn : 0 < n) {delta t : ℝ}
    (hdelta : 0 ≤ delta) (ht : 0 < t) :
    ‖deriv (hardyPhaseWindowCoeff n delta) t‖ ≤
      (Real.sqrt n)⁻¹ * delta ^ 2 / (4 * t) := by
  rw [(hasDerivAt_hardyPhaseWindowCoeff n ht).deriv,
    hardyPhaseWindowCoeffDerivValue, norm_mul, norm_inv_nat_cpow_half hn]
  have hpoint : ∀ v ∈ Set.Icc (0 : ℝ) delta,
      ‖(I * ((v / (2 * t) : ℝ) : ℂ)) *
          Complex.exp
            (I * (((deriv thetaModel t - Real.log n) * v : ℝ) : ℂ))‖ =
        v / (2 * t) := by
    intro v hv
    have hnormexp :
        ‖Complex.exp
          (I * (((deriv thetaModel t - Real.log n) * v : ℝ) : ℂ))‖ = 1 :=
      Complex.norm_exp_I_mul_ofReal _
    rw [norm_mul, hnormexp, mul_one, norm_mul, norm_I,
      one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : 0 < 2 * t), abs_of_nonneg hv.1]
  have hintNorm :
      (∫ v in (0 : ℝ)..delta,
        ‖(I * ((v / (2 * t) : ℝ) : ℂ)) *
          Complex.exp
            (I * (((deriv thetaModel t - Real.log n) * v : ℝ) : ℂ))‖) =
        delta ^ 2 / (4 * t) := by
    calc
      (∫ v in (0 : ℝ)..delta,
          ‖(I * ((v / (2 * t) : ℝ) : ℂ)) *
            Complex.exp
              (I * (((deriv thetaModel t - Real.log n) * v : ℝ) : ℂ))‖) =
          ∫ v in (0 : ℝ)..delta, v / (2 * t) := by
            apply intervalIntegral.integral_congr
            intro v hv
            apply hpoint v
            rwa [Set.uIcc_of_le hdelta] at hv
      _ = ∫ v in (0 : ℝ)..delta, (1 / (2 * t)) * v := by
        apply intervalIntegral.integral_congr
        intro v _hv
        ring
      _ = (1 / (2 * t)) * ∫ v in (0 : ℝ)..delta, v := by
        exact intervalIntegral.integral_const_mul _ _
      _ = delta ^ 2 / (4 * t) := by
        rw [integral_id]
        field_simp [ht.ne']
        ring
  calc
    (Real.sqrt n)⁻¹ *
        ‖∫ v in (0 : ℝ)..delta,
          (I * ((v / (2 * t) : ℝ) : ℂ)) *
            Complex.exp
              (I * (((deriv thetaModel t - Real.log n) * v : ℝ) : ℂ))‖ ≤
        (Real.sqrt n)⁻¹ * (delta ^ 2 / (4 * t)) := by
      gcongr
      exact (intervalIntegral.norm_integral_le_integral_norm hdelta).trans_eq hintNorm
    _ = (Real.sqrt n)⁻¹ * delta ^ 2 / (4 * t) := by
      ring

/-- Summing the squared derivative bounds gives a harmonic-energy estimate
for every finite initial Dirichlet segment. -/
theorem sum_normSq_deriv_hardyPhaseWindowCoeff_le
    {N : ℕ} {delta t : ℝ} (hdelta : 0 ≤ delta) (ht : 0 < t) :
    (∑ n ∈ Finset.Icc 1 N,
        Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) ≤
      delta ^ 4 / (16 * t ^ 2) * (1 + Real.log N) := by
  let C : ℝ := delta ^ 4 / (16 * t ^ 2)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hpoint : ∀ n ∈ Finset.Icc 1 N,
      Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t) ≤
        C * ((n : ℝ))⁻¹ := by
    intro n hnmem
    have hn : 0 < n := (Finset.mem_Icc.mp hnmem).1
    have hnorm := norm_deriv_hardyPhaseWindowCoeff_le hn hdelta ht
    rw [Complex.normSq_eq_norm_sq]
    calc
      ‖deriv (hardyPhaseWindowCoeff n delta) t‖ ^ 2 ≤
          ((Real.sqrt n)⁻¹ * delta ^ 2 / (4 * t)) ^ 2 := by
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
      _ = C * ((n : ℝ))⁻¹ := by
        dsimp only [C]
        rw [div_pow, mul_pow, inv_sqrt_sq_nat hn]
        field_simp [ht.ne']
        ring
  have hharmonic :
      (∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹) = (harmonic N : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
  calc
    (∑ n ∈ Finset.Icc 1 N,
        Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) ≤
        ∑ n ∈ Finset.Icc 1 N, C * ((n : ℝ))⁻¹ :=
      Finset.sum_le_sum hpoint
    _ = C * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
    _ = C * (harmonic N : ℝ) := by rw [hharmonic]
    _ ≤ C * (1 + Real.log N) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) hC
    _ = delta ^ 4 / (16 * t ^ 2) * (1 + Real.log N) := rfl

end HardyTheorem
