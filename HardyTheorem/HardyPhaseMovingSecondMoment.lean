import HardyTheorem.HardyPhaseFullDerivativeEnergy
import HardyTheorem.HardyPhaseFullLinearizedEnergy
import HardyTheorem.HardyPhaseWindowPolynomial
import MathlibAux.TimeDependentLogHilbertMeasurable

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

/-- Removing the two unitary phase factors does not change the energy of one
linearized Hardy coefficient. -/
theorem normSq_hardyPhaseWindowCoeff_eq_linearizedCoeff
    {n : ℕ} (hn : 0 < n) {delta t : ℝ} (ht : 0 < t) :
    Complex.normSq (hardyPhaseWindowCoeff n delta t) =
      Complex.normSq (hardyPhaseLinearizedCoeff n delta t) := by
  rw [hardyPhaseLinearizedCoeff_eq_commonPhase_mul_windowCoeff hn ht,
    Complex.normSq_mul, Complex.normSq_mul]
  have htheta :
      Complex.normSq (Complex.exp (I * thetaModel t)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_I_mul_ofReal]
    norm_num
  have hlog :
      Complex.normSq (Complex.exp (-I * (Real.log n * t))) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have hrewrite :
        -I * ((Real.log n : ℂ) * (t : ℂ)) =
          I * ((-(Real.log n * t) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hrewrite, Complex.norm_exp_I_mul_ofReal]
    norm_num
  rw [htheta, hlog]
  ring

/-- Uniform second-moment estimate for the complete linearized Hardy short
sum on a positive height interval.  The displayed constants are obtained by
substituting the full coefficient and derivative energies into the moving
logarithmic Hilbert inequality. -/
theorem integral_normSq_hardyPhaseLinearizedSum_le
    {T delta a b q : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hdelta : 1 ≤ delta) (hq : 0 < q)
    (hcutoff : 0 < firstZetaApproximationCutoff T)
    (hscale : ∀ t ∈ Set.Icc a b, 8 ≤ hardyPhaseStationaryScale t)
    (hwindow : ∀ t ∈ Set.Icc a b,
      delta ≤ hardyPhaseStationaryScale t) :
    (∫ t in a..b, Complex.normSq (hardyPhaseLinearizedSum T delta t)) ≤
      (b - a) * (200 * delta) +
        4 * (5 * Real.pi + 4) * firstZetaApproximationCutoff T *
          (200 * delta) +
        |b - a| *
          (2 * (5 * Real.pi + 4) * firstZetaApproximationCutoff T *
            (q ^ 2 * (204 * delta ^ 4 / a ^ 2) +
              (q ^ 2)⁻¹ * (200 * delta))) := by
  let N := firstZetaApproximationCutoff T
  let s : Finset ℕ := Finset.Icc 1 N
  let coeff : ℝ → ℕ → ℂ := fun x n ↦
    (starRingEnd ℂ) (hardyPhaseWindowCoeff n delta x)
  let coeff' : ℝ → ℕ → ℂ := fun x n ↦
    deriv (fun y ↦ coeff y n) x
  have hpositive : ∀ n ∈ s, n ≠ 0 := by
    intro n hn
    have := (Finset.mem_Icc.mp hn).1
    omega
  have hupper : ∀ n ∈ s, n ≤ N := by
    intro n hn
    exact (Finset.mem_Icc.mp hn).2
  have htpos : ∀ t ∈ Set.Icc a b, 0 < t := by
    intro t ht
    exact ha.trans_le ht.1
  have hderiv : ∀ t ∈ Set.Icc a b, ∀ n ∈ s,
      HasDerivAt (fun x ↦ coeff x n) (coeff' t n) t := by
    intro t ht n hn
    have hd :=
      (hasDerivAt_hardyPhaseWindowCoeff (delta := delta) n (htpos t ht)).star
    exact hd.differentiableAt.hasDerivAt
  have hcoeffCont : ∀ n ∈ s,
      ContinuousOn (fun t ↦ coeff t n) (Set.Icc a b) := by
    intro n hn t ht
    exact ((hasDerivAt_hardyPhaseWindowCoeff n (htpos t ht)).star).continuousAt.continuousWithinAt
  have hcoeffPrimeMeas : ∀ n ∈ s,
      AEStronglyMeasurable (fun t ↦ coeff' t n)
        (volume.restrict (Set.Icc a b)) := by
    intro n hn
    dsimp only [coeff']
    exact (stronglyMeasurable_deriv (fun y ↦ coeff y n)).aestronglyMeasurable.restrict
  have henergy : ∀ t ∈ Set.Icc a b,
      (∑ n ∈ s, Complex.normSq (coeff t n)) ≤ 200 * delta := by
    intro t ht
    have hraw := sum_normSq_hardyPhaseLinearizedCoeff_full_le_mul
      s N (htpos t ht) hdelta (hscale t ht) (hwindow t ht)
        hpositive hupper
    calc
      (∑ n ∈ s, Complex.normSq (coeff t n)) =
          ∑ n ∈ s, Complex.normSq (hardyPhaseLinearizedCoeff n delta t) := by
        apply Finset.sum_congr rfl
        intro n hnmem
        have hnpos : 0 < n := Nat.pos_of_ne_zero (hpositive n hnmem)
        dsimp only [coeff]
        rw [Complex.normSq_conj]
        exact normSq_hardyPhaseWindowCoeff_eq_linearizedCoeff
          hnpos (htpos t ht)
      _ ≤ 200 * delta := hraw
  have hderivEnergy : ∀ t ∈ Set.Icc a b,
      (∑ n ∈ s, Complex.normSq (coeff' t n)) ≤
        204 * delta ^ 4 / a ^ 2 := by
    intro t ht
    have hraw := sum_normSq_deriv_hardyPhaseWindowCoeff_full_le_mul
      s N (htpos t ht) hdelta (hscale t ht) hpositive hupper
    have hta : a ^ 2 ≤ t ^ 2 := by
      nlinarith [sq_nonneg (t - a), ht.1, ha]
    have hscaleDen :
        204 * delta ^ 4 / t ^ 2 ≤ 204 * delta ^ 4 / a ^ 2 := by
      exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ha) hta
    calc
      (∑ n ∈ s, Complex.normSq (coeff' t n)) =
          ∑ n ∈ s,
            Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t) := by
        apply Finset.sum_congr rfl
        intro n hnmem
        have hd :=
          hasDerivAt_hardyPhaseWindowCoeff (delta := delta) n (htpos t ht)
        have hstar := hd.star
        dsimp only [coeff', coeff]
        change Complex.normSq
            (deriv (fun y ↦ star (hardyPhaseWindowCoeff n delta y)) t) =
          Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)
        rw [hstar.deriv, hd.deriv]
        simp only [Complex.normSq_eq_norm_sq, norm_star]
      _ ≤ 204 * delta ^ 4 / t ^ 2 := hraw
      _ ≤ 204 * delta ^ 4 / a ^ 2 := hscaleDen
  have hpoly :=
    MathlibAux.integral_normSq_timeDependentLogPolynomial_le_of_measurable
      hcutoff s coeff coeff' hpositive hupper hab hq hderiv hcoeffCont
        hcoeffPrimeMeas henergy hderivEnergy
  have hpoint : ∀ t ∈ Set.Icc a b,
      Complex.normSq (hardyPhaseLinearizedSum T delta t) =
        Complex.normSq (MathlibAux.timeDependentLogPolynomial s coeff t) := by
    intro t ht
    rw [normSq_hardyPhaseLinearizedSum_eq_negLogPolynomial (htpos t ht),
      hardyPhaseNegLogPolynomial_eq_conj_positive,
      Complex.normSq_conj]
  calc
    (∫ t in a..b, Complex.normSq (hardyPhaseLinearizedSum T delta t)) =
        ∫ t in a..b,
          Complex.normSq (MathlibAux.timeDependentLogPolynomial s coeff t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact hpoint t ht
    _ ≤ (b - a) * (200 * delta) +
        4 * (5 * Real.pi + 4) * N * (200 * delta) +
        |b - a| *
          (2 * (5 * Real.pi + 4) * N *
            (q ^ 2 * (204 * delta ^ 4 / a ^ 2) +
              (q ^ 2)⁻¹ * (200 * delta))) := hpoly
    _ = (b - a) * (200 * delta) +
        4 * (5 * Real.pi + 4) * firstZetaApproximationCutoff T *
          (200 * delta) +
        |b - a| *
          (2 * (5 * Real.pi + 4) * firstZetaApproximationCutoff T *
            (q ^ 2 * (204 * delta ^ 4 / a ^ 2) +
              (q ^ 2)⁻¹ * (200 * delta))) := by rfl

end HardyTheorem
