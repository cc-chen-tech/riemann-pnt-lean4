import HardyTheorem.HardyPhaseDyadicSecondMoment
import HardyTheorem.HardyShortSignedMeanSquare

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

private theorem sq_le_two_sq_add_two_sq_sub (x y : ℝ) :
    x ^ 2 ≤ 2 * y ^ 2 + 2 * (x - y) ^ 2 := by
  nlinarith [sq_nonneg (x - 2 * y)]

/-- For every fixed short-window length at least one, the signed Hardy short
integral has second moment `O(T)` on the interior of a dyadic interval. -/
theorem exists_integral_hardyShortIntegral_sq_le_mul
    (delta : ℝ) (hdelta : 1 ≤ delta) :
    ∃ C > 0, ∃ T0 : ℝ, 1 ≤ T0 ∧ ∀ T ≥ T0,
      (∫ t in T..2 * T - delta, (hardyShortIntegral delta t) ^ 2) ≤
        C * T := by
  obtain ⟨kappa, Capprox, Tapprox, hCapprox, hTapprox, happ⟩ :=
    exists_abs_hardyShortIntegral_sub_hardyFirstModelShortIntegral_le
  obtain ⟨Clinear, hClinear, Tlinear, hTlinear, hlinear⟩ :=
    exists_integral_normSq_hardyPhaseLinearizedSum_le_mul delta hdelta
  let K : ℝ := 16 * delta ^ 6 + 2 * Capprox ^ 2 * delta ^ 2
  let C : ℝ := 4 * Clinear + K
  let T0 : ℝ := max Tapprox (max Tlinear delta)
  have hdelta0 : 0 ≤ delta := zero_le_one.trans hdelta
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hT0 : 1 ≤ T0 := by
    exact hTapprox.trans (le_max_left _ _)
  refine ⟨C, hC, T0, hT0, ?_⟩
  intro T hT
  have hTapproxT : Tapprox ≤ T := (le_max_left _ _).trans hT
  have hrest : max Tlinear delta ≤ T := (le_max_right _ _).trans hT
  have hTlinearT : Tlinear ≤ T := (le_max_left _ _).trans hrest
  have hdeltaT : delta ≤ T := (le_max_right _ _).trans hrest
  have hT1 : 1 ≤ T := hT0.trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have hab : T ≤ 2 * T - delta := by linarith
  have hsqrtTpos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hsqrtTsq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hTpos.le
  have hcutoff : (firstZetaApproximationCutoff T : ℝ) ≤ 4 * T := by
    dsimp only [firstZetaApproximationCutoff]
    exact Nat.floor_le (by positivity)
  let phaseSum : ℝ → ℂ := fun t ↦
    ∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
      ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ * hardyPhaseShortIntegral n delta t
  let s : Finset ℕ := Finset.Icc 1 (firstZetaApproximationCutoff T)
  let coeff : ℝ → ℕ → ℂ := fun t n ↦
    (starRingEnd ℂ) (hardyPhaseWindowCoeff n delta t)
  let polynomial : ℝ → ℂ :=
    MathlibAux.timeDependentLogPolynomial s coeff
  have hcoeffCont : ∀ n ∈ s,
      ContinuousOn (fun t ↦ coeff t n) (Icc T (2 * T - delta)) := by
    intro n hn t ht
    dsimp only [coeff]
    exact ((hasDerivAt_hardyPhaseWindowCoeff n
      (hTpos.trans_le ht.1)).star).continuousAt.continuousWithinAt
  have hpolyCont : ContinuousOn polynomial (Icc T (2 * T - delta)) := by
    simpa only [polynomial] using
      MathlibAux.continuousOn_timeDependentLogPolynomial s coeff hcoeffCont
  have hpolyNormInt : IntervalIntegrable
      (fun t ↦ Complex.normSq (polynomial t)) volume T (2 * T - delta) :=
    (Complex.continuous_normSq.comp_continuousOn hpolyCont).intervalIntegrable_of_Icc hab
  have htrueInt : IntervalIntegrable
      (fun t ↦ (hardyShortIntegral delta t) ^ 2)
      volume T (2 * T - delta) :=
    ((continuous_hardyShortIntegral delta).pow 2).intervalIntegrable _ _
  have hconstInt : IntervalIntegrable (fun _t : ℝ ↦ K)
      volume T (2 * T - delta) :=
    continuous_const.intervalIntegrable _ _
  have hmajorantInt : IntervalIntegrable
      (fun t ↦ 4 * Complex.normSq (polynomial t) + K)
      volume T (2 * T - delta) :=
    (hpolyNormInt.const_mul 4).add hconstInt
  have hlinearPoint : ∀ t ∈ Icc T (2 * T - delta),
      Complex.normSq (hardyPhaseLinearizedSum T delta t) =
        Complex.normSq (polynomial t) := by
    intro t ht
    have htpos : 0 < t := hTpos.trans_le ht.1
    rw [normSq_hardyPhaseLinearizedSum_eq_negLogPolynomial htpos,
      hardyPhaseNegLogPolynomial_eq_conj_positive, Complex.normSq_conj]
  have hpoint : ∀ t ∈ Icc T (2 * T - delta),
      (hardyShortIntegral delta t) ^ 2 ≤
        4 * Complex.normSq (polynomial t) + K := by
    intro t ht
    have htpos : 0 < t := hTpos.trans_le ht.1
    let A : ℝ := Capprox * delta / Real.sqrt T
    let B : ℝ :=
      2 * Real.sqrt (firstZetaApproximationCutoff T) *
        (delta ^ 3 / (2 * T))
    have hA : 0 ≤ A := by
      dsimp only [A]
      positivity
    have hB : 0 ≤ B := by
      dsimp only [B]
      positivity
    have hAsqEq : A ^ 2 = Capprox ^ 2 * delta ^ 2 / T := by
      dsimp only [A]
      field_simp [hsqrtTpos.ne']
      rw [hsqrtTsq]
    have hAsq : A ^ 2 ≤ Capprox ^ 2 * delta ^ 2 := by
      rw [hAsqEq]
      apply (div_le_iff₀ hTpos).2
      exact le_mul_of_one_le_right (by positivity) hT1
    have hsqrtCutoffSq :
        (Real.sqrt (firstZetaApproximationCutoff T)) ^ 2 =
          firstZetaApproximationCutoff T :=
      Real.sq_sqrt (by positivity)
    have hBsqEq :
        B ^ 2 = (firstZetaApproximationCutoff T : ℝ) * delta ^ 6 / T ^ 2 := by
      dsimp only [B]
      rw [mul_pow, mul_pow, hsqrtCutoffSq]
      field_simp [hTpos.ne']
    have hBsq : B ^ 2 ≤ 4 * delta ^ 6 := by
      rw [hBsqEq]
      apply (div_le_iff₀ (sq_pos_of_pos hTpos)).2
      calc
        (firstZetaApproximationCutoff T : ℝ) * delta ^ 6 ≤
            (4 * T) * delta ^ 6 :=
          mul_le_mul_of_nonneg_right hcutoff (by positivity)
        _ ≤ (4 * T ^ 2) * delta ^ 6 := by
          gcongr
          nlinarith
        _ = 4 * delta ^ 6 * T ^ 2 := by ring
    have htrueError := happ T delta t hTapproxT hdelta0 ht
    have htrueErrorSq :
        (hardyShortIntegral delta t -
            hardyFirstModelShortIntegral kappa T delta t) ^ 2 ≤ A ^ 2 := by
      have hsquare := (sq_le_sq₀ (abs_nonneg _) hA).2 htrueError
      simpa only [sq_abs, A] using hsquare
    have hmodel := hardyFirstModelShortIntegral_sq_le_normSq_phase_sum
      kappa T delta t htpos hdelta0
    have hphaseUnit :
        Complex.normSq (Complex.exp (I * kappa)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_I_mul_ofReal]
      norm_num
    have hmodel' :
        (hardyFirstModelShortIntegral kappa T delta t) ^ 2 ≤
          Complex.normSq (phaseSum t) := by
      calc
        (hardyFirstModelShortIntegral kappa T delta t) ^ 2 ≤
            Complex.normSq (Complex.exp (I * kappa) * phaseSum t) := by
          simpa only [phaseSum] using hmodel
        _ = Complex.normSq (phaseSum t) := by
          rw [Complex.normSq_mul, hphaseUnit, one_mul]
    have hphaseError := norm_hardyPhaseSum_sub_linearized_le_sqrtCutoff
      hTpos ht.1 hdelta0
    have hphaseError' :
        ‖phaseSum t - hardyPhaseLinearizedSum T delta t‖ ≤ B := by
      simpa only [phaseSum, B] using hphaseError
    have hphaseNorm :
        ‖phaseSum t‖ ≤ ‖hardyPhaseLinearizedSum T delta t‖ + B := by
      calc
        ‖phaseSum t‖ =
            ‖(phaseSum t - hardyPhaseLinearizedSum T delta t) +
              hardyPhaseLinearizedSum T delta t‖ := by
          congr 1
          ring
        _ ≤ ‖phaseSum t - hardyPhaseLinearizedSum T delta t‖ +
              ‖hardyPhaseLinearizedSum T delta t‖ := norm_add_le _ _
        _ ≤ B + ‖hardyPhaseLinearizedSum T delta t‖ := by gcongr
        _ = ‖hardyPhaseLinearizedSum T delta t‖ + B := by ring
    have hphaseSq : Complex.normSq (phaseSum t) ≤
        2 * Complex.normSq (hardyPhaseLinearizedSum T delta t) + 2 * B ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      have hsquare := (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (norm_nonneg _) hB)).2 hphaseNorm
      nlinarith [sq_nonneg (‖hardyPhaseLinearizedSum T delta t‖ - B)]
    have hscaledPhaseSq :
        2 * Complex.normSq (phaseSum t) ≤
          4 * Complex.normSq (hardyPhaseLinearizedSum T delta t) +
            4 * B ^ 2 := by
      convert mul_le_mul_of_nonneg_left hphaseSq (by norm_num : (0 : ℝ) ≤ 2)
        using 1
      all_goals ring
    have herrors : 4 * B ^ 2 + 2 * A ^ 2 ≤ K := by
      dsimp only [K]
      convert add_le_add
        (mul_le_mul_of_nonneg_left hBsq (by norm_num : (0 : ℝ) ≤ 4))
        (mul_le_mul_of_nonneg_left hAsq (by norm_num : (0 : ℝ) ≤ 2)) using 1
      all_goals ring
    calc
      (hardyShortIntegral delta t) ^ 2 ≤
          2 * (hardyFirstModelShortIntegral kappa T delta t) ^ 2 +
            2 * (hardyShortIntegral delta t -
              hardyFirstModelShortIntegral kappa T delta t) ^ 2 :=
        sq_le_two_sq_add_two_sq_sub _ _
      _ ≤ 2 * (hardyFirstModelShortIntegral kappa T delta t) ^ 2 +
            2 * A ^ 2 := by gcongr
      _ ≤ 2 * Complex.normSq (phaseSum t) + 2 * A ^ 2 := by gcongr
      _ ≤ 4 * Complex.normSq (hardyPhaseLinearizedSum T delta t) +
            4 * B ^ 2 + 2 * A ^ 2 := by
        convert add_le_add_right hscaledPhaseSq (2 * A ^ 2) using 1 <;> ring
      _ ≤ 4 * Complex.normSq (hardyPhaseLinearizedSum T delta t) + K := by
        convert add_le_add_left herrors
          (4 * Complex.normSq (hardyPhaseLinearizedSum T delta t)) using 1 <;> ring
      _ = 4 * Complex.normSq (polynomial t) + K := by
        rw [hlinearPoint t ht]
  have hmono :
      (∫ t in T..2 * T - delta, (hardyShortIntegral delta t) ^ 2) ≤
        ∫ t in T..2 * T - delta,
          (4 * Complex.normSq (polynomial t) + K) :=
    intervalIntegral.integral_mono_on hab htrueInt hmajorantInt hpoint
  have hpolyLinearIntegral :
      (∫ t in T..2 * T - delta, Complex.normSq (polynomial t)) =
        ∫ t in T..2 * T - delta,
          Complex.normSq (hardyPhaseLinearizedSum T delta t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact (hlinearPoint t ht).symm
  have hlinearT := hlinear T hTlinearT
  calc
    (∫ t in T..2 * T - delta, (hardyShortIntegral delta t) ^ 2) ≤
        ∫ t in T..2 * T - delta,
          (4 * Complex.normSq (polynomial t) + K) := hmono
    _ = 4 * (∫ t in T..2 * T - delta,
          Complex.normSq (polynomial t)) + (T - delta) * K := by
      rw [intervalIntegral.integral_add (hpolyNormInt.const_mul 4) hconstInt,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ = 4 * (∫ t in T..2 * T - delta,
          Complex.normSq (hardyPhaseLinearizedSum T delta t)) +
            (T - delta) * K := by rw [hpolyLinearIntegral]
    _ ≤ 4 * (Clinear * T) + T * K := by
      gcongr
      exact sub_le_self T hdelta0
    _ = C * T := by
      dsimp only [C]
      ring

end HardyTheorem
