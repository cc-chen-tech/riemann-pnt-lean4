import HardyTheorem.HardyPhaseSharpTwoBandSecondMoment
import HardyTheorem.HardyShortSignedMeanSquare

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

set_option maxHeartbeats 1200000

private theorem sq_le_two_sq_add_two_sq_sub (x y : ℝ) :
    x ^ 2 ≤ 2 * y ^ 2 + 2 * (x - y) ^ 2 := by
  nlinarith [sq_nonneg (x - 2 * y)]

/-- There is a universal second-moment constant for the genuine signed Hardy
short integral. The height threshold may depend on the fixed window length,
but the constant multiplying `delta * T` does not. -/
theorem exists_integral_hardyShortIntegral_sq_le_mul_delta :
    ∃ C : ℝ, 0 < C ∧
      ∀ delta : ℝ, 1 ≤ delta →
        ∃ T0 : ℝ, 1 ≤ T0 ∧ ∀ T ≥ T0,
          (∫ t in T..2 * T - delta, (hardyShortIntegral delta t) ^ 2) ≤
            C * delta * T := by
  obtain ⟨kappa, Capprox, Tapprox, hCapprox, hTapprox, happ⟩ :=
    exists_abs_hardyShortIntegral_sub_hardyFirstModelShortIntegral_le
  obtain ⟨Alinear, Blinear, hAlinear, hBlinear, hlinear⟩ :=
    exists_integral_normSq_hardyPhaseLinearizedSum_le_twoBand
  let C : ℝ :=
    4 * Alinear + 4 * Blinear + 16 + 2 * Capprox ^ 2
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro delta hdelta
  obtain ⟨Tlinear, hTlinear, hlinearT⟩ := hlinear delta hdelta
  let T0 : ℝ :=
    max Tapprox
      (max Tlinear
        (max delta (max (delta ^ 5) ((delta ^ 3 + 1) ^ 2))))
  have hT0 : 1 ≤ T0 := hTapprox.trans (le_max_left _ _)
  refine ⟨T0, hT0, ?_⟩
  intro T hT
  have hTapproxT : Tapprox ≤ T := (le_max_left _ _).trans hT
  have hrest :
      max Tlinear (max delta (max (delta ^ 5) ((delta ^ 3 + 1) ^ 2))) ≤ T :=
    (le_max_right Tapprox _).trans hT
  have hTlinearT : Tlinear ≤ T := (le_max_left _ _).trans hrest
  have hrest' :
      max delta (max (delta ^ 5) ((delta ^ 3 + 1) ^ 2)) ≤ T :=
    (le_max_right Tlinear _).trans hrest
  have hdeltaT : delta ≤ T := (le_max_left _ _).trans hrest'
  have hrest'' : max (delta ^ 5) ((delta ^ 3 + 1) ^ 2) ≤ T :=
    (le_max_right delta _).trans hrest'
  have hdeltaFiveT : delta ^ 5 ≤ T := (le_max_left _ _).trans hrest''
  have hsqrtThreshold : (delta ^ 3 + 1) ^ 2 ≤ T :=
    (le_max_right _ _).trans hrest''
  have hT1 : 1 ≤ T := hT0.trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have hdelta0 : 0 ≤ delta := zero_le_one.trans hdelta
  have hab : T ≤ 2 * T - delta := by linarith
  have hlen0 : 0 ≤ T - delta := sub_nonneg.mpr hdeltaT
  have hlenLe : T - delta ≤ T := sub_le_self T hdelta0
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
  let Aerr : ℝ := Capprox * delta / Real.sqrt T
  let Berr : ℝ :=
    2 * Real.sqrt (firstZetaApproximationCutoff T) *
      (delta ^ 3 / (2 * T))
  let Kpoint : ℝ := 4 * Berr ^ 2 + 2 * Aerr ^ 2
  have hAerr : 0 ≤ Aerr := by
    dsimp only [Aerr]
    positivity
  have hBerr : 0 ≤ Berr := by
    dsimp only [Berr]
    positivity
  have hKpoint : 0 ≤ Kpoint := by
    dsimp only [Kpoint]
    positivity
  have hAerrSq : Aerr ^ 2 = Capprox ^ 2 * delta ^ 2 / T := by
    dsimp only [Aerr]
    field_simp [hsqrtTpos.ne']
    rw [hsqrtTsq]
  have hsqrtCutoffSq :
      (Real.sqrt (firstZetaApproximationCutoff T)) ^ 2 =
        firstZetaApproximationCutoff T :=
    Real.sq_sqrt (by positivity)
  have hBerrSq :
      Berr ^ 2 =
        (firstZetaApproximationCutoff T : ℝ) * delta ^ 6 / T ^ 2 := by
    dsimp only [Berr]
    rw [mul_pow, mul_pow, hsqrtCutoffSq]
    field_simp [hTpos.ne']
  have hAerrIntegrated : T * Aerr ^ 2 = Capprox ^ 2 * delta ^ 2 := by
    rw [hAerrSq]
    field_simp [hTpos.ne']
  have hBerrIntegrated : T * Berr ^ 2 ≤ 4 * delta ^ 6 := by
    rw [hBerrSq]
    calc
      T *
          ((firstZetaApproximationCutoff T : ℝ) * delta ^ 6 / T ^ 2) =
          (firstZetaApproximationCutoff T : ℝ) * delta ^ 6 / T := by
        field_simp [hTpos.ne']
      _ ≤ (4 * T) * delta ^ 6 / T := by
        gcongr
      _ = 4 * delta ^ 6 := by
        field_simp [hTpos.ne']
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
  have hconstInt : IntervalIntegrable (fun _t : ℝ ↦ Kpoint)
      volume T (2 * T - delta) :=
    continuous_const.intervalIntegrable _ _
  have hmajorantInt : IntervalIntegrable
      (fun t ↦ 4 * Complex.normSq (polynomial t) + Kpoint)
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
        4 * Complex.normSq (polynomial t) + Kpoint := by
    intro t ht
    have htpos : 0 < t := hTpos.trans_le ht.1
    have htrueError := happ T delta t hTapproxT hdelta0 ht
    have htrueErrorSq :
        (hardyShortIntegral delta t -
            hardyFirstModelShortIntegral kappa T delta t) ^ 2 ≤ Aerr ^ 2 := by
      have hsquare := (sq_le_sq₀ (abs_nonneg _) hAerr).2 htrueError
      simpa only [sq_abs, Aerr] using hsquare
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
        ‖phaseSum t - hardyPhaseLinearizedSum T delta t‖ ≤ Berr := by
      simpa only [phaseSum, Berr] using hphaseError
    have hphaseNorm :
        ‖phaseSum t‖ ≤ ‖hardyPhaseLinearizedSum T delta t‖ + Berr := by
      calc
        ‖phaseSum t‖ =
            ‖(phaseSum t - hardyPhaseLinearizedSum T delta t) +
              hardyPhaseLinearizedSum T delta t‖ := by
          congr 1
          ring
        _ ≤ ‖phaseSum t - hardyPhaseLinearizedSum T delta t‖ +
              ‖hardyPhaseLinearizedSum T delta t‖ := norm_add_le _ _
        _ ≤ Berr + ‖hardyPhaseLinearizedSum T delta t‖ := by gcongr
        _ = ‖hardyPhaseLinearizedSum T delta t‖ + Berr := by ring
    have hphaseSq : Complex.normSq (phaseSum t) ≤
        2 * Complex.normSq (hardyPhaseLinearizedSum T delta t) +
          2 * Berr ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      have hsquare := (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (norm_nonneg _) hBerr)).2 hphaseNorm
      nlinarith [sq_nonneg (‖hardyPhaseLinearizedSum T delta t‖ - Berr)]
    have hscaledPhaseSq :
        2 * Complex.normSq (phaseSum t) ≤
          4 * Complex.normSq (hardyPhaseLinearizedSum T delta t) +
            4 * Berr ^ 2 := by
      convert mul_le_mul_of_nonneg_left hphaseSq (by norm_num : (0 : ℝ) ≤ 2)
        using 1
      all_goals ring
    calc
      (hardyShortIntegral delta t) ^ 2 ≤
          2 * (hardyFirstModelShortIntegral kappa T delta t) ^ 2 +
            2 * (hardyShortIntegral delta t -
              hardyFirstModelShortIntegral kappa T delta t) ^ 2 :=
        sq_le_two_sq_add_two_sq_sub _ _
      _ ≤ 2 * (hardyFirstModelShortIntegral kappa T delta t) ^ 2 +
            2 * Aerr ^ 2 := by gcongr
      _ ≤ 2 * Complex.normSq (phaseSum t) + 2 * Aerr ^ 2 := by gcongr
      _ ≤ 4 * Complex.normSq (hardyPhaseLinearizedSum T delta t) +
            4 * Berr ^ 2 + 2 * Aerr ^ 2 := by
        convert add_le_add_right hscaledPhaseSq (2 * Aerr ^ 2) using 1 <;> ring
      _ = 4 * Complex.normSq (polynomial t) + Kpoint := by
        rw [hlinearPoint t ht]
        dsimp only [Kpoint]
        ring
  have hmono :
      (∫ t in T..2 * T - delta, (hardyShortIntegral delta t) ^ 2) ≤
        ∫ t in T..2 * T - delta,
          (4 * Complex.normSq (polynomial t) + Kpoint) :=
    intervalIntegral.integral_mono_on hab htrueInt hmajorantInt hpoint
  have hpolyLinearIntegral :
      (∫ t in T..2 * T - delta, Complex.normSq (polynomial t)) =
        ∫ t in T..2 * T - delta,
          Complex.normSq (hardyPhaseLinearizedSum T delta t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact (hlinearPoint t ht).symm
  have hlinearBound := hlinearT T hTlinearT
  have herrorIntegrated :
      (T - delta) * Kpoint ≤
        16 * delta ^ 6 + 2 * Capprox ^ 2 * delta ^ 2 := by
    calc
      (T - delta) * Kpoint ≤ T * Kpoint :=
        mul_le_mul_of_nonneg_right hlenLe hKpoint
      _ = 4 * (T * Berr ^ 2) + 2 * (T * Aerr ^ 2) := by
        dsimp only [Kpoint]
        ring
      _ ≤ 4 * (4 * delta ^ 6) +
          2 * (Capprox ^ 2 * delta ^ 2) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hBerrIntegrated (by norm_num))
          (le_of_eq (congrArg (fun x : ℝ ↦ 2 * x) hAerrIntegrated))
      _ = 16 * delta ^ 6 + 2 * Capprox ^ 2 * delta ^ 2 := by ring
  have hsqrtThreshold' : delta ^ 3 + 1 ≤ Real.sqrt T := by
    rw [Real.le_sqrt (by positivity) hTpos.le]
    exact hsqrtThreshold
  have hresidual :
      (delta ^ 4 + delta) * Real.sqrt T ≤ delta * T := by
    calc
      (delta ^ 4 + delta) * Real.sqrt T =
          delta * (delta ^ 3 + 1) * Real.sqrt T := by ring
      _ ≤ delta * Real.sqrt T * Real.sqrt T := by gcongr
      _ = delta * (Real.sqrt T) ^ 2 := by ring
      _ = delta * T := by rw [hsqrtTsq]
  have hdeltaSix : delta ^ 6 ≤ delta * T := by
    calc
      delta ^ 6 = delta * delta ^ 5 := by ring
      _ ≤ delta * T := by gcongr
  have hdeltaSq : delta ^ 2 ≤ delta * T := by
    calc
      delta ^ 2 = delta * delta := by ring
      _ ≤ delta * T := by gcongr
  calc
    (∫ t in T..2 * T - delta, (hardyShortIntegral delta t) ^ 2) ≤
        ∫ t in T..2 * T - delta,
          (4 * Complex.normSq (polynomial t) + Kpoint) := hmono
    _ = 4 * (∫ t in T..2 * T - delta,
          Complex.normSq (polynomial t)) + (T - delta) * Kpoint := by
      rw [intervalIntegral.integral_add (hpolyNormInt.const_mul 4) hconstInt,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ = 4 * (∫ t in T..2 * T - delta,
          Complex.normSq (hardyPhaseLinearizedSum T delta t)) +
            (T - delta) * Kpoint := by rw [hpolyLinearIntegral]
    _ ≤ 4 * (Alinear * delta * T +
          Blinear * (delta ^ 4 + delta) * Real.sqrt T) +
        (16 * delta ^ 6 + 2 * Capprox ^ 2 * delta ^ 2) := by
      gcongr
    _ ≤ 4 * (Alinear * delta * T + Blinear * (delta * T)) +
        (16 * (delta * T) + 2 * Capprox ^ 2 * (delta * T)) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        convert add_le_add_left
          (mul_le_mul_of_nonneg_left hresidual hBlinear.le)
          (Alinear * delta * T) using 1 <;> ring
      · exact add_le_add
          (mul_le_mul_of_nonneg_left hdeltaSix (by norm_num))
          (mul_le_mul_of_nonneg_left hdeltaSq (by positivity))
    _ = C * delta * T := by
      dsimp only [C]
      ring

end HardyTheorem
