import HardyTheorem.SelbergSqrtZetaSignedCollectedPhase
import HardyTheorem.SelbergSqrtZetaGoodWindowMeasure
import HardyTheorem.SelbergSqrtZetaSignedModelContinuity

/-!
# Dyadic L2 budget for the signed square-root-zeta model

The common Hardy phase has norm one.  After collecting equal arithmetic
frequencies, the standard finite exponential-polynomial mean-square estimate
therefore gives an explicit square-mass budget for the real theta model.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- The explicit diagonal-plus-gap budget for the signed theta model on
`[T, 2T]`. -/
noncomputable def selbergSqrtZetaSignedModelL2Budget
    (T : ℝ) (X : ℕ) : ℝ :=
  ∑ omega ∈
      selbergSqrtZetaSignedCollectedFrequencySupport
        (firstZetaApproximationCutoff T) X,
    ∑ nu ∈
        selbergSqrtZetaSignedCollectedFrequencySupport
          (firstZetaApproximationCutoff T) X,
      if omega = nu then
        T * Complex.normSq
          (selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X nu)
      else
        2 *
          ‖selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X omega‖ *
          ‖selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X nu‖ /
          |omega - nu|

/-- The actual-function square-mass budget obtained from the model budget and
the uniform first-zeta approximation error. -/
noncomputable def selbergSqrtZetaSignedActualL2Budget
    (C T : ℝ) (X : ℕ) : ℝ :=
  2 * selbergSqrtZetaSignedModelL2Budget T X +
    2 * T * (4 * C * X / Real.sqrt T) ^ 2

/-- The real signed theta model has square mass bounded by the explicit
collected-frequency diagonal-plus-gap budget. -/
theorem integral_sq_selbergSqrtZetaSignedThetaModel_le_modelL2Budget
    (kappa T : ℝ) (X : ℕ) (hT : 0 < T) :
    (∫ t in T..2 * T,
      selbergSqrtZetaSignedThetaModel kappa T X t ^ 2) ≤
        selbergSqrtZetaSignedModelL2Budget T X := by
  let N : ℕ := firstZetaApproximationCutoff T
  let K : Finset ℝ :=
    selbergSqrtZetaSignedCollectedFrequencySupport N X
  let a : ℝ → ℂ := fun omega => selbergSqrtZetaSignedCollectedCoeff N X omega
  let Q : ℝ → ℂ :=
    selbergSqrtZetaSignedCollectedTriplePolynomial N X
  have hTtwo : T ≤ 2 * T := by linarith
  have hmodelCont : ContinuousOn
      (selbergSqrtZetaSignedThetaModel kappa T X) (Icc T (2 * T)) :=
    continuousOn_selbergSqrtZetaSignedThetaModel_Icc_T_two_mul_T
      kappa T X hT
  have hQcont : Continuous Q := by
    dsimp only [Q]
    unfold selbergSqrtZetaSignedCollectedTriplePolynomial
      MathlibAux.collectedExponentialPolynomial
      MathlibAux.exponentialPolynomial
    fun_prop
  have hmodelInt : IntervalIntegrable
      (fun t => selbergSqrtZetaSignedThetaModel kappa T X t ^ 2)
      volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hTtwo]
    exact hmodelCont.pow 2
  have hQInt : IntervalIntegrable (fun t => Complex.normSq (Q t))
      volume T (2 * T) := by
    exact (Complex.continuous_normSq.comp hQcont).intervalIntegrable T (2 * T)
  have hpoint : ∀ t ∈ Icc T (2 * T),
      selbergSqrtZetaSignedThetaModel kappa T X t ^ 2 ≤
        Complex.normSq (Q t) := by
    intro t ht
    calc
      selbergSqrtZetaSignedThetaModel kappa T X t ^ 2 =
          (selbergSqrtZetaSignedComplexModel kappa T X t).re ^ 2 := by
            rw [selbergSqrtZetaSignedThetaModel_eq_complexModel_re]
      _ ≤ Complex.normSq
          (selbergSqrtZetaSignedComplexModel kappa T X t) := by
            simpa only [pow_two] using
              Complex.re_sq_le_normSq
                (selbergSqrtZetaSignedComplexModel kappa T X t)
      _ = Complex.normSq (Q t) := by
        have hkappa :
            Complex.normSq (Complex.exp (I * kappa)) = 1 := by
          rw [Complex.normSq_eq_norm_sq,
            Complex.norm_exp_I_mul_ofReal]
          norm_num
        have htheta :
            Complex.normSq
                (Complex.exp (I * (thetaModel t : ℂ))) = 1 := by
          rw [Complex.normSq_eq_norm_sq,
            Complex.norm_exp_I_mul_ofReal]
          norm_num
        rw [
          selbergSqrtZetaSignedComplexModel_eq_exp_mul_exp_mul_collectedTriplePolynomial]
        dsimp only [Q, N]
        rw [Complex.normSq_mul, Complex.normSq_mul]
        rw [hkappa, htheta]
        ring
  have hmean :
      (∫ t in T..2 * T, Complex.normSq (Q t)) ≤
        selbergSqrtZetaSignedModelL2Budget T X := by
    have hbase :=
      MathlibAux.integral_normSq_exponentialPolynomial_le
        K a (fun omega : ℝ => omega)
        (a := T) (b := 2 * T)
        (by
          intro omega homega nu hnu hne
          exact hne)
    simpa [Q, K, a, N,
      selbergSqrtZetaSignedCollectedTriplePolynomial,
      MathlibAux.collectedExponentialPolynomial,
      selbergSqrtZetaSignedCollectedFrequencySupport,
      selbergSqrtZetaSignedCollectedCoeff,
      selbergSqrtZetaSignedModelL2Budget,
      show 2 * T - T = T by ring] using hbase
  calc
    (∫ t in T..2 * T,
        selbergSqrtZetaSignedThetaModel kappa T X t ^ 2) ≤
        ∫ t in T..2 * T, Complex.normSq (Q t) :=
      intervalIntegral.integral_mono_on hTtwo hmodelInt hQInt hpoint
    _ ≤ selbergSqrtZetaSignedModelL2Budget T X := hmean

/-- The actual mollified Hardy function inherits an explicit dyadic square
mass bound from the finite model and the uniform approximation error. -/
theorem
    exists_integral_sq_selbergSqrtZetaMollifiedHardyZ_le_actualL2Budget :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T : ℝ, T0 ≤ T →
        (∫ t in T..2 * T,
          selbergSqrtZetaMollifiedHardyZ X t ^ 2) ≤
            selbergSqrtZetaSignedActualL2Budget C T X := by
  obtain ⟨kappa, C, T0, hC, hT0, happ⟩ :=
    exists_abs_selbergSqrtZetaMollifiedHardyZ_sub_signedThetaModel_le_four_mul
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X hX T hT
  let F : ℝ → ℝ := selbergSqrtZetaMollifiedHardyZ X
  let P : ℝ → ℝ := selbergSqrtZetaSignedThetaModel kappa T X
  let eps : ℝ := 4 * C * X / Real.sqrt T
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) (hT0.trans hT)
  have hTtwo : T ≤ 2 * T := by linarith
  have heps : 0 ≤ eps := by
    dsimp only [eps]
    positivity
  have hPcont : ContinuousOn P (Icc T (2 * T)) := by
    dsimp only [P]
    exact
      continuousOn_selbergSqrtZetaSignedThetaModel_Icc_T_two_mul_T
        kappa T X hTpos
  have hFint : IntervalIntegrable (fun t => F t ^ 2)
      volume T (2 * T) := by
    exact
      ((continuous_selbergSqrtZetaMollifiedHardyZ X).pow 2).intervalIntegrable
        T (2 * T)
  have hmajorInt : IntervalIntegrable
      (fun t => 2 * (P t ^ 2 + eps ^ 2)) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hTtwo]
    exact continuousOn_const.mul
      ((hPcont.pow 2).add continuousOn_const)
  have hpoint : ∀ t ∈ Icc T (2 * T),
      F t ^ 2 ≤ 2 * (P t ^ 2 + eps ^ 2) := by
    intro t ht
    have herr := happ X hX T t hT ht
    have herrSq : (F t - P t) ^ 2 ≤ eps ^ 2 := by
      have habsSq : |F t - P t| ^ 2 = (F t - P t) ^ 2 := sq_abs _
      nlinarith [abs_nonneg (F t - P t)]
    nlinarith [sq_nonneg ((F t - P t) - P t)]
  have hmodelMass :=
    integral_sq_selbergSqrtZetaSignedThetaModel_le_modelL2Budget
      kappa T X hTpos
  calc
    (∫ t in T..2 * T, selbergSqrtZetaMollifiedHardyZ X t ^ 2) =
        ∫ t in T..2 * T, F t ^ 2 := rfl
    _ ≤ ∫ t in T..2 * T, 2 * (P t ^ 2 + eps ^ 2) :=
      intervalIntegral.integral_mono_on hTtwo hFint hmajorInt hpoint
    _ = 2 * (∫ t in T..2 * T, P t ^ 2) +
        2 * T * eps ^ 2 := by
      have hPsqInt : IntervalIntegrable (fun t => P t ^ 2)
          volume T (2 * T) := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hTtwo]
        exact hPcont.pow 2
      have hconstInt : IntervalIntegrable (fun _t : ℝ => eps ^ 2)
          volume T (2 * T) :=
        continuous_const.intervalIntegrable T (2 * T)
      calc
        (∫ t in T..2 * T, 2 * (P t ^ 2 + eps ^ 2)) =
            2 * (∫ t in T..2 * T, P t ^ 2 + eps ^ 2) := by
              rw [intervalIntegral.integral_const_mul]
        _ = 2 * ((∫ t in T..2 * T, P t ^ 2) +
            ∫ _t in T..2 * T, eps ^ 2) := by
              rw [intervalIntegral.integral_add hPsqInt hconstInt]
        _ = 2 * (∫ t in T..2 * T, P t ^ 2) +
            2 * T * eps ^ 2 := by
              simp only [intervalIntegral.integral_const, smul_eq_mul]
              ring
    _ ≤ 2 * selbergSqrtZetaSignedModelL2Budget T X +
        2 * T * eps ^ 2 := by
      gcongr
    _ = selbergSqrtZetaSignedActualL2Budget C T X := by
      simp only [selbergSqrtZetaSignedActualL2Budget, eps]

end HardyTheorem
