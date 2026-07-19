import HardyTheorem.CriticalLineShortDirichletUniform
import HardyTheorem.HardyShortAbsLower
import HardyTheorem.HardyShortSharpSecondMoment

open Complex MeasureTheory Set

namespace HardyTheorem

set_option maxHeartbeats 1200000

/-- Starts of fixed-length intervals on which cancellation in the signed
Hardy integral is strict. -/
def hardyGoodWindowStarts (H : ℝ) : Set ℝ :=
  {t | |hardyShortIntegral H t| < hardyShortAbsIntegral H t}

/-- A single fixed window length detects strict cancellation at all but a
fixed small proportion of starts in every sufficiently high dyadic block. -/
theorem exists_fixed_window_bad_start_measure_le :
    ∃ H : ℝ, 0 < H ∧ ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T →
        volume.real
            (Set.Icc T (2 * T - H) \ hardyGoodWindowStarts H) ≤
          T / 12 := by
  obtain ⟨Cs, hCs, hsigned⟩ :=
    exists_integral_hardyShortIntegral_sq_le_mul_delta
  obtain ⟨B, hB, hpoly⟩ :=
    exists_integral_normSq_criticalLineShortDirichletPolynomial_le_mul
  obtain ⟨Ca, Ta, hCa, hTa, habsLower⟩ :=
    exists_hardyShortAbsIntegral_ge_sub_shortDirichlet
  let H : ℝ := max 1 (384 * (Cs + B + 1))
  have hH1 : 1 ≤ H := le_max_left _ _
  have hH : 0 < H := zero_lt_one.trans_le hH1
  have hHCs : 384 * Cs ≤ H := by
    calc
      384 * Cs ≤ 384 * (Cs + B + 1) := by nlinarith
      _ ≤ H := le_max_right _ _
  have hHB : 384 * B ≤ H := by
    calc
      384 * B ≤ 384 * (Cs + B + 1) := by nlinarith
      _ ≤ H := le_max_right _ _
  obtain ⟨Ts, hTs, hsignedH⟩ := hsigned H hH1
  let T0 : ℝ :=
    max Ta (max Ts (max H (max 1 ((2 * Ca) ^ 2))))
  have hT0 : 1 ≤ T0 := by
    exact (le_max_left 1 ((2 * Ca) ^ 2)).trans
      ((le_max_right H _).trans
        ((le_max_right Ts _).trans (le_max_right Ta _)))
  refine ⟨H, hH, T0, hT0, ?_⟩
  intro T hT
  have hTaT : Ta ≤ T := (le_max_left _ _).trans hT
  have hrest : max Ts (max H (max 1 ((2 * Ca) ^ 2))) ≤ T :=
    (le_max_right Ta _).trans hT
  have hTsT : Ts ≤ T := (le_max_left _ _).trans hrest
  have hrest' : max H (max 1 ((2 * Ca) ^ 2)) ≤ T :=
    (le_max_right Ts _).trans hrest
  have hHT : H ≤ T := (le_max_left _ _).trans hrest'
  have hrest'' : max 1 ((2 * Ca) ^ 2) ≤ T :=
    (le_max_right H _).trans hrest'
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hrest''
  have hCaSqT : (2 * Ca) ^ 2 ≤ T :=
    (le_max_right 1 _).trans hrest''
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have hab : T ≤ 2 * T - H := by linarith
  have hsqrtTpos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have htwoCa : 2 * Ca ≤ Real.sqrt T := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg T)).mp
    rw [Real.sq_sqrt hTpos.le]
    exact hCaSqT
  have herror : Ca * H / Real.sqrt T ≤ H / 2 := by
    apply (div_le_iff₀ hsqrtTpos).2
    have hmul := mul_le_mul_of_nonneg_right htwoCa hH.le
    nlinarith
  have hsignedBound := hsignedH T hTsT
  have hpolyBound := hpoly T H hT1 hH.le hHT
  let N : ℕ := firstZetaApproximationCutoff T
  let I : Set ℝ := Set.Icc T (2 * T - H)
  let S : ℝ → ℝ := hardyShortIntegral H
  let Q : ℝ → ℂ := criticalLineShortDirichletPolynomial H N
  let epsilon : ℝ := H ^ 2 / 16
  let largeS : Set ℝ := {t | epsilon ≤ (S t) ^ 2}
  let largeQ : Set ℝ := {t | epsilon ≤ Complex.normSq (Q t)}
  have hScont : Continuous S := by
    simpa only [S] using continuous_hardyShortIntegral H
  have hQcont : Continuous Q := by
    change Continuous
      (MathlibAux.exponentialPolynomial (Finset.Icc 2 N)
        (criticalLineShortDirichletCoeff H) (fun n => -Real.log n))
    unfold MathlibAux.exponentialPolynomial
    apply continuous_finset_sum
    intro n hn
    fun_prop
  have hSint : Integrable (fun t => (S t) ^ 2) (volume.restrict I) := by
    change IntegrableOn (fun t => (S t) ^ 2) I volume
    exact (hScont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hQint : Integrable (fun t => Complex.normSq (Q t))
      (volume.restrict I) := by
    change IntegrableOn (fun t => Complex.normSq (Q t)) I volume
    exact (Complex.continuous_normSq.comp hQcont).continuousOn.integrableOn_compact
      isCompact_Icc
  have hSsetBound :
      (∫ t, (S t) ^ 2 ∂volume.restrict I) ≤ Cs * H * T := by
    change (∫ t in I, (S t) ^ 2) ≤ Cs * H * T
    rw [show I = Set.Icc T (2 * T - H) by rfl,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab]
    simpa only [S] using hsignedBound
  have hQsetBound :
      (∫ t, Complex.normSq (Q t) ∂volume.restrict I) ≤ B * T := by
    change (∫ t in I, Complex.normSq (Q t)) ≤ B * T
    rw [show I = Set.Icc T (2 * T - H) by rfl,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab]
    simpa only [Q, N] using hpolyBound
  have hSmarkov :
      epsilon * volume.real (largeS ∩ I) ≤ Cs * H * T := by
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (μ := volume.restrict I)
      (Filter.Eventually.of_forall fun t => sq_nonneg (S t)) hSint epsilon
    rw [measureReal_restrict_apply' measurableSet_Icc] at hmarkov
    exact hmarkov.trans hSsetBound
  have hQmarkov :
      epsilon * volume.real (largeQ ∩ I) ≤ B * T := by
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (μ := volume.restrict I)
      (Filter.Eventually.of_forall fun t => Complex.normSq_nonneg (Q t)) hQint epsilon
    rw [measureReal_restrict_apply' measurableSet_Icc] at hmarkov
    exact hmarkov.trans hQsetBound
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  have hlargeS : volume.real (largeS ∩ I) ≤ T / 24 := by
    have hHT0 : 0 ≤ H * T := mul_nonneg hH.le hTpos.le
    have hscaled := mul_le_mul_of_nonneg_right hHCs hHT0
    have hupper : Cs * H * T ≤ epsilon * (T / 24) := by
      dsimp only [epsilon]
      nlinarith
    have hmul := hSmarkov.trans hupper
    nlinarith
  have hlargeQ : volume.real (largeQ ∩ I) ≤ T / 24 := by
    have hHsq : H ≤ H ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hH1 hH.le]
    have hBsq : 384 * B ≤ H ^ 2 := hHB.trans hHsq
    have hscaled := mul_le_mul_of_nonneg_right hBsq hTpos.le
    have hupper : B * T ≤ epsilon * (T / 24) := by
      dsimp only [epsilon]
      nlinarith
    have hmul := hQmarkov.trans hupper
    nlinarith
  have hbadSubset :
      I \ hardyGoodWindowStarts H ⊆ (largeS ∩ I) ∪ (largeQ ∩ I) := by
    intro t ht
    have htI : t ∈ I := ht.1
    have hnotGood : ¬ |S t| < hardyShortAbsIntegral H t := by
      simpa only [hardyGoodWindowStarts, S, Set.mem_setOf_eq] using ht.2
    have hAbsLe : hardyShortAbsIntegral H t ≤ |S t| := le_of_not_gt hnotGood
    have hlower := habsLower T H t hTaT hH.le (by simpa only [I] using htI)
    have hhalf : H / 2 ≤ |S t| + ‖Q t‖ := by
      change H - ‖Q t‖ - Ca * H / Real.sqrt T ≤
        hardyShortAbsIntegral H t at hlower
      nlinarith
    by_cases hSlarge : H / 4 ≤ |S t|
    · left
      refine ⟨?_, htI⟩
      change epsilon ≤ (S t) ^ 2
      dsimp only [epsilon]
      nlinarith [sq_nonneg (|S t| - H / 4), sq_abs (S t)]
    · right
      have hQlarge : H / 4 ≤ ‖Q t‖ := by
        have hSsmall : |S t| < H / 4 := lt_of_not_ge hSlarge
        linarith
      refine ⟨?_, htI⟩
      change epsilon ≤ Complex.normSq (Q t)
      rw [Complex.normSq_eq_norm_sq]
      dsimp only [epsilon]
      nlinarith [sq_nonneg (‖Q t‖ - H / 4)]
  have hunion_ne_top :
      volume ((largeS ∩ I) ∪ (largeQ ∩ I)) ≠ ⊤ := by
    apply measure_ne_top_of_subset
      (union_subset inter_subset_right inter_subset_right)
    simpa only [I] using (measure_Icc_lt_top :
      volume (Set.Icc T (2 * T - H)) < ⊤).ne
  have hbadMeasure :
      volume.real (I \ hardyGoodWindowStarts H) ≤
        volume.real ((largeS ∩ I) ∪ (largeQ ∩ I)) :=
    measureReal_mono hbadSubset hunion_ne_top
  calc
    volume.real (Set.Icc T (2 * T - H) \ hardyGoodWindowStarts H) =
        volume.real (I \ hardyGoodWindowStarts H) := by rfl
    _ ≤ volume.real ((largeS ∩ I) ∪ (largeQ ∩ I)) := hbadMeasure
    _ ≤ volume.real (largeS ∩ I) + volume.real (largeQ ∩ I) :=
      measureReal_union_le _ _
    _ ≤ T / 12 := by linarith

end HardyTheorem
