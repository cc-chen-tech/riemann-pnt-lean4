import HardyTheorem.SelbergSqrtZetaSignedLagIntegral
import HardyTheorem.SelbergSqrtZetaSignedModelContinuity
import HardyTheorem.SelbergSqrtZetaSignedRationalShortModel

/-!
# Actual signed short windows versus the exact rational model

The uniform first-zeta approximation is integrated over a short window.  Its
pointwise error therefore contributes at most `H` times the dyadic error.
After taking squares, the real finite model is bounded by the square norm of
the exact complex rational short model.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

private theorem sq_le_two_sq_add_two_sq_sub (x y : ℝ) :
    x ^ 2 ≤ 2 * y ^ 2 + 2 * (x - y) ^ 2 := by
  nlinarith [sq_nonneg (x - 2 * y)]

private noncomputable def actualTransferClampedPhase
    (T omega x : ℝ) : ℂ :=
  Complex.exp
    (I * ((thetaModel (max T x) + omega * max T x : ℝ) : ℂ))

private theorem continuous_actualTransferClampedPhase
    {T : ℝ} (hT : 0 < T) (omega : ℝ) :
    Continuous (actualTransferClampedPhase T omega) := by
  unfold actualTransferClampedPhase
  rw [continuous_iff_continuousAt]
  intro x
  have hmax : 0 < max T x := hT.trans_le (le_max_left T x)
  have harg : ContinuousAt (fun y : ℝ => max T y) x :=
    (continuous_const.max continuous_id).continuousAt
  have htheta : ContinuousAt (fun y : ℝ => thetaModel (max T y)) x := by
    unfold thetaModel
    fun_prop (disch := positivity)
  have hlinear : ContinuousAt (fun y : ℝ => omega * max T y) x :=
    continuousAt_const.mul harg
  exact (continuousAt_const.mul
    (Complex.continuous_ofReal.continuousAt.comp
      (htheta.add hlinear))).cexp

private noncomputable def actualTransferClampedIntegral
    (T omega H t : ℝ) : ℂ :=
  ∫ v in 0..H, actualTransferClampedPhase T omega (t + v)

private theorem continuous_actualTransferClampedIntegral
    {T : ℝ} (hT : 0 < T) (omega H : ℝ) :
    Continuous (actualTransferClampedIntegral T omega H) := by
  unfold actualTransferClampedIntegral
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_actualTransferClampedPhase hT omega).comp
    (continuous_fst.add continuous_snd)

private theorem thetaFrequencyShortIntegral_eq_actualTransferClampedIntegral
    (omega : ℝ) {T H t : ℝ}
    (hH : 0 ≤ H) (ht : T ≤ t) :
    thetaFrequencyShortIntegral omega H t =
      actualTransferClampedIntegral T omega H t := by
  unfold thetaFrequencyShortIntegral actualTransferClampedIntegral
    actualTransferClampedPhase
  apply intervalIntegral.integral_congr
  intro v hv
  have hvIcc : v ∈ Icc (0 : ℝ) H := by
    simpa [uIcc_of_le hH] using hv
  have hmax : T ≤ t + v :=
    ht.trans (le_add_of_nonneg_right hvIcc.1)
  change
    Complex.exp
        (I * ((thetaModel (t + v) + omega * (t + v) : ℝ) : ℂ)) =
      Complex.exp
        (I * ((thetaModel (max T (t + v)) +
          omega * max T (t + v) : ℝ) : ℂ))
  rw [max_eq_right hmax]

private noncomputable def actualTransferClampedRationalShortModel
    (T : ℝ) (X : ℕ) (H t : ℝ) : ℂ :=
  ∑ q ∈ selbergSqrtZetaSignedRationalSupport
      (firstZetaApproximationCutoff T) X,
    selbergSqrtZetaSignedRationalCoeff
        (firstZetaApproximationCutoff T) X q *
      actualTransferClampedIntegral T
        (selbergSqrtZetaSignedRationalFrequency q) H t

private theorem continuous_actualTransferClampedRationalShortModel
    {T : ℝ} (hT : 0 < T) (X : ℕ) (H : ℝ) :
    Continuous (actualTransferClampedRationalShortModel T X H) := by
  unfold actualTransferClampedRationalShortModel
  apply continuous_finset_sum
  intro q _hq
  exact continuous_const.mul
    (continuous_actualTransferClampedIntegral hT
      (selbergSqrtZetaSignedRationalFrequency q) H)

private theorem
    selbergSqrtZetaSignedRationalShortModel_eq_actualTransferClamped
    (T : ℝ) (X : ℕ) {H t : ℝ}
    (hH : 0 ≤ H) (ht : T ≤ t) :
    selbergSqrtZetaSignedRationalShortModel T X H t =
      actualTransferClampedRationalShortModel T X H t := by
  unfold selbergSqrtZetaSignedRationalShortModel
    actualTransferClampedRationalShortModel
  apply Finset.sum_congr rfl
  intro q _hq
  rw [thetaFrequencyShortIntegral_eq_actualTransferClampedIntegral
    (selbergSqrtZetaSignedRationalFrequency q) hH ht]

/-- The exact rational short model has an integrable squared norm on its
natural dyadic window.  This public form lets downstream carrier/noncarrier
decompositions use interval-integral monotonicity without rebuilding the
clamped continuity argument. -/
theorem
    intervalIntegrable_normSq_selbergSqrtZetaSignedRationalShortModel
    (T : ℝ) (X : ℕ) {H : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T) :
    IntervalIntegrable
      (fun t =>
        Complex.normSq
          (selbergSqrtZetaSignedRationalShortModel T X H t))
      volume T (2 * T - H) := by
  have hab : T ≤ 2 * T - H := by linarith
  have hclamped :
      IntervalIntegrable
        (fun t =>
          Complex.normSq
            (actualTransferClampedRationalShortModel T X H t))
        volume T (2 * T - H) :=
    (Complex.continuous_normSq.comp
      (continuous_actualTransferClampedRationalShortModel hT X H)
    ).intervalIntegrable _ _
  apply hclamped.congr
  intro t ht
  have htIcc : t ∈ Icc T (2 * T - H) := by
    simpa [uIcc_of_le hab] using (uIoc_subset_uIcc ht)
  change
    Complex.normSq
        (actualTransferClampedRationalShortModel T X H t) =
      Complex.normSq
        (selbergSqrtZetaSignedRationalShortModel T X H t)
  rw [selbergSqrtZetaSignedRationalShortModel_eq_actualTransferClamped
    T X hH htIcc.1]

/-- The genuine signed short-window second moment is bounded by twice the
exact rational complex-model energy plus the explicit integrated first-zeta
approximation error.  The constants are uniform in the mollifier length,
dyadic height, and admissible short-window length. -/
theorem
    exists_integral_sq_selbergSqrtZetaSignedShortIntegral_le_rationalShortModel_add_error :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H : ℝ,
        T0 ≤ T → 0 < H → H ≤ T →
          (∫ t in T..2 * T - H,
            (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) ≤
            2 * (∫ t in T..2 * T - H,
              Complex.normSq
                (selbergSqrtZetaSignedRationalShortModel T X H t)) +
            2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 := by
  obtain ⟨kappa, C, T0, hC, hT0, happ⟩ :=
    exists_abs_selbergSqrtZetaMollifiedHardyZ_sub_signedThetaModel_le_four_mul
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X hX T H hT hH hroom
  have hTpos : 0 < T :=
    zero_lt_one.trans_le (hT0.trans hT)
  have hHnonneg : 0 ≤ H := hH.le
  have hab : T ≤ 2 * T - H := by linarith
  let F : ℝ → ℝ := selbergSqrtZetaMollifiedHardyZ X
  let P : ℝ → ℝ := selbergSqrtZetaSignedThetaModel kappa T X
  let eps : ℝ := 4 * C * X / Real.sqrt T
  let E : ℝ := 4 * C * H * X / Real.sqrt T
  have heps : 0 ≤ eps := by
    dsimp only [eps]
    positivity
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hPcont :
      ContinuousOn P (Icc T (2 * T)) := by
    simpa only [P] using
      continuousOn_selbergSqrtZetaSignedThetaModel_Icc_T_two_mul_T
        kappa T X hTpos
  have hactualInt :
      IntervalIntegrable
        (fun t => (selbergSqrtZetaSignedShortIntegral X H t) ^ 2)
        volume T (2 * T - H) :=
    (continuous_selbergSqrtZetaSignedShortIntegral X H).pow 2
      |>.intervalIntegrable _ _
  have hrationalInt :=
    intervalIntegrable_normSq_selbergSqrtZetaSignedRationalShortModel
      T X hTpos hHnonneg hroom
  have hmajorInt :
      IntervalIntegrable
        (fun t =>
          2 * Complex.normSq
              (selbergSqrtZetaSignedRationalShortModel T X H t) +
            2 * E ^ 2)
        volume T (2 * T - H) :=
    (hrationalInt.const_mul 2).add
      (continuous_const.intervalIntegrable _ _)
  have hpoint : ∀ t ∈ Icc T (2 * T - H),
      (selbergSqrtZetaSignedShortIntegral X H t) ^ 2 ≤
        2 * Complex.normSq
            (selbergSqrtZetaSignedRationalShortModel T X H t) +
          2 * E ^ 2 := by
    intro t ht
    have htpos : 0 < t := hTpos.trans_le ht.1
    have hwindow : ∀ v ∈ Icc (0 : ℝ) H, t + v ∈ Icc T (2 * T) := by
      intro v hv
      constructor
      · exact ht.1.trans (le_add_of_nonneg_right hv.1)
      · linarith [ht.2, hv.2]
    have hFshiftInt :
        IntervalIntegrable (fun v => F (t + v)) volume 0 H := by
      apply ContinuousOn.intervalIntegrable_of_Icc hHnonneg
      exact (continuous_selbergSqrtZetaMollifiedHardyZ X).comp_continuousOn
        (continuousOn_const.add continuousOn_id)
    have hPshiftCont :
        ContinuousOn (fun v => P (t + v)) (Icc (0 : ℝ) H) := by
      exact hPcont.comp
        (continuousOn_const.add continuousOn_id)
        hwindow
    have hPshiftInt :
        IntervalIntegrable (fun v => P (t + v)) volume 0 H :=
      hPshiftCont.intervalIntegrable_of_Icc hHnonneg
    have hactualShift :
        selbergSqrtZetaSignedShortIntegral X H t =
          ∫ v in 0..H, F (t + v) := by
      have hshift :=
        intervalIntegral.integral_comp_add_right F t
          (a := 0) (b := H)
      unfold selbergSqrtZetaSignedShortIntegral
      change (∫ u in t..t + H, F u) =
        ∫ v in 0..H, F (t + v)
      calc
        (∫ u in t..t + H, F u) =
            ∫ v in 0..H, F (v + t) := by
          simpa only [zero_add, add_comm H t] using hshift.symm
        _ = ∫ v in 0..H, F (t + v) := by
          apply intervalIntegral.integral_congr
          intro v _hv
          change F (v + t) = F (t + v)
          rw [add_comm]
    have herrIntegral :
        |selbergSqrtZetaSignedShortIntegral X H t -
            ∫ v in 0..H, P (t + v)| ≤ E := by
      have hmajor :
          ‖∫ v in 0..H, (F (t + v) - P (t + v))‖ ≤
            eps * |H - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro v hv
        rw [uIoc_of_le hHnonneg] at hv
        have hvIcc : v ∈ Icc (0 : ℝ) H := ⟨hv.1.le, hv.2⟩
        have happAt :=
          happ X hX T (t + v) hT (hwindow v hvIcc)
        simpa only [F, P, Real.norm_eq_abs, eps] using happAt
      rw [hactualShift, ← intervalIntegral.integral_sub hFshiftInt hPshiftInt]
      calc
        |∫ v in 0..H, (F (t + v) - P (t + v))| =
            ‖∫ v in 0..H, (F (t + v) - P (t + v))‖ := by
          rw [Real.norm_eq_abs]
        _ ≤ eps * |H - 0| := hmajor
        _ = E := by
          rw [sub_zero, abs_of_nonneg hHnonneg]
          simp only [eps, E]
          ring
    have hcomplexShiftInt :
        IntervalIntegrable
          (fun v =>
            selbergSqrtZetaSignedComplexModel kappa T X (t + v))
          volume 0 H := by
      apply ContinuousOn.intervalIntegrable_of_Icc hHnonneg
      intro v hv
      apply ContinuousAt.continuousWithinAt
      unfold selbergSqrtZetaSignedComplexModel
        selbergSqrtZetaSignedPhasePolynomial
      apply continuousAt_const.mul
      apply tendsto_finset_sum
      intro p _hp
      have htv : 0 < t + v := by linarith [hv.1]
      have htheta :
          ContinuousAt (fun y : ℝ => thetaModel (t + y)) v := by
        unfold thetaModel
        fun_prop (disch := positivity)
      have hphase : ContinuousAt (fun y : ℝ =>
          thetaModel (t + y) +
            selbergSqrtZetaSignedPhaseFrequency p * (t + y)) v :=
        htheta.add
          (continuousAt_const.mul
            (continuousAt_const.add continuousAt_id))
      exact continuousAt_const.mul
        ((continuousAt_const.mul
          (Complex.continuous_ofReal.continuousAt.comp hphase)).cexp)
    have hrealIntegral :
        (∫ v in 0..H, P (t + v)) =
          (∫ v in 0..H,
            selbergSqrtZetaSignedComplexModel kappa T X (t + v)).re := by
      calc
        (∫ v in 0..H, P (t + v)) =
            ∫ v in 0..H,
              (selbergSqrtZetaSignedComplexModel kappa T X (t + v)).re := by
          apply intervalIntegral.integral_congr
          intro v _hv
          exact selbergSqrtZetaSignedThetaModel_eq_complexModel_re
            kappa T X (t + v)
        _ = (∫ v in 0..H,
              selbergSqrtZetaSignedComplexModel kappa T X (t + v)).re := by
          simpa using
            Complex.reCLM.intervalIntegral_comp_comm hcomplexShiftInt
    have hmodel :
        (∫ v in 0..H, P (t + v)) ^ 2 ≤
          Complex.normSq
            (selbergSqrtZetaSignedRationalShortModel T X H t) := by
      calc
        (∫ v in 0..H, P (t + v)) ^ 2 =
            (∫ v in 0..H,
              selbergSqrtZetaSignedComplexModel kappa T X (t + v)).re ^ 2 := by
          rw [hrealIntegral]
        _ ≤ Complex.normSq
            (∫ v in 0..H,
              selbergSqrtZetaSignedComplexModel kappa T X (t + v)) := by
          simpa only [pow_two] using
            Complex.re_sq_le_normSq
              (∫ v in 0..H,
                selbergSqrtZetaSignedComplexModel kappa T X (t + v))
        _ = Complex.normSq
            (selbergSqrtZetaSignedRationalShortModel T X H t) :=
          normSq_integral_selbergSqrtZetaSignedComplexModel_shift_eq_rationalShortModel
            kappa T X htpos hHnonneg
    have herrSq :
        (selbergSqrtZetaSignedShortIntegral X H t -
          ∫ v in 0..H, P (t + v)) ^ 2 ≤ E ^ 2 := by
      have hsquare :=
        (sq_le_sq₀
          (abs_nonneg
            (selbergSqrtZetaSignedShortIntegral X H t -
              ∫ v in 0..H, P (t + v)))
          hE).2 herrIntegral
      simpa only [sq_abs] using hsquare
    calc
      (selbergSqrtZetaSignedShortIntegral X H t) ^ 2 ≤
          2 * (∫ v in 0..H, P (t + v)) ^ 2 +
            2 * (selbergSqrtZetaSignedShortIntegral X H t -
              ∫ v in 0..H, P (t + v)) ^ 2 :=
        sq_le_two_sq_add_two_sq_sub _ _
      _ ≤
          2 * Complex.normSq
              (selbergSqrtZetaSignedRationalShortModel T X H t) +
            2 * E ^ 2 := by
        gcongr
  have hmono :
      (∫ t in T..2 * T - H,
        (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) ≤
        ∫ t in T..2 * T - H,
          (2 * Complex.normSq
              (selbergSqrtZetaSignedRationalShortModel T X H t) +
            2 * E ^ 2) :=
    intervalIntegral.integral_mono_on
      hab hactualInt hmajorInt hpoint
  calc
    (∫ t in T..2 * T - H,
        (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) ≤
        ∫ t in T..2 * T - H,
          (2 * Complex.normSq
              (selbergSqrtZetaSignedRationalShortModel T X H t) +
            2 * E ^ 2) := hmono
    _ =
        2 * (∫ t in T..2 * T - H,
          Complex.normSq
            (selbergSqrtZetaSignedRationalShortModel T X H t)) +
          2 * (T - H) * E ^ 2 := by
      rw [intervalIntegral.integral_add
          (hrationalInt.const_mul 2)
          (continuous_const.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤
        2 * (∫ t in T..2 * T - H,
          Complex.normSq
            (selbergSqrtZetaSignedRationalShortModel T X H t)) +
          2 * T * E ^ 2 := by
      gcongr
      linarith
    _ =
        2 * (∫ t in T..2 * T - H,
          Complex.normSq
            (selbergSqrtZetaSignedRationalShortModel T X H t)) +
          2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 := by
      simp only [E]

end HardyTheorem
