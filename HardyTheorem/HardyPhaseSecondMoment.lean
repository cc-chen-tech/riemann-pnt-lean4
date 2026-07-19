import HardyTheorem.HardyShortSignedMeanSquare
import MathlibAux.SlidingIntervalCorrelation

open Complex MeasureTheory Set

namespace HardyTheorem

private noncomputable def clampedHardyPhaseExponential
    (T : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (I * OscillatoryIntegral.hardyPhase n (max T x))

private theorem continuous_clampedHardyPhaseExponential
    {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : n ≠ 0) :
    Continuous (clampedHardyPhaseExponential T n) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hmax : 0 < max T x := hT.trans_le (le_max_left T x)
  have harg : ContinuousAt (fun y : ℝ => max T y) x :=
    (continuous_const.max continuous_id).continuousAt
  have hphase : ContinuousAt
      (fun y : ℝ => OscillatoryIntegral.hardyPhase n (max T y)) x :=
    (OscillatoryIntegral.contDiffAt_hardyPhase_two hn hmax).continuousAt.comp' harg
  exact (continuousAt_const.mul
    (Complex.continuous_ofReal.continuousAt.comp hphase)).cexp

private theorem clampedHardyPhaseExponential_eq
    (n : ℕ) {T x : ℝ} (hTx : T ≤ x) :
    clampedHardyPhaseExponential T n x =
      Complex.exp (I * OscillatoryIntegral.hardyPhase n x) := by
  simp only [clampedHardyPhaseExponential, max_eq_right hTx]

private theorem hardyPhaseShortIntegral_eq_clamped
    (n : ℕ) {T delta t : ℝ} (hdelta : 0 ≤ delta) (ht : T ≤ t) :
    OscillatoryIntegral.hardyPhaseShortIntegral n delta t =
      ∫ v in 0..delta, clampedHardyPhaseExponential T n (t + v) := by
  dsimp only [OscillatoryIntegral.hardyPhaseShortIntegral]
  apply intervalIntegral.integral_congr
  intro v hv
  have hvIcc : v ∈ Icc (0 : ℝ) delta := by
    simpa [uIcc_of_le hdelta] using hv
  exact (clampedHardyPhaseExponential_eq n (by linarith [hvIcc.1])).symm

private theorem conj_clampedHardyPhaseExponential_mul_eq_correlation
    (m n : ℕ) {T t v w : ℝ}
    (ht : T ≤ t) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    (starRingEnd ℂ) (clampedHardyPhaseExponential T n (t + v)) *
        clampedHardyPhaseExponential T m (t + w) =
      Complex.exp (I *
        OscillatoryIntegral.hardyPhaseCorrelation m n w v t) := by
  rw [clampedHardyPhaseExponential_eq n (by linarith),
    clampedHardyPhaseExponential_eq m (by linarith)]
  have hconj :
      (starRingEnd ℂ)
          (Complex.exp (I * OscillatoryIntegral.hardyPhase n (t + v))) =
        Complex.exp (-I * OscillatoryIntegral.hardyPhase n (t + v)) := by
    rw [← Complex.exp_conj]
    simp
  rw [hconj, ← Complex.exp_add]
  congr 1
  dsimp only [OscillatoryIntegral.hardyPhaseCorrelation]
  push_cast
  ring

/-- The outer second-moment cross term for two Hardy phases is exactly the
threefold integral of their shifted phase correlation. -/
theorem integral_conj_hardyPhaseShortIntegral_mul_eq_triple_correlation
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {T delta : ℝ} (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hroom : delta ≤ T) :
    (∫ t in T..2 * T - delta,
      (starRingEnd ℂ)
          (OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
        OscillatoryIntegral.hardyPhaseShortIntegral m delta t) =
      ∫ v in 0..delta, ∫ w in 0..delta,
        ∫ t in T..2 * T - delta,
          Complex.exp (I *
            OscillatoryIntegral.hardyPhaseCorrelation m n w v t) := by
  have hTB : T ≤ 2 * T - delta := by linarith
  let f : ℝ → ℂ := clampedHardyPhaseExponential T n
  let g : ℝ → ℂ := clampedHardyPhaseExponential T m
  have hf : Continuous f := continuous_clampedHardyPhaseExponential hT hn
  have hg : Continuous g := continuous_clampedHardyPhaseExponential hT hm
  calc
    (∫ t in T..2 * T - delta,
        (starRingEnd ℂ)
            (OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
          OscillatoryIntegral.hardyPhaseShortIntegral m delta t) =
        ∫ t in T..2 * T - delta,
          (starRingEnd ℂ) (∫ v in 0..delta, f (t + v)) *
            (∫ w in 0..delta, g (t + w)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Icc T (2 * T - delta) := by
        simpa [uIcc_of_le hTB] using ht
      change
        (starRingEnd ℂ)
              (OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
            OscillatoryIntegral.hardyPhaseShortIntegral m delta t =
          (starRingEnd ℂ)
              (∫ v in 0..delta,
                clampedHardyPhaseExponential T n (t + v)) *
            (∫ w in 0..delta,
              clampedHardyPhaseExponential T m (t + w))
      rw [hardyPhaseShortIntegral_eq_clamped n hdelta htIcc.1,
        hardyPhaseShortIntegral_eq_clamped m hdelta htIcc.1]
    _ = ∫ v in 0..delta, ∫ w in 0..delta,
        ∫ t in T..2 * T - delta,
          (starRingEnd ℂ) (f (t + v)) * g (t + w) :=
      MathlibAux.slidingIntervalCorrelation_fubini hf hg hTB hdelta
    _ = ∫ v in 0..delta, ∫ w in 0..delta,
        ∫ t in T..2 * T - delta,
          Complex.exp (I *
            OscillatoryIntegral.hardyPhaseCorrelation m n w v t) := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hvIcc : v ∈ Icc (0 : ℝ) delta := by
        simpa [uIcc_of_le hdelta] using hv
      apply intervalIntegral.integral_congr
      intro w hw
      have hwIcc : w ∈ Icc (0 : ℝ) delta := by
        simpa [uIcc_of_le hdelta] using hw
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Icc T (2 * T - delta) := by
        simpa [uIcc_of_le hTB] using ht
      dsimp only [f, g]
      exact conj_clampedHardyPhaseExponential_mul_eq_correlation
        m n htIcc.1 hvIcc.1 hwIcc.1

end HardyTheorem
