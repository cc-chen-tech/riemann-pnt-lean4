import HardyTheorem.SelbergSqrtZetaSignedRationalShortModel
import MathlibAux.SlidingIntervalCorrelation

/-!
# Exact kernel expansion for the signed rational short model

The integrated square energy of the rational short model is expanded as a
finite Hermitian double sum.  Its kernel retains the exact complex phases of
the theta-frequency short integrals; no absolute-value or frequency-gap
estimate is used in this module.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- The exact complex cross kernel for two rational frequencies. -/
noncomputable def selbergSqrtZetaSignedRationalShortKernel
    (T H : ℝ) (q r : ℚ) : ℂ :=
  ∫ t in T..2 * T - H,
    (starRingEnd ℂ)
        (thetaFrequencyShortIntegral
          (selbergSqrtZetaSignedRationalFrequency r) H t) *
      thetaFrequencyShortIntegral
        (selbergSqrtZetaSignedRationalFrequency q) H t

/-- The phase difference underlying one exact rational short kernel. -/
noncomputable def selbergSqrtZetaSignedRationalShortKernelPhase
    (q r : ℚ) (v w t : ℝ) : ℝ :=
  thetaModel (t + w) +
      selbergSqrtZetaSignedRationalFrequency q * (t + w) -
    (thetaModel (t + v) +
      selbergSqrtZetaSignedRationalFrequency r * (t + v))

private noncomputable def rationalShortKernelClampedPhase
    (T omega x : ℝ) : ℂ :=
  Complex.exp
    (I * ((thetaModel (max T x) + omega * max T x : ℝ) : ℂ))

private theorem continuous_rationalShortKernelClampedPhase
    {T : ℝ} (hT : 0 < T) (omega : ℝ) :
    Continuous (rationalShortKernelClampedPhase T omega) := by
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

private noncomputable def rationalShortKernelClampedIntegral
    (T omega H t : ℝ) : ℂ :=
  ∫ v in 0..H, rationalShortKernelClampedPhase T omega (t + v)

private theorem continuous_rationalShortKernelClampedIntegral
    {T : ℝ} (hT : 0 < T) (omega H : ℝ) :
    Continuous (rationalShortKernelClampedIntegral T omega H) := by
  unfold rationalShortKernelClampedIntegral
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_rationalShortKernelClampedPhase hT omega).comp
    (continuous_fst.add continuous_snd)

private theorem thetaFrequencyShortIntegral_eq_clamped
    (omega : ℝ) {T H t : ℝ}
    (hH : 0 ≤ H) (ht : T ≤ t) :
    thetaFrequencyShortIntegral omega H t =
      rationalShortKernelClampedIntegral T omega H t := by
  unfold thetaFrequencyShortIntegral
    rationalShortKernelClampedIntegral
    rationalShortKernelClampedPhase
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

private theorem intervalIntegrable_rationalShortKernelIntegrand
    {T H : ℝ} (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T)
    (q r : ℚ) :
    IntervalIntegrable
      (fun t : ℝ =>
        (starRingEnd ℂ)
            (thetaFrequencyShortIntegral
              (selbergSqrtZetaSignedRationalFrequency r) H t) *
          thetaFrequencyShortIntegral
            (selbergSqrtZetaSignedRationalFrequency q) H t)
      volume T (2 * T - H) := by
  let g : ℝ → ℂ := fun t =>
    (starRingEnd ℂ)
        (rationalShortKernelClampedIntegral T
          (selbergSqrtZetaSignedRationalFrequency r) H t) *
      rationalShortKernelClampedIntegral T
        (selbergSqrtZetaSignedRationalFrequency q) H t
  have hg : IntervalIntegrable g volume T (2 * T - H) := by
    apply Continuous.intervalIntegrable
    exact
      (continuous_rationalShortKernelClampedIntegral hT
        (selbergSqrtZetaSignedRationalFrequency r) H).star.mul
      (continuous_rationalShortKernelClampedIntegral hT
        (selbergSqrtZetaSignedRationalFrequency q) H)
  have hlong : T ≤ 2 * T - H := by linarith
  apply hg.congr
  intro t ht
  have htIcc : t ∈ Icc T (2 * T - H) := by
    simpa [uIcc_of_le hlong] using (uIoc_subset_uIcc ht)
  dsimp only [g]
  rw [thetaFrequencyShortIntegral_eq_clamped
      (selbergSqrtZetaSignedRationalFrequency r) hH htIcc.1,
    thetaFrequencyShortIntegral_eq_clamped
      (selbergSqrtZetaSignedRationalFrequency q) hH htIcc.1]

private theorem conj_rationalShortKernelClampedPhase_mul_eq
    (q r : ℚ) {T t v w : ℝ}
    (ht : T ≤ t) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    (starRingEnd ℂ)
        (rationalShortKernelClampedPhase T
          (selbergSqrtZetaSignedRationalFrequency r) (t + v)) *
      rationalShortKernelClampedPhase T
        (selbergSqrtZetaSignedRationalFrequency q) (t + w) =
      Complex.exp
        (I *
          ((selbergSqrtZetaSignedRationalShortKernelPhase
            q r v w t : ℝ) : ℂ)) := by
  have htv : T ≤ t + v := ht.trans (le_add_of_nonneg_right hv)
  have htw : T ≤ t + w := ht.trans (le_add_of_nonneg_right hw)
  unfold rationalShortKernelClampedPhase
  rw [max_eq_right htv, max_eq_right htw, ← Complex.exp_conj]
  simp only [map_mul, conj_I, conj_ofReal, ← Complex.exp_add]
  unfold selbergSqrtZetaSignedRationalShortKernelPhase
  push_cast
  ring

/-- The exact rational short kernel as a threefold oscillatory integral.
The two window variables remain outside the height integral, exposing the
full phase difference without taking absolute values. -/
theorem selbergSqrtZetaSignedRationalShortKernel_eq_triple
    (q r : ℚ) {T H : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T) :
    selbergSqrtZetaSignedRationalShortKernel T H q r =
      ∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        Complex.exp
          (I *
            ((selbergSqrtZetaSignedRationalShortKernelPhase
              q r v w t : ℝ) : ℂ)) := by
  have hlong : T ≤ 2 * T - H := by linarith
  let f : ℝ → ℂ :=
    rationalShortKernelClampedPhase T
      (selbergSqrtZetaSignedRationalFrequency r)
  let g : ℝ → ℂ :=
    rationalShortKernelClampedPhase T
      (selbergSqrtZetaSignedRationalFrequency q)
  have hf : Continuous f :=
    continuous_rationalShortKernelClampedPhase hT
      (selbergSqrtZetaSignedRationalFrequency r)
  have hg : Continuous g :=
    continuous_rationalShortKernelClampedPhase hT
      (selbergSqrtZetaSignedRationalFrequency q)
  calc
    selbergSqrtZetaSignedRationalShortKernel T H q r =
        ∫ t in T..2 * T - H,
          (starRingEnd ℂ) (∫ v in 0..H, f (t + v)) *
            (∫ w in 0..H, g (t + w)) := by
      unfold selbergSqrtZetaSignedRationalShortKernel
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Icc T (2 * T - H) := by
        simpa [uIcc_of_le hlong] using ht
      change
        (starRingEnd ℂ)
              (thetaFrequencyShortIntegral
                (selbergSqrtZetaSignedRationalFrequency r) H t) *
            thetaFrequencyShortIntegral
              (selbergSqrtZetaSignedRationalFrequency q) H t =
          (starRingEnd ℂ)
              (∫ v in 0..H,
                rationalShortKernelClampedPhase T
                  (selbergSqrtZetaSignedRationalFrequency r) (t + v)) *
            (∫ w in 0..H,
              rationalShortKernelClampedPhase T
                (selbergSqrtZetaSignedRationalFrequency q) (t + w))
      rw [thetaFrequencyShortIntegral_eq_clamped
          (selbergSqrtZetaSignedRationalFrequency r) hH htIcc.1,
        thetaFrequencyShortIntegral_eq_clamped
          (selbergSqrtZetaSignedRationalFrequency q) hH htIcc.1]
      rfl
    _ = ∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
          (starRingEnd ℂ) (f (t + v)) * g (t + w) :=
      MathlibAux.slidingIntervalCorrelation_fubini hf hg hlong hH
    _ = ∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        Complex.exp
          (I *
            ((selbergSqrtZetaSignedRationalShortKernelPhase
              q r v w t : ℝ) : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hvIcc : v ∈ Icc (0 : ℝ) H := by
        simpa [uIcc_of_le hH] using hv
      apply intervalIntegral.integral_congr
      intro w hw
      have hwIcc : w ∈ Icc (0 : ℝ) H := by
        simpa [uIcc_of_le hH] using hw
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Icc T (2 * T - H) := by
        simpa [uIcc_of_le hlong] using ht
      dsimp only [f, g]
      exact conj_rationalShortKernelClampedPhase_mul_eq
        q r htIcc.1 hvIcc.1 hwIcc.1

/-- Exact Hermitian kernel expansion of the integrated square energy of the
signed rational short model.  Every complex phase is retained inside the
kernel. -/
theorem
    integral_normSq_selbergSqrtZetaSignedRationalShortModel_eq_re_kernelSum
    (T : ℝ) (X : ℕ) {H : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T) :
    (∫ t in T..2 * T - H,
      Complex.normSq
        (selbergSqrtZetaSignedRationalShortModel T X H t)) =
      (∑ q ∈ selbergSqrtZetaSignedRationalSupport
          (firstZetaApproximationCutoff T) X,
        ∑ r ∈ selbergSqrtZetaSignedRationalSupport
            (firstZetaApproximationCutoff T) X,
          (starRingEnd ℂ)
              (selbergSqrtZetaSignedRationalCoeff
                (firstZetaApproximationCutoff T) X r) *
            selbergSqrtZetaSignedRationalCoeff
              (firstZetaApproximationCutoff T) X q *
            selbergSqrtZetaSignedRationalShortKernel T H q r).re := by
  classical
  let S := selbergSqrtZetaSignedRationalSupport
    (firstZetaApproximationCutoff T) X
  let c := selbergSqrtZetaSignedRationalCoeff
    (firstZetaApproximationCutoff T) X
  let Iq : ℚ → ℝ → ℂ := fun q t =>
    thetaFrequencyShortIntegral
      (selbergSqrtZetaSignedRationalFrequency q) H t
  have hcomplex (q r : ℚ) :
      IntervalIntegrable
        (fun t : ℝ =>
          (starRingEnd ℂ) (c r * Iq r t) * (c q * Iq q t))
        volume T (2 * T - H) := by
    have hkernel :=
      intervalIntegrable_rationalShortKernelIntegrand
        hT hH hroom q r
    have hscaled :=
      hkernel.const_mul ((starRingEnd ℂ) (c r) * c q)
    apply hscaled.congr
    intro t _ht
    dsimp only [Iq]
    simp only [map_mul]
    ring
  have hcross (q : ℚ) (_hq : q ∈ S) (r : ℚ) (_hr : r ∈ S) :
      IntervalIntegrable
        (fun t : ℝ =>
          ((starRingEnd ℂ) (c r * Iq r t) * (c q * Iq q t)).re)
        volume T (2 * T - H) := by
    have hint := hcomplex q r
    exact ⟨Complex.reCLM.integrable_comp hint.1,
      Complex.reCLM.integrable_comp hint.2⟩
  have hinner (q : ℚ) (hq : q ∈ S) :
      IntervalIntegrable
        (fun t : ℝ => ∑ r ∈ S,
          ((starRingEnd ℂ) (c r * Iq r t) * (c q * Iq q t)).re)
        volume T (2 * T - H) := by
    have hsum := Finset.sum_induction
      (fun r => fun t : ℝ =>
        ((starRingEnd ℂ) (c r * Iq r t) * (c q * Iq q t)).re)
      (fun f => IntervalIntegrable f volume T (2 * T - H))
      (fun f g hf hg => hf.add hg) IntervalIntegrable.zero
      (fun r hr => hcross q hq r hr)
    apply hsum.congr
    intro t _ht
    exact Finset.sum_apply t S (fun r t =>
      ((starRingEnd ℂ) (c r * Iq r t) * (c q * Iq q t)).re)
  change
    (∫ t in T..2 * T - H,
      Complex.normSq (∑ q ∈ S, c q * Iq q t)) =
      (∑ q ∈ S, ∑ r ∈ S,
        (starRingEnd ℂ) (c r) * c q *
          selbergSqrtZetaSignedRationalShortKernel T H q r).re
  rw [show (fun t : ℝ =>
      Complex.normSq (∑ q ∈ S, c q * Iq q t)) =
      fun t : ℝ => ∑ q ∈ S, ∑ r ∈ S,
        ((starRingEnd ℂ) (c r * Iq r t) * (c q * Iq q t)).re by
    funext t
    exact MathlibAux.normSq_finset_sum_eq_sum_re_conj_mul S
      (fun q => c q * Iq q t)]
  rw [intervalIntegral.integral_finset_sum]
  · simp only [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finset_sum
      (fun r hr => hcross q hq r hr)]
    apply Finset.sum_congr rfl
    intro r hr
    have hre :=
      Complex.reCLM.intervalIntegral_comp_comm (hcomplex q r)
    change
      (∫ t in T..2 * T - H,
        ((starRingEnd ℂ) (c r * Iq r t) * (c q * Iq q t)).re) =
        (∫ t in T..2 * T - H,
          (starRingEnd ℂ) (c r * Iq r t) * (c q * Iq q t)).re at hre
    rw [hre]
    have hfactor :
        (∫ t in T..2 * T - H,
          (starRingEnd ℂ) (c r * Iq r t) * (c q * Iq q t)) =
          ((starRingEnd ℂ) (c r) * c q) *
            ∫ t in T..2 * T - H,
              (starRingEnd ℂ) (Iq r t) * Iq q t := by
      rw [show (fun t : ℝ =>
          (starRingEnd ℂ) (c r * Iq r t) * (c q * Iq q t)) =
          fun t : ℝ =>
            ((starRingEnd ℂ) (c r) * c q) *
              ((starRingEnd ℂ) (Iq r t) * Iq q t) by
        funext t
        simp only [map_mul]
        ring]
      exact intervalIntegral.integral_const_mul _ _
    rw [hfactor]
    rfl
  · intro q hq
    exact hinner q hq

end HardyTheorem
