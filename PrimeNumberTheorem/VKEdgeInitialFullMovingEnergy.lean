import PrimeNumberTheorem.VKEdgeFullMovingComplementEnergy
import PrimeNumberTheorem.VKEdgePiOverTwoSweptL2

open Complex Filter MeasureTheory Set
open scoped Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Initial full moving energy forced by an off-line zero

The swept contour theorem already gives a linear ordinary local `L²` lower
bound for the true normalized Chebyshev error on every sufficiently late
epsilon window, assuming one off-critical-line zeta zero.  This module turns
that lower bound into a uniform positive Gaussian energy for the concrete
no-jump explicit-formula remainder with an empty selected cluster.

The Gaussian variance is chosen to be the square of the logarithmic window
length.  Its minimum on the window is therefore a fixed constant divided by
the window length, exactly cancelling the linear ordinary `L²` scale.

This is the first residual-energy input for the full moving complementary
energy bridge.  It does not yet control the finite-height approximation on
the growing epsilon window and does not iterate maximal-layer absorption.
-/

/-- The real normalization used by the oscillation theorem is the squared
norm of the complex Chebyshev normalization, multiplied by `‖rho‖²`. -/
theorem
    normalizedPsiError_sq_eq_norm_sq_mul_normalizedChebyshevPsiErrorAtExponent
    (rho : ℂ) (y : ℝ) :
    normalizedPsiError rho y ^ 2 =
      ‖rho‖ ^ 2 *
        ‖normalizedChebyshevPsiErrorAtExponent rho.re y‖ ^ 2 := by
  unfold normalizedPsiError normalizedChebyshevPsiErrorAtExponent
  rw [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_real, Real.norm_eq_abs]
  ring_nf
  rw [sq_abs]
  ring

/-- At variance `L²`, the Gaussian value at the right endpoint has the
explicit scale `constant / L`. -/
theorem normalizedGaussian_sqScale_endpoint
    {L : ℝ} (hL : 0 < L) :
    normalizedGaussian (L ^ 2) L =
      Real.exp (-(1 : ℝ) / 4) /
        (2 * Real.sqrt Real.pi * L) := by
  have hLne : L ≠ 0 := hL.ne'
  have hsqrt :
      Real.sqrt (Real.pi * L ^ 2) =
        Real.sqrt Real.pi * L := by
    rw [Real.sqrt_mul Real.pi_nonneg, Real.sqrt_sq_eq_abs,
      abs_of_pos hL]
  unfold normalizedGaussian
  rw [hsqrt]
  congr 1
  · field_simp [hLne]
  · ring

/-- The endpoint is the minimum of the variance-`L²` Gaussian on the forward
window `[0,L]`. -/
theorem normalizedGaussian_sqScale_endpoint_le
    {L t : ℝ} (hL : 0 < L) (ht : t ∈ Set.Icc 0 L) :
    normalizedGaussian (L ^ 2) L ≤
      normalizedGaussian (L ^ 2) t := by
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hL
  have hsum : 0 ≤ L + t := by linarith [ht.1]
  have htSq : t ^ 2 ≤ L ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hsum]
  have hexponent :
      -L ^ 2 / (4 * L ^ 2) ≤
        -t ^ 2 / (4 * L ^ 2) := by
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 4 * L ^ 2)).2
    linarith
  have hexp :
      Real.exp (-L ^ 2 / (4 * L ^ 2)) ≤
        Real.exp (-t ^ 2 / (4 * L ^ 2)) :=
    Real.exp_le_exp.mpr hexponent
  unfold normalizedGaussian
  exact div_le_div_of_nonneg_right hexp (by positivity)

/-- Forward Gaussian second moment of the real normalized PNT error. -/
noncomputable def normalizedPsiErrorForwardGaussianSecondMoment
    (rho : ℂ) (a m L : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Icc 0 L,
    normalizedGaussian m t * normalizedPsiError rho (a + t) ^ 2

private theorem measurable_normalizedPsiError_initialEnergy (rho : ℂ) :
    Measurable (normalizedPsiError rho) := by
  have hpsi : Measurable chebyshevPsi := by
    simpa only [chebyshevPsi_eq_mathlib] using
      Chebyshev.psi_mono.measurable
  unfold normalizedPsiError
  fun_prop

private theorem normalizedPsiError_abs_le_exp_growth_initialEnergy
    (rho : ℂ) (y : ℝ) :
    |normalizedPsiError rho y| ≤
      ‖rho‖ * (Real.log 4 + 5) *
        Real.exp ((1 - rho.re) * y) := by
  have hpsi :
      chebyshevPsi (Real.exp y) ≤
        (Real.log 4 + 4) * Real.exp y := by
    rw [chebyshevPsi_eq_mathlib]
    exact Chebyshev.psi_le_const_mul_self (Real.exp_pos y).le
  have hpsiNonneg : 0 ≤ chebyshevPsi (Real.exp y) := by
    unfold chebyshevPsi
    exact Finset.sum_nonneg fun n _ => by
      rw [vonMangoldt_eq_mathlib]
      exact ArithmeticFunction.vonMangoldt_nonneg
  have herror :
      |chebyshevPsi (Real.exp y) - Real.exp y| ≤
        (Real.log 4 + 5) * Real.exp y := by
    rw [abs_sub_le_iff]
    constructor
    · nlinarith [Real.exp_pos y]
    · nlinarith [Real.exp_pos y,
        Real.log_pos (by norm_num : 1 < (4 : ℝ))]
  unfold normalizedPsiError
  rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg rho),
    abs_of_pos (Real.exp_pos _)]
  calc
    ‖rho‖ * |chebyshevPsi (Real.exp y) - Real.exp y| *
          Real.exp (-rho.re * y) ≤
        ‖rho‖ * ((Real.log 4 + 5) * Real.exp y) *
          Real.exp (-rho.re * y) := by
      gcongr
    _ = ‖rho‖ * (Real.log 4 + 5) *
          Real.exp ((1 - rho.re) * y) := by
      rw [show
          ‖rho‖ * ((Real.log 4 + 5) * Real.exp y) *
                Real.exp (-rho.re * y) =
              ‖rho‖ * (Real.log 4 + 5) *
                (Real.exp y * Real.exp (-rho.re * y)) by ring,
        ← Real.exp_add]
      congr 1
      ring

private theorem integrableOn_normalizedPsiError_sq_comp_add
    (rho : ℂ) (a L : ℝ) :
    IntegrableOn
      (fun t => normalizedPsiError rho (a + t) ^ 2)
      (Set.Icc 0 L) := by
  let R : ℝ := |a| + |L|
  let B : ℝ :=
    (‖rho‖ * (Real.log 4 + 5) *
      Real.exp (|1 - rho.re| * R)) ^ 2
  apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top
  · exact
      (((measurable_normalizedPsiError_initialEnergy rho).comp
        (measurable_const.add measurable_id)).pow_const 2
          |>.aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have htAbs : |t| ≤ |L| := by
      by_cases hL0 : 0 ≤ L
      · rw [abs_of_nonneg hL0]
        exact (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)
      · have hempty : Set.Icc (0 : ℝ) L = ∅ := by
          exact Set.Icc_eq_empty hL0
        rw [hempty] at ht
        simp at ht
    have hayAbs : |a + t| ≤ R := by
      dsimp [R]
      have htriangle : |a + t| ≤ |a| + |t| := by
        simpa [Real.norm_eq_abs] using norm_add_le a t
      linarith
    have hexponent :
        (1 - rho.re) * (a + t) ≤ |1 - rho.re| * R := by
      calc
        (1 - rho.re) * (a + t) ≤
            |(1 - rho.re) * (a + t)| := le_abs_self _
        _ = |1 - rho.re| * |a + t| := abs_mul _ _
        _ ≤ |1 - rho.re| * R :=
          mul_le_mul_of_nonneg_left hayAbs (abs_nonneg _)
    have hexp :
        Real.exp ((1 - rho.re) * (a + t)) ≤
          Real.exp (|1 - rho.re| * R) :=
      Real.exp_le_exp.mpr hexponent
    have hcoef :
        0 ≤ ‖rho‖ * (Real.log 4 + 5) := by positivity
    have hnorm :=
      (normalizedPsiError_abs_le_exp_growth_initialEnergy
        rho (a + t)).trans
        (mul_le_mul_of_nonneg_left hexp hcoef)
    have hsq :
        normalizedPsiError rho (a + t) ^ 2 ≤ B := by
      dsimp [B]
      nlinarith [sq_abs (normalizedPsiError rho (a + t)),
        abs_nonneg (normalizedPsiError rho (a + t))]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq

private theorem normalizedPsiError_sq_setIntegral_comp_add
    (rho : ℂ) (a : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ t : ℝ in Set.Icc 0 L,
        normalizedPsiError rho (a + t) ^ 2) =
      ∫ y : ℝ in Set.Icc a (a + L),
        normalizedPsiError rho y ^ 2 := by
  let f : ℝ → ℝ := fun y => normalizedPsiError rho y ^ 2
  calc
    (∫ t : ℝ in Set.Icc 0 L,
        normalizedPsiError rho (a + t) ^ 2) =
        ∫ t : ℝ in (0 : ℝ)..L, f (t + a) := by
      rw [intervalIntegral.integral_of_le hL,
        ← integral_Icc_eq_integral_Ioc]
      apply integral_congr_ae
      filter_upwards with t
      simp [f, add_comm]
    _ = ∫ y : ℝ in a..L + a, f y := by
      simpa only [zero_add] using
        intervalIntegral.integral_comp_add_right
          (a := 0) (b := L) f a
    _ = ∫ y : ℝ in Set.Icc a (a + L),
        normalizedPsiError rho y ^ 2 := by
      rw [intervalIntegral.integral_of_le (by linarith),
        ← integral_Icc_eq_integral_Ioc]
      simp only [f, add_comm]

/-- With an empty selected cluster, the concrete no-jump remainder energy is
exactly the true normalized PNT-error Gaussian energy divided by `‖rho‖²`.
The equality is independent of the truncation height `T`. -/
theorem
    normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment_empty
    (rho : ℂ) (T a m L : ℝ) (hrho : rho ≠ 0) :
    normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
        ∅ T rho.re a m L =
      (1 / ‖rho‖ ^ 2) *
        normalizedPsiErrorForwardGaussianSecondMoment rho a m L := by
  have hbase :=
    normalizedChebyshevPsiErrorAtExponent_ae_eq_neg_cluster_sub_withoutJump
      (S := (∅ : Finset ℂ)) (T := T) (beta := rho.re)
      (by simp)
  have hshift :
      (fun t =>
        normalizedChebyshevPsiErrorAtExponent rho.re (a + t)) =ᵐ[volume]
      (fun t =>
        -normalizedFiniteZeroClusterPsiRemainderWithoutJump
          ∅ T rho.re (a + t)) := by
    have hcomp :=
      hbase.comp_tendsto
        (measurePreserving_add_left volume a).quasiMeasurePreserving.tendsto_ae
    filter_upwards [hcomp] with t ht
    simpa [normalizedFiniteZeroClusterContribution] using ht
  unfold
    normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
    normalizedPsiErrorForwardGaussianSecondMoment
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hshift] with t ht
  have hnormPos : 0 < ‖rho‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hrho)
  have hnorm :
      ‖normalizedChebyshevPsiErrorAtExponent rho.re (a + t)‖ =
        ‖normalizedFiniteZeroClusterPsiRemainderWithoutJump
          ∅ T rho.re (a + t)‖ := by
    simpa only [norm_neg] using congrArg norm ht
  rw [← hnorm,
    normalizedPsiError_sq_eq_norm_sq_mul_normalizedChebyshevPsiErrorAtExponent]
  field_simp

/-- An ordinary second moment on `[a,a+L]` controls the forward Gaussian
moment at variance `L²`. -/
theorem
    normalizedPsiErrorForwardGaussianSecondMoment_ge_endpoint_mul_ordinary
    (rho : ℂ) {a L : ℝ} (hL : 0 < L) :
    normalizedGaussian (L ^ 2) L *
        (∫ y : ℝ in Set.Icc a (a + L),
          normalizedPsiError rho y ^ 2) ≤
      normalizedPsiErrorForwardGaussianSecondMoment
        rho a (L ^ 2) L := by
  let f : ℝ → ℝ := fun t => normalizedPsiError rho (a + t) ^ 2
  let endpoint : ℝ := normalizedGaussian (L ^ 2) L
  have hfInt : IntegrableOn f (Set.Icc 0 L) := by
    simpa [f] using integrableOn_normalizedPsiError_sq_comp_add rho a L
  have hweightContinuous : Continuous (normalizedGaussian (L ^ 2)) := by
    exact continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_normalizedGaussian (sq_pos_of_pos hL) t).continuousAt
  have hweightedInt :
      IntegrableOn
        (fun t => normalizedGaussian (L ^ 2) t * f t)
        (Set.Icc 0 L) := by
    have hfMeas :
        AEStronglyMeasurable f
          (volume.restrict (Set.Icc 0 L)) :=
      hfInt.1
    have hweightBounded :
        ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) L,
          ‖normalizedGaussian (L ^ 2) t‖ ≤ C := by
      refine ⟨normalizedGaussian (L ^ 2) 0, ?_⟩
      intro t ht
      rw [Real.norm_eq_abs,
        abs_of_pos (normalizedGaussian_pos (sq_pos_of_pos hL) t)]
      unfold normalizedGaussian
      apply div_le_div_of_nonneg_right
      · have hexponent :
            -t ^ 2 / (4 * L ^ 2) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (sq_nonneg t)) (by positivity)
        simpa using Real.exp_le_exp.mpr hexponent
      · positivity
    rcases hweightBounded with ⟨C, hC⟩
    exact hfInt.bdd_mul
      (hweightContinuous.measurable.aestronglyMeasurable.restrict)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact hC t ht)
  have hendpointNonneg : 0 ≤ endpoint := by
    dsimp [endpoint]
    exact (normalizedGaussian_pos (sq_pos_of_pos hL) L).le
  have hlowerInt :
      IntegrableOn (fun t => endpoint * f t) (Set.Icc 0 L) :=
    hfInt.const_mul endpoint
  have hmono :
      (∫ t : ℝ in Set.Icc 0 L, endpoint * f t) ≤
        ∫ t : ℝ in Set.Icc 0 L,
          normalizedGaussian (L ^ 2) t * f t := by
    apply integral_mono_ae hlowerInt hweightedInt
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_le_mul_of_nonneg_right
      (normalizedGaussian_sqScale_endpoint_le hL ht)
      (sq_nonneg _)
  have htranslate :=
    normalizedPsiError_sq_setIntegral_comp_add rho a hL.le
  unfold normalizedPsiErrorForwardGaussianSecondMoment
  calc
    endpoint *
          (∫ y : ℝ in Set.Icc a (a + L),
            normalizedPsiError rho y ^ 2) =
        ∫ t : ℝ in Set.Icc 0 L, endpoint * f t := by
      rw [MeasureTheory.integral_const_mul, htranslate]
    _ ≤
        ∫ t : ℝ in Set.Icc 0 L,
          normalizedGaussian (L ^ 2) t * f t := hmono

/-- Uniform positive residual-energy constant obtained after the linear
ordinary `L²` scale cancels the `1/L` Gaussian endpoint scale. -/
def initialEmptyClusterResidualGaussianL2Constant
    (ε : ℝ) (rho : ℂ) (k : ℕ) : ℝ :=
  Real.exp (-(1 : ℝ) / 4) *
      centeredSharpenedSweptOrdinaryL2Constant ε rho k /
    (2 * Real.sqrt Real.pi * ε * ‖rho‖ ^ 2)

/-- One off-critical-line zeta zero forces a uniform positive Gaussian
energy for the true no-jump remainder with empty selected cluster on every
sufficiently late epsilon logarithmic window.  The statement is independent
of the truncation height because the empty-cluster remainder is almost
everywhere the full normalized Chebyshev error. -/
theorem
    exists_eventually_emptyClusterResidualForwardGaussianSecondMoment_gt
    {ε : ℝ} {rho : ℂ} {sigma : ℝ}
    (hε : 0 < ε)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hσ : 1 / 2 < sigma)
    (hσrho : sigma < rho.re)
    (hrhoRe1 : rho.re < 1) :
    ∃ k : ℕ,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      0 < initialEmptyClusterResidualGaussianL2Constant ε rho k ∧
      ∀ᶠ Y : ℝ in atTop,
        ∀ T : ℝ,
          initialEmptyClusterResidualGaussianL2Constant ε rho k <
            normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
              ∅ T rho.re (Real.log Y)
                ((ε * Real.log Y) ^ 2) (ε * Real.log Y) := by
  rcases
      exists_eventually_ordinarySecondMoment_in_epsilonLogWindow_gt_linear
        hε hgamma hzero hσ hσrho hrhoRe1 with
    ⟨k, hmissing, hCpos, hordinary⟩
  have hrho : rho ≠ 0 := by
    intro hrho
    have him := congrArg Complex.im hrho
    norm_num at him
    linarith
  have hconstantPos :
      0 < initialEmptyClusterResidualGaussianL2Constant ε rho k := by
    unfold initialEmptyClusterResidualGaussianL2Constant
    positivity
  refine ⟨k, hmissing, hconstantPos, ?_⟩
  filter_upwards [hordinary, eventually_gt_atTop (1 : ℝ)] with
      Y hordinaryY hY
  intro T
  let L : ℝ := ε * Real.log Y
  have hlog : 0 < Real.log Y := Real.log_pos hY
  have hL : 0 < L := mul_pos hε hlog
  have hordinaryY' :
      centeredSharpenedSweptOrdinaryL2Constant ε rho k *
          Real.log Y <
        ∫ y : ℝ in Set.Icc (Real.log Y) (Real.log Y + L),
          normalizedPsiError rho y ^ 2 := by
    simpa [L, add_mul] using hordinaryY
  have hgaussian :=
    normalizedPsiErrorForwardGaussianSecondMoment_ge_endpoint_mul_ordinary
      rho (a := Real.log Y) hL
  have hweightPos :
      0 < normalizedGaussian (L ^ 2) L :=
    normalizedGaussian_pos (sq_pos_of_pos hL) L
  have hweighted :
      normalizedGaussian (L ^ 2) L *
          (centeredSharpenedSweptOrdinaryL2Constant ε rho k *
            Real.log Y) <
        normalizedPsiErrorForwardGaussianSecondMoment
          rho (Real.log Y) (L ^ 2) L := by
    exact
      (mul_lt_mul_of_pos_left hordinaryY' hweightPos).trans_le hgaussian
  have hresidual :=
    normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment_empty
      rho T (Real.log Y) (L ^ 2) L hrho
  have hnormSqPos : 0 < ‖rho‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hrho)
  have hscaled :
      (1 / ‖rho‖ ^ 2) *
          (normalizedGaussian (L ^ 2) L *
            (centeredSharpenedSweptOrdinaryL2Constant ε rho k *
              Real.log Y)) <
        normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
          ∅ T rho.re (Real.log Y) (L ^ 2) L := by
    rw [hresidual]
    exact mul_lt_mul_of_pos_left hweighted (one_div_pos.mpr hnormSqPos)
  have hconstant :
      initialEmptyClusterResidualGaussianL2Constant ε rho k =
        (1 / ‖rho‖ ^ 2) *
          (normalizedGaussian (L ^ 2) L *
            (centeredSharpenedSweptOrdinaryL2Constant ε rho k *
              Real.log Y)) := by
    rw [normalizedGaussian_sqScale_endpoint hL]
    unfold initialEmptyClusterResidualGaussianL2Constant
    dsimp [L]
    field_simp [hε.ne', hlog.ne',
      (Real.sqrt_pos.2 Real.pi_pos).ne',
      (norm_pos_iff.mpr hrho).ne']
  simpa [L, hconstant] using hscaled

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
