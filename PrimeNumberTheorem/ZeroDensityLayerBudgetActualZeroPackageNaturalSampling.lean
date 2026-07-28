import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackagePhase

/-!
# Natural sampling of the actual equal-real-part zero package

This module proves that replacing a real scale `x` by `Nat.floor x` changes the
actual equal-real-part zero-package main term by `o(x^(beta - 1))`.

The proof separates two effects:

* the target power amplitude has floor ratio tending to one;
* the finite Fourier phase sum changes by `o(1)` and is uniformly bounded.

No zero-density or zero-separation hypothesis is used here.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Filter

/-- A uniform norm budget for a finite phase sum. -/
noncomputable def finitePhaseCoefficientNormBudget {ι : Type*} (S : Finset ι)
    (coefficient : ι → ℂ) : ℝ :=
  ∑ z ∈ S, ‖coefficient z‖

theorem norm_finitePhaseSum_le_coefficientNormBudget {ι : Type*}
    (S : Finset ι) (coefficient : ι → ℂ) (frequency : ι → ℝ) (y : ℝ) :
    ‖finitePhaseSum S coefficient frequency y‖ ≤
      finitePhaseCoefficientNormBudget S coefficient := by
  unfold finitePhaseSum finitePhaseCoefficientNormBudget
  calc
    ‖∑ z ∈ S, coefficient z *
        Complex.exp (Complex.I * ((frequency z : ℂ) * (y : ℂ)))‖
        ≤ ∑ z ∈ S,
            ‖coefficient z *
              Complex.exp (Complex.I * ((frequency z : ℂ) * (y : ℂ)))‖ :=
      norm_sum_le _ _
    _ = ∑ z ∈ S, ‖coefficient z‖ := by
      apply Finset.sum_congr rfl
      intro z hz
      simp [Complex.norm_exp]

/--
A real scalar tending to zero kills an arbitrary finite pure-phase sum.
The phases need not converge and the frequencies need not be separated.
-/
theorem tendsto_zero_mul_finitePhaseSum {ι : Type*}
    (S : Finset ι) (coefficient : ι → ℂ) (frequency : ι → ℝ)
    (g v : ℝ → ℝ) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto
      (fun x => (g x : ℂ) * finitePhaseSum S coefficient frequency (v x))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (g := fun x => |g x| * finitePhaseCoefficientNormBudget S coefficient)
  · exact Eventually.of_forall (fun x => norm_nonneg _)
  · exact Eventually.of_forall (fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (norm_finitePhaseSum_le_coefficientNormBudget
          S coefficient frequency (v x))
        (abs_nonneg _))
  · simpa using
      (hg.abs.mul_const (finitePhaseCoefficientNormBudget S coefficient))

/--
The normalized floor-sampling error for a target power amplitude times any
finite phase sum tends to zero.
-/
theorem tendsto_norm_targetAmplitude_mul_finitePhaseSum_natFloor_sub_div
    {ι : Type*} (beta : ℝ) (S : Finset ι)
    (coefficient : ι → ℂ) (frequency : ι → ℝ) :
    Tendsto
      (fun x =>
        ‖(-(targetZeroPowerAmplitude beta (Nat.floor x) : ℂ) *
              finitePhaseSum S coefficient frequency (Real.log (Nat.floor x)) -
            (-(targetZeroPowerAmplitude beta x : ℂ) *
              finitePhaseSum S coefficient frequency (Real.log x)))‖ /
          targetZeroPowerAmplitude beta x)
      atTop (𝓝 0) := by
  let ratio : ℝ → ℝ := fun x =>
    targetZeroPowerAmplitude beta (Nat.floor x) /
      targetZeroPowerAmplitude beta x
  let phase : ℝ → ℂ := fun x =>
    finitePhaseSum S coefficient frequency (Real.log x)
  have hratio : Tendsto ratio atTop (𝓝 1) := by
    simpa [ratio] using targetZeroPowerAmplitude_natFloor_ratio_tendsto beta
  have hphaseDiff : Tendsto
      (fun x => phase (Nat.floor x) - phase x) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [phase] using
      tendsto_norm_finitePhaseSum_log_natFloor_sub S coefficient frequency
  have hfirst : Tendsto
      (fun x => (ratio x : ℂ) * (phase (Nat.floor x) - phase x))
      atTop (𝓝 0) := by
    simpa using hratio.ofReal.mul hphaseDiff
  have hratioSub : Tendsto (fun x => ratio x - 1) atTop (𝓝 0) := by
    simpa using hratio.sub
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1))
  have hsecond : Tendsto
      (fun x => ((ratio x - 1 : ℝ) : ℂ) * phase x) atTop (𝓝 0) := by
    simpa [phase] using
      tendsto_zero_mul_finitePhaseSum S coefficient frequency
        (fun x => ratio x - 1) Real.log hratioSub
  have hnormalized : Tendsto
      (fun x =>
        ((-(targetZeroPowerAmplitude beta (Nat.floor x) : ℂ) *
              phase (Nat.floor x)) -
            (-(targetZeroPowerAmplitude beta x : ℂ) * phase x)) /
          (targetZeroPowerAmplitude beta x : ℂ))
      atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ (by simpa using (hfirst.add hsecond).neg)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hA : targetZeroPowerAmplitude beta x ≠ 0 := by
      exact ne_of_gt (Real.rpow_pos_of_pos hx (beta - 1))
    have hAC : (targetZeroPowerAmplitude beta x : ℂ) ≠ 0 := by
      exact_mod_cast hA
    dsimp [ratio]
    push_cast
    field_simp [hAC]
    ring
  have hnormalizedNorm := hnormalized.norm
  refine Tendsto.congr' ?_ (by simpa using hnormalizedNorm)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hA : 0 < targetZeroPowerAmplitude beta x :=
    Real.rpow_pos_of_pos hx (beta - 1)
  rw [abs_of_pos hA]
  simp [phase, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]

/--
The actual equal-real-part zero-package PNT main term is stable under natural
floor sampling at its exact target power scale.
-/
theorem tendsto_actualEqualRealPartZeroPackagePNTMain_natFloor_error
    (T beta : ℝ) :
    Tendsto
      (fun x =>
        ‖actualEqualRealPartZeroPackagePNTMain (Nat.floor x) T beta -
            actualEqualRealPartZeroPackagePNTMain x T beta‖ /
          targetZeroPowerAmplitude beta x)
      atTop (𝓝 0) := by
  let coefficient : ℂ → ℂ := fun rho =>
    (analyticOrderNatAt riemannZeta rho : ℂ) / rho
  let frequency : ℂ → ℝ := fun rho => rho.im
  have hgeneric :=
    tendsto_norm_targetAmplitude_mul_finitePhaseSum_natFloor_sub_div beta
      (ZeroForcedOscillation.equalRealPartZeroPackage T beta)
      coefficient frequency
  refine Tendsto.congr' ?_ hgeneric
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hfloorpos : 0 < (Nat.floor x : ℝ) := by
    exact_mod_cast (Nat.floor_pos.mpr (le_of_lt hx))
  rw [actualEqualRealPartZeroPackagePNTMain_eq_target_mul_phase hxpos,
    actualEqualRealPartZeroPackagePNTMain_eq_target_mul_phase hfloorpos]
  rfl

end PrimeNumberTheorem
