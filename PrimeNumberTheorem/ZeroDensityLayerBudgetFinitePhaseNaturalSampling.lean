import PrimeNumberTheorem.ZeroDensityLayerBudgetNaturalSamplingTransfer
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Natural-floor stability of finite phase sums

Finite equal-real-part zero packages become finite Fourier sums after the
common power `x^beta` is factored out.  This file proves the global phase
Lipschitz estimate and applies it to the logarithmic displacement caused by
taking the natural floor.
-/

namespace PrimeNumberTheorem

open Filter

/-- A finite complex Fourier sum with arbitrary coefficients and real
frequencies. -/
noncomputable def finitePhaseSum {ι : Type*}
    (S : Finset ι) (coefficient : ι → ℂ) (frequency : ι → ℝ)
    (y : ℝ) : ℂ :=
  ∑ z ∈ S,
    coefficient z * Complex.exp (Complex.I * (frequency z * y : ℂ))

/-- The global Lipschitz budget of a finite phase sum. -/
noncomputable def finitePhaseLipschitzBudget {ι : Type*}
    (S : Finset ι) (coefficient : ι → ℂ) (frequency : ι → ℝ) : ℝ :=
  ∑ z ∈ S, ‖coefficient z‖ * |frequency z|

private theorem norm_exp_phase_sub_le
    (gamma u v : ℝ) :
    ‖Complex.exp (Complex.I * (gamma * u : ℂ)) -
        Complex.exp (Complex.I * (gamma * v : ℂ))‖ ≤
      |gamma| * |u - v| := by
  have harg :
      Complex.I * (gamma * u : ℂ) =
        Complex.I * (gamma * v : ℂ) +
          Complex.I * (gamma * (u - v) : ℂ) := by
    push_cast
    ring
  rw [harg, Complex.exp_add]
  have hfactor :
      Complex.exp (Complex.I * (gamma * v : ℂ)) *
            Complex.exp (Complex.I * (gamma * (u - v) : ℂ)) -
          Complex.exp (Complex.I * (gamma * v : ℂ)) =
        Complex.exp (Complex.I * (gamma * v : ℂ)) *
          (Complex.exp (Complex.I * (gamma * (u - v) : ℂ)) - 1) := by
    ring
  rw [hfactor, norm_mul]
  have hunit :
      ‖Complex.exp (Complex.I * (gamma * v : ℂ))‖ = 1 := by
    have hcast :
        (((gamma * v : ℝ) : ℂ)) = (gamma : ℂ) * (v : ℂ) := by
      norm_num
    rw [← hcast]
    exact Complex.norm_exp_I_mul_ofReal (gamma * v)
  rw [hunit, one_mul]
  simpa [Real.norm_eq_abs, abs_mul] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le
      (x := gamma * (u - v)))

/-- A finite phase sum is globally Lipschitz, with the explicit sum of
coefficient norms times frequency magnitudes as its constant. -/
theorem norm_finitePhaseSum_sub_le {ι : Type*}
    (S : Finset ι) (coefficient : ι → ℂ) (frequency : ι → ℝ)
    (u v : ℝ) :
    ‖finitePhaseSum S coefficient frequency u -
        finitePhaseSum S coefficient frequency v‖ ≤
      finitePhaseLipschitzBudget S coefficient frequency * |u - v| := by
  rw [finitePhaseSum, finitePhaseSum, ← Finset.sum_sub_distrib]
  calc
    ‖∑ z ∈ S,
        (coefficient z *
            Complex.exp (Complex.I * (frequency z * u : ℂ)) -
          coefficient z *
            Complex.exp (Complex.I * (frequency z * v : ℂ)))‖
        ≤
      ∑ z ∈ S,
        ‖coefficient z *
            Complex.exp (Complex.I * (frequency z * u : ℂ)) -
          coefficient z *
            Complex.exp (Complex.I * (frequency z * v : ℂ))‖ :=
      norm_sum_le S (fun z =>
        coefficient z *
            Complex.exp (Complex.I * (frequency z * u : ℂ)) -
          coefficient z *
            Complex.exp (Complex.I * (frequency z * v : ℂ)))
    _ ≤
      ∑ z ∈ S,
        (‖coefficient z‖ * |frequency z|) * |u - v| := by
      apply Finset.sum_le_sum
      intro z hz
      rw [← mul_sub, norm_mul]
      calc
        ‖coefficient z‖ *
              ‖Complex.exp (Complex.I * (frequency z * u : ℂ)) -
                Complex.exp (Complex.I * (frequency z * v : ℂ))‖
            ≤
          ‖coefficient z‖ * (|frequency z| * |u - v|) :=
            mul_le_mul_of_nonneg_left
              (norm_exp_phase_sub_le (frequency z) u v)
              (norm_nonneg (coefficient z))
        _ = (‖coefficient z‖ * |frequency z|) * |u - v| := by
          ring
    _ =
      finitePhaseLipschitzBudget S coefficient frequency * |u - v| := by
      simp [finitePhaseLipschitzBudget, Finset.sum_mul]

/-- The logarithmic displacement between a positive real number and its
natural floor tends to zero. -/
theorem tendsto_log_natFloor_sub_log :
    Tendsto
      (fun x : ℝ => Real.log (⌊x⌋₊ : ℝ) - Real.log x)
      atTop (nhds 0) := by
  have hratio :
      Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ) / x)
        atTop (nhds 1) :=
    tendsto_nat_floor_div_atTop
  have hlog :
      Tendsto (fun x : ℝ => Real.log ((⌊x⌋₊ : ℝ) / x))
        atTop (nhds 0) := by
    simpa using hratio.log one_ne_zero
  apply hlog.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hxne : x ≠ 0 := by linarith
  have hfloor_ge : 1 ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    norm_num
    exact hx
  have hfloor_ne : (⌊x⌋₊ : ℝ) ≠ 0 := by
    have hfloor_nat_ne : ⌊x⌋₊ ≠ 0 := by omega
    exact_mod_cast hfloor_nat_ne
  exact Real.log_div hfloor_ne hxne

/-- A finite phase sum changes by `o(1)` when its logarithmic argument is
replaced by the logarithm of the natural floor. -/
theorem tendsto_norm_finitePhaseSum_log_natFloor_sub
    {ι : Type*} (S : Finset ι)
    (coefficient : ι → ℂ) (frequency : ι → ℝ) :
    Tendsto
      (fun x : ℝ =>
        ‖finitePhaseSum S coefficient frequency (Real.log (⌊x⌋₊ : ℝ)) -
          finitePhaseSum S coefficient frequency (Real.log x)‖)
      atTop (nhds 0) := by
  have hlog_abs :
      Tendsto
        (fun x : ℝ =>
          |Real.log (⌊x⌋₊ : ℝ) - Real.log x|)
        atTop (nhds 0) := by
    simpa using tendsto_log_natFloor_sub_log.abs
  have hmajorant :
      Tendsto
        (fun x : ℝ =>
          finitePhaseLipschitzBudget S coefficient frequency *
            |Real.log (⌊x⌋₊ : ℝ) - Real.log x|)
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hlog_abs
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmajorant
      (fun x => norm_nonneg _)
      (fun x =>
        norm_finitePhaseSum_sub_le S coefficient frequency
          (Real.log (⌊x⌋₊ : ℝ)) (Real.log x))

end PrimeNumberTheorem
