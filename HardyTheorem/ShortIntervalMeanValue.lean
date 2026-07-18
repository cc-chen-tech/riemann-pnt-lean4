import HardyTheorem.FirstZetaApproximation
import HardyTheorem.HardyIntegralBasics
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Complex MeasureTheory Set

namespace HardyTheorem

/-- The signed Hardy-Z integral over a sliding interval of length `delta`. -/
noncomputable def hardyShortIntegral (δ t : ℝ) : ℝ :=
  ∫ u in t..t + δ, hardyZ u

/-- The absolute Hardy-Z integral over a sliding interval of length `delta`. -/
noncomputable def hardyShortAbsIntegral (δ t : ℝ) : ℝ :=
  ∫ u in t..t + δ, |hardyZ u|

theorem continuous_hardyShortIntegral (δ : ℝ) :
    Continuous (hardyShortIntegral δ) := by
  let F : ℝ → ℝ := fun x => ∫ u in 0..x, hardyZ u
  have hF : Continuous F := by
    dsimp only [F]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (_x : ℝ) u => hardyZ u)
        (hardyZ_continuous.comp continuous_snd) continuous_id
  have hEq : hardyShortIntegral δ = fun t => F (t + δ) - F t := by
    funext t
    have h0add : IntervalIntegrable hardyZ volume 0 (t + δ) :=
      hardyZ_continuous.intervalIntegrable _ _
    have h0t : IntervalIntegrable hardyZ volume 0 t :=
      hardyZ_continuous.intervalIntegrable _ _
    dsimp only [hardyShortIntegral, F]
    exact (intervalIntegral.integral_interval_sub_left h0add h0t).symm
  rw [hEq]
  exact (hF.comp (continuous_id.add continuous_const)).sub hF

theorem continuous_hardyShortAbsIntegral (δ : ℝ) :
    Continuous (hardyShortAbsIntegral δ) := by
  let F : ℝ → ℝ := fun x => ∫ u in 0..x, |hardyZ u|
  have habs : Continuous fun u : ℝ => |hardyZ u| := hardyZ_continuous.abs
  have hF : Continuous F := by
    dsimp only [F]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (_x : ℝ) u => |hardyZ u|)
        (habs.comp continuous_snd) continuous_id
  have hEq : hardyShortAbsIntegral δ = fun t => F (t + δ) - F t := by
    funext t
    have h0add : IntervalIntegrable (fun u : ℝ => |hardyZ u|) volume 0 (t + δ) :=
      habs.intervalIntegrable _ _
    have h0t : IntervalIntegrable (fun u : ℝ => |hardyZ u|) volume 0 t :=
      habs.intervalIntegrable _ _
    dsimp only [hardyShortAbsIntegral, F]
    exact (intervalIntegral.integral_interval_sub_left h0add h0t).symm
  rw [hEq]
  exact (hF.comp (continuous_id.add continuous_const)).sub hF

/-- A short absolute Hardy-Z integral inside `[T, 2T]` is bounded by its
length times the uniform `O(sqrt T)` critical-line bound. -/
theorem exists_hardyShortAbsIntegral_le_mul_sqrt :
    ∃ C T0 : ℝ, 0 < C ∧ 1 ≤ T0 ∧
      ∀ T δ t : ℝ, T0 ≤ T → 0 ≤ δ → t ∈ Set.Icc T (2 * T - δ) →
        hardyShortAbsIntegral δ t ≤ C * δ * Real.sqrt T := by
  obtain ⟨C, T0, hC, hT0, hbound⟩ :=
    exists_norm_riemannZeta_critical_line_le_sqrt
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T δ t hT hδ ht
  have htt : t ≤ t + δ := by linarith
  have habsInt :
      IntervalIntegrable (fun u : ℝ => |hardyZ u|) volume t (t + δ) :=
    hardyZ_continuous.abs.intervalIntegrable _ _
  have hconstInt :
      IntervalIntegrable (fun _u : ℝ => C * Real.sqrt T) volume t (t + δ) :=
    continuous_const.intervalIntegrable _ _
  have hpoint : ∀ u ∈ Set.Icc t (t + δ),
      |hardyZ u| ≤ C * Real.sqrt T := by
    intro u hu
    rw [abs_hardyZ_eq_norm_riemannZeta]
    apply hbound T u hT
    constructor
    · exact ht.1.trans hu.1
    · linarith [hu.2, ht.2]
  dsimp only [hardyShortAbsIntegral]
  calc
    (∫ u in t..t + δ, |hardyZ u|) ≤
        ∫ _u in t..t + δ, C * Real.sqrt T :=
      intervalIntegral.integral_mono_on htt habsInt hconstInt hpoint
    _ = C * δ * Real.sqrt T := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

end HardyTheorem
