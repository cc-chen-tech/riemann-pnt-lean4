import PrimeNumberTheorem.MWKFCubicAFEProgression
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Complex Filter MeasureTheory Set
open scoped Interval ContDiff

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The actual finite-height Mellin weight on positive real products

The logarithmic extension is entire.  Compactness supplies the domination
needed for differentiating its finite vertical integral.  These are local
regularity statements, not uniform derivative or transform-tail estimates.
-/

private theorem differentiable_setIntegral_Ioc_of_continuous_derivative
    (F F' : ℂ → ℝ → ℂ)
    (hF : Continuous (fun p : ℂ × ℝ ↦ F p.1 p.2))
    (hF' : Continuous (fun p : ℂ × ℝ ↦ F' p.1 p.2))
    (hd : ∀ z y, HasDerivAt (fun w ↦ F w y) (F' z y) z)
    (a b : ℝ) : Differentiable ℂ (fun z ↦ ∫ y in Ioc a b, F z y) := by
  intro z
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z 1).prod isCompact_Icc).bddAbove_image
    hF'.norm.continuousOn
  have hmeas : ∀ w, AEStronglyMeasurable (F w) (volume.restrict (Ioc a b)) :=
    fun w ↦ (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hint : Integrable (F z) (volume.restrict (Ioc a b)) :=
    (hF.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hmeas' : AEStronglyMeasurable (F' z) (volume.restrict (Ioc a b)) :=
    (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hbound : ∀ᵐ y ∂volume.restrict (Ioc a b),
      ∀ w ∈ Metric.closedBall z 1, ‖F' w y‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    intro w hw
    exact hC (mem_image_of_mem (fun p : ℂ × ℝ ↦ ‖F' p.1 p.2‖)
      (show (w, y) ∈ (Metric.closedBall z 1) ×ˢ Icc a b from
        ⟨hw, Ioc_subset_Icc_self hy⟩))
  have hconst : Integrable (fun _ : ℝ ↦ C) (volume.restrict (Ioc a b)) :=
    continuous_const.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.closedBall_mem_nhds z (by norm_num)) (Eventually.of_forall hmeas)
    hint hmeas' hbound hconst
    (Eventually.of_forall (fun y w _ ↦ hd w y))).2.differentiableAt

private theorem differentiable_intervalIntegral_of_continuous_derivative
    (F F' : ℂ → ℝ → ℂ)
    (hF : Continuous (fun p : ℂ × ℝ ↦ F p.1 p.2))
    (hF' : Continuous (fun p : ℂ × ℝ ↦ F' p.1 p.2))
    (hd : ∀ z y, HasDerivAt (fun w ↦ F w y) (F' z y) z)
    (a b : ℝ) : Differentiable ℂ (fun z ↦ ∫ y in a..b, F z y) := by
  exact (differentiable_setIntegral_Ioc_of_continuous_derivative F F' hF hF' hd a b).sub
    (differentiable_setIntegral_Ioc_of_continuous_derivative F F' hF hF' hd b a)

/-- Entire extension in the logarithm of the product variable. -/
noncomputable def cubicAFELogProductWeightFinite (t X V : ℝ) (z : ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ in -V..V,
    cubicAFEScalar t (cubicAFEVerticalPoint X y) *
      Complex.exp (-cubicAFEVerticalPoint X y * z)

theorem differentiable_cubicAFELogProductWeightFinite
    (t X V : ℝ) (hX : 1 / 2 < X) :
    Differentiable ℂ (cubicAFELogProductWeightFinite t X V) := by
  let F : ℂ → ℝ → ℂ := fun z y ↦
    cubicAFEScalar t (cubicAFEVerticalPoint X y) *
      Complex.exp (-cubicAFEVerticalPoint X y * z)
  let F' : ℂ → ℝ → ℂ := fun z y ↦
    cubicAFEScalar t (cubicAFEVerticalPoint X y) *
      (Complex.exp (-cubicAFEVerticalPoint X y * z) * -cubicAFEVerticalPoint X y)
  have hs : Continuous (fun p : ℂ × ℝ ↦
      cubicAFEScalar t (cubicAFEVerticalPoint X p.2)) :=
    (continuous_cubicAFEScalar_vertical t X hX).comp continuous_snd
  have hv : Continuous (fun p : ℂ × ℝ ↦ cubicAFEVerticalPoint X p.2) := by
    unfold cubicAFEVerticalPoint
    fun_prop
  have hF : Continuous (fun p : ℂ × ℝ ↦ F p.1 p.2) :=
    hs.mul (Complex.continuous_exp.comp (hv.neg.mul continuous_fst))
  have hF' : Continuous (fun p : ℂ × ℝ ↦ F' p.1 p.2) :=
    hs.mul ((Complex.continuous_exp.comp (hv.neg.mul continuous_fst)).mul hv.neg)
  have hd : ∀ z y, HasDerivAt (fun w ↦ F w y) (F' z y) z := by
    intro z y
    simpa only [F, F', id_eq, mul_one] using
      (((hasDerivAt_id z).const_mul (-cubicAFEVerticalPoint X y)).cexp).const_mul
        (cubicAFEScalar t (cubicAFEVerticalPoint X y))
  exact (differentiable_intervalIntegral_of_continuous_derivative F F' hF hF' hd (-V) V).const_mul _

/-- Extension of the arithmetic product weight to real positive products. -/
noncomputable def cubicAFERealProductWeightFinite (t X V x : ℝ) : ℂ :=
  cubicAFELogProductWeightFinite t X V (Real.log x : ℂ)

theorem cubicAFERealProductWeightFinite_natCast
    (t X V : ℝ) {k : ℕ} (hk : 0 < k) :
    cubicAFERealProductWeightFinite t X V k = cubicAFEProductWeightFinite t X V k := by
  unfold cubicAFERealProductWeightFinite cubicAFELogProductWeightFinite cubicAFEProductWeightFinite
  congr 1
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Nat.ne_of_gt hk))]
  rw [one_div, ← Complex.exp_neg, Complex.natCast_log]
  congr 1
  ring

theorem contDiffOn_cubicAFERealProductWeightFinite
    (t X V : ℝ) (hX : 1 / 2 < X) :
    ContDiffOn ℝ ∞ (cubicAFERealProductWeightFinite t X V) (Ioi 0) := by
  intro x hx
  have he : ContDiff ℝ ∞ (cubicAFELogProductWeightFinite t X V) :=
    (differentiable_cubicAFELogProductWeightFinite t X V hX).contDiff.restrict_scalars ℝ
  exact (he.contDiffAt.comp x
    (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (Real.contDiffAt_log.mpr (ne_of_gt hx)))).contDiffWithinAt

end PrimeNumberTheorem.MWKFCubic
