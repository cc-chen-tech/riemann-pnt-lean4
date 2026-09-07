import PrimeNumberTheorem.MWKFCubicAFEFourierTimeIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Filter MeasureTheory Set
open scoped ContDiff Interval Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Smooth finite-interval and compactly supported parametric integrals

Local domination comes from compactness of a parameter ball times the
integration interval. The derivative bound is constructed, not assumed.
-/

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [ProperSpace D]

private theorem hasFDerivAt_intervalIntegral_joint
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : D × ℝ → E) (G : D × ℝ → D →L[ℝ] E)
    (hF : Continuous F) (hG : Continuous G)
    (hd : ∀ x y, HasFDerivAt (fun z ↦ F (z, y)) (G (x, y)) x)
    (a b : ℝ) (x : D) :
    HasFDerivAt (fun z ↦ ∫ y : ℝ in a..b, F (z, y))
      (∫ y : ℝ in a..b, G (x, y)) x := by
  have hK : IsCompact (Metric.closedBall x 1 ×ˢ uIcc a b) :=
    (isCompact_closedBall x 1).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.bddAbove_image hG.norm.continuousOn
  have hb : ∀ᵐ y ∂volume.restrict (Ι a b),
      ∀ z ∈ Metric.closedBall x 1, ‖G (z, y)‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
    intro z hz
    exact hC (mem_image_of_mem (fun p : D × ℝ ↦ ‖G p‖)
      (show (z, y) ∈ Metric.closedBall x 1 ×ˢ uIcc a b from
        ⟨hz, uIoc_subset_uIcc hy⟩))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := fun z y ↦ F (z, y)) (F' := fun z y ↦ G (z, y))
    (bound := fun _ ↦ C) (Metric.closedBall_mem_nhds x (by norm_num : (0 : ℝ) < 1))
  · exact Eventually.of_forall (fun z ↦
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact hb
  · exact intervalIntegrable_const
  · exact Eventually.of_forall (fun y z _ ↦ hd z y)

private theorem contDiff_nat_intervalIntegral_joint (n : ℕ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : D × ℝ → E) (hF : ContDiff ℝ n F) (a b : ℝ) :
    ContDiff ℝ n (fun x ↦ ∫ y : ℝ in a..b, F (x, y)) := by
  induction n generalizing E with
  | zero =>
    exact contDiff_zero.mpr
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun x y ↦ F (x, y)) hF.continuous a b)
  | succ n ih =>
    have hF' : ContDiff ℝ ((n : ℕ∞ω) + 1) F := by simpa only [Nat.cast_add, Nat.cast_one] using hF
    have h := contDiff_succ_iff_fderiv.mp hF'
    let G : D × ℝ → D →L[ℝ] E := fun p ↦
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ D ℝ)
    have hG : ContDiff ℝ n G := h.2.2.clm_comp contDiff_const
    have hd : ∀ x y, HasFDerivAt (fun z ↦ F (z, y)) (G (x, y)) x := by
      intro x y
      exact (h.1 (x, y)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x y)
    have hint := hasFDerivAt_intervalIntegral_joint F G hF.continuous hG.continuous hd a b
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp, contDiff_succ_iff_fderiv]
    refine ⟨fun x ↦ (hint x).differentiableAt, by simp, ?_⟩
    have heq : fderiv ℝ (fun x ↦ ∫ y : ℝ in a..b, F (x, y)) =
        fun x ↦ ∫ y : ℝ in a..b, G (x, y) := funext (fun x ↦ (hint x).fderiv)
    rw [heq]
    exact ih G hG

/-- Joint smoothness implies smoothness after integration over a fixed
finite interval. No supplied dominating function or derivative bound. -/
theorem contDiff_intervalIntegral_joint
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : D × ℝ → E) (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x ↦ ∫ y : ℝ in a..b, F (x, y)) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_nat_intervalIntegral_joint n F (contDiff_infty.mp hF n) a b

/-- For a jointly smooth, jointly compactly supported function, the full
real-line marginal is smooth. The compact integration interval is derived
from the projection of the actual closed support. -/
theorem contDiff_integral_joint_compactSupport
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : D × ℝ → E) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ContDiff ℝ ∞ (fun x ↦ ∫ y : ℝ, F (x, y)) := by
  obtain ⟨r, hr⟩ := (hc.image continuous_snd).isBounded.subset_closedBall (0 : ℝ)
  have hs : ∀ x, Function.support (fun y ↦ F (x, y)) ⊆ Ioc (-r - 1) (r + 1) := by
    intro x y hy
    have hb := hr (mem_image_of_mem Prod.snd (subset_tsupport F hy))
    have hnorm : |y| ≤ r := by simpa [Metric.mem_closedBall, Real.dist_eq] using hb
    have hh := abs_le.mp hnorm
    constructor <;> linarith
  have heq : (fun x ↦ ∫ y : ℝ, F (x, y)) =
      fun x ↦ ∫ y : ℝ in (-r - 1)..(r + 1), F (x, y) := by
    funext x
    exact (intervalIntegral.integral_eq_integral_of_support_subset (hs x)).symm
  rw [heq]
  exact contDiff_intervalIntegral_joint F hF _ _

end PrimeNumberTheorem.MWKFCubic
