import PrimeNumberTheorem.MWKFCubicAFECompletedHeight

open Complex Filter MeasureTheory Set
open scoped Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Actual compact-time domination of the complete Mellin scalar

The inverse unshifted gamma product is continuous and hence bounded on
each compact time set. This makes the Gaussian majorant uniform on that
set, on either side of X=0. It is not a bound uniform as T tends to infinity.
-/

theorem continuous_cubicAFEGammaProduct_zero_inv :
    Continuous (fun t : ℝ ↦ (cubicAFEGammaProduct t 0)⁻¹) := by
  have hs : Continuous cubicCriticalPoint := by unfold cubicCriticalPoint; fun_prop
  have hu : Continuous (fun t ↦ 1 - cubicCriticalPoint t) := continuous_const.sub hs
  have hGs : Continuous (fun t ↦ (Gammaℝ (cubicCriticalPoint t))⁻¹) :=
    differentiable_Gammaℝ_inv.continuous.comp hs
  have hGu : Continuous (fun t ↦ (Gammaℝ (1 - cubicCriticalPoint t))⁻¹) :=
    differentiable_Gammaℝ_inv.continuous.comp hu
  have hh : Continuous (fun t ↦ (Gammaℝ (1 - cubicCriticalPoint t))⁻¹ *
      (Gammaℝ (cubicCriticalPoint t))⁻¹) := hGu.mul hGs
  simpa only [cubicAFEGammaProduct, add_zero, mul_inv_rev] using hh

theorem continuous_cubicAFEScalar_joint_of_halfPlane {X : ℝ}
    (hX : -1 / 2 < X) (hne : X ≠ 0) :
    Continuous (fun p : ℝ × ℝ ↦ cubicAFEScalar p.1 (cubicAFEVerticalPoint X p.2)) := by
  let s : ℝ × ℝ → ℂ := fun p ↦ cubicCriticalPoint p.1
  let u : ℝ × ℝ → ℂ := fun p ↦ 1 - s p
  let z : ℝ × ℝ → ℂ := fun p ↦ cubicAFEVerticalPoint X p.2
  have hs : Continuous s := by unfold s cubicCriticalPoint; fun_prop
  have hu : Continuous u := continuous_const.sub hs
  have hz : Continuous z := by unfold z cubicAFEVerticalPoint; fun_prop
  have hgamma {f : ℝ × ℝ → ℂ} (hf : Continuous f) (hp : ∀ p, 0 < (f p).re) :
      Continuous (fun p ↦ Gammaℝ (f p)) := by
    have hi : Continuous (fun p ↦ (Gammaℝ (f p))⁻¹) :=
      differentiable_Gammaℝ_inv.continuous.comp hf
    have hii : Continuous (fun p ↦ ((Gammaℝ (f p))⁻¹)⁻¹) :=
      hi.inv₀ (fun p ↦ inv_ne_zero (Gammaℝ_ne_zero_of_re_pos (hp p)))
    simpa only [inv_inv] using hii
  have hGs := hgamma (hs.add hz) (fun p ↦ by
    simp [s, z, cubicCriticalPoint, cubicAFEVerticalPoint]; linarith)
  have hGu := hgamma (hu.add hz) (fun p ↦ by
    norm_num [u, s, z, cubicCriticalPoint, cubicAFEVerticalPoint]; linarith)
  have hk : Continuous (fun p ↦ cubicAFEKernelG p.1 (z p)) := by
    have hs0 : ∀ p, s p ≠ 0 := fun p ↦ cubicCriticalPoint_ne_zero p.1
    have hu0 : ∀ p, u p ≠ 0 := fun p ↦ one_sub_cubicCriticalPoint_ne_zero p.1
    unfold cubicAFEKernelG cubicAFEPoleCanceller
    exact (Complex.continuous_exp.comp (hz.pow 2)).mul
      (((continuous_const.sub (continuous_const.mul (hz.pow 2))).mul
        (continuous_const.sub ((hz.pow 2).div₀ (hs.pow 2) (fun p ↦ pow_ne_zero 2 (hs0 p))))).mul
        (continuous_const.sub ((hz.pow 2).div₀ (hu.pow 2) (fun p ↦ pow_ne_zero 2 (hu0 p)))))
  have hz0 (p : ℝ × ℝ) : z p ≠ 0 := by
    intro hh
    exact hne (by simpa [z, cubicAFEVerticalPoint] using congrArg Complex.re hh)
  have hi : Continuous (fun p : ℝ × ℝ ↦ (cubicAFEGammaProduct p.1 0)⁻¹) :=
    continuous_cubicAFEGammaProduct_zero_inv.comp continuous_fst
  have hh : Continuous (fun p ↦ cubicAFEKernelG p.1 (z p) *
      (Gammaℝ (s p + z p) * Gammaℝ (u p + z p)) *
      (cubicAFEGammaProduct p.1 0)⁻¹ * (z p)⁻¹) :=
    ((hk.mul (hGs.mul hGu)).mul hi).mul (hz.inv₀ hz0)
  simpa only [cubicAFEScalar, cubicAFEGammaProduct, div_eq_mul_inv, s, u, z] using hh

theorem exists_norm_cubicAFEScalar_vertical_le_on_compact {X : ℝ}
    (hX : -1 / 2 < X) (hne : X ≠ 0) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K, ∀ y : ℝ,
      ‖cubicAFEScalar t (cubicAFEVerticalPoint X y)‖ ≤ C * cubicAFEVerticalGaussianMajorant X y := by
  obtain ⟨C, hC, hgamma⟩ := MathlibAux.exists_norm_Gammaℝ_le_on_positive_reIcc
    (show 0 < 1 / 2 + X by linarith) (show 0 < 1 / 2 + X by linarith)
  obtain ⟨D, hD⟩ := hK.bddAbove_image continuous_cubicAFEGammaProduct_zero_inv.norm.continuousOn
  have hbound (t : ℝ) (ht : t ∈ K) : ‖cubicAFEGammaProduct t 0‖⁻¹ ≤ max D 0 := by
    rw [← norm_inv]
    exact (hD (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  refine ⟨125 * Real.exp (X^2) * C^2 * max D 0 / |X|, by positivity, ?_⟩
  intro t ht y
  have hgp : ‖cubicAFEGammaProduct t (cubicAFEVerticalPoint X y)‖ ≤ C^2 := by
    unfold cubicAFEGammaProduct
    rw [norm_mul, pow_two]
    apply mul_le_mul (hgamma _ ?_ ?_) (hgamma _ ?_ ?_) (norm_nonneg _) hC <;>
      norm_num [cubicCriticalPoint, cubicAFEVerticalPoint]
  have hz : |X| ≤ ‖cubicAFEVerticalPoint X y‖ := by
    simpa [cubicAFEVerticalPoint] using abs_re_le_norm (cubicAFEVerticalPoint X y)
  have hXpos : 0 < |X| := abs_pos.mpr hne
  have hM := cubicAFEVerticalGaussianMajorant_nonneg X y
  unfold cubicAFEScalar
  rw [norm_div, norm_div, norm_mul]
  calc
    _ ≤ ((125 * Real.exp (X^2) * cubicAFEVerticalGaussianMajorant X y) * C^2) /
        ‖cubicAFEGammaProduct t 0‖ / |X| := by
      gcongr
      exact norm_cubicAFEKernelG_vertical_le t X y
    _ = ((125 * Real.exp (X^2) * cubicAFEVerticalGaussianMajorant X y) * C^2) *
        ‖cubicAFEGammaProduct t 0‖⁻¹ / |X| := by ring
    _ ≤ ((125 * Real.exp (X^2) * cubicAFEVerticalGaussianMajorant X y) * C^2 * max D 0) / |X| := by
      gcongr
      exact hbound t ht
    _ = _ := by ring

theorem continuous_cubicAFEWeightNormMass {X : ℝ} (hX : -1 / 2 < X) (hne : X ≠ 0) :
    Continuous (fun t : ℝ ↦ cubicAFEWeightNormMass t X) := by
  apply Continuous.const_mul
  apply continuous_iff_continuousAt.mpr
  intro t₀
  obtain ⟨C, _, hC⟩ := exists_norm_cubicAFEScalar_vertical_le_on_compact hX hne
    (isCompact_Icc : IsCompact (Icc (t₀ - 1) (t₀ + 1)))
  apply continuousAt_of_dominated
    (bound := fun y ↦ C * cubicAFEVerticalGaussianMajorant X y)
  · exact Eventually.of_forall (fun t ↦
      (continuous_cubicAFEScalar_vertical_of_halfPlane t hX hne).norm.aestronglyMeasurable)
  · filter_upwards [Icc_mem_nhds (by linarith : t₀ - 1 < t₀) (by linarith : t₀ < t₀ + 1)] with t ht
    exact Eventually.of_forall (fun y ↦ by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact hC t ht y)
  · exact (integrable_cubicAFEVerticalGaussianMajorant X).const_mul C
  · exact Eventually.of_forall (fun y ↦
      ((continuous_cubicAFEScalar_joint_of_halfPlane hX hne).comp
        (continuous_id.prodMk continuous_const)).norm.continuousAt)

theorem integrable_cubicAFEPhysicalHeightMass
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ}
    (hX : -1 / 2 < X) (hne : X ≠ 0) (d e : ℕ) :
    Integrable (cubicAFEPhysicalHeightMass W T X d e) := by
  have hc : Continuous (cubicAFEPhysicalHeightMass W T X d e) :=
    (continuous_const.mul (continuous_cubicAFEWeightNormMass hX hne)).mul
      (W.continuous.comp (continuous_id.div_const T)).norm
  exact hc.integrable_of_hasCompactSupport (W.hasCompactSupport_dilate hT).norm.mul_left

end PrimeNumberTheorem.MWKFCubic
