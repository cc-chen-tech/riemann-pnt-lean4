import HardyTheorem.SelbergJLowMass
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

open Complex MeasureTheory Set
open scoped ENNReal

namespace HardyTheorem

/-! # Genuine integrability of the mass defining Selberg's `J` -/

private theorem integrableOn_selbergJGlobalPairSeries
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {X : ℕ} (hX : 2 ≤ X) :
    IntegrableOn (fun u => selbergJGlobalPairSeries delta theta u X)
      (Ioi x) := by
  let μ : Measure ℝ := volume.restrict (Ioi x)
  let F : (SelbergJOuterIndex X × (ℕ × ℕ)) → ℝ → ℂ := fun q u =>
    selbergJGlobalExpandedPairIntegrand delta theta X q u
  have hFint : ∀ q, Integrable (F q) μ := by
    intro q
    have ho := Finset.mem_product.mp q.1.property
    have hkl := Finset.mem_product.mp ho.1
    have hmn := Finset.mem_product.mp ho.2
    change IntegrableOn
      (selbergPhysicalExpandedPairIntegrand delta theta X
        q.1.val.1.1 q.1.val.1.2 q.1.val.2.1 q.1.val.2.2 q.2) (Ioi x)
    exact integrableOn_selbergPhysicalExpandedPairIntegrand
      hdelta hdelta1 htheta hx hX
      (Finset.mem_Icc.mp hkl.1).1 (Finset.mem_Icc.mp hkl.1).2
      (Finset.mem_Icc.mp hkl.2).1 (Finset.mem_Icc.mp hkl.2).2
      (Finset.mem_Icc.mp hmn.1).1 (Finset.mem_Icc.mp hmn.1).2
      (Finset.mem_Icc.mp hmn.2).1 (Finset.mem_Icc.mp hmn.2).2 q.2
  have hFsum : Summable (fun q => ∫ u, ‖F q u‖ ∂μ) := by
    simpa only [μ, F] using
      summable_integral_norm_selbergJGlobalExpandedPairIntegrand
        hdelta hdelta1 htheta hx hX
  let L : (SelbergJOuterIndex X × (ℕ × ℕ)) → (ℝ →₁[μ] ℂ) := fun q =>
    (hFint q).toL1 (F q)
  have hLnorm : Summable (fun q => ‖L q‖) := by
    apply hFsum.congr
    intro q
    change (∫ u, ‖F q u‖ ∂μ) = ‖(hFint q).toL1 (F q)‖
    rw [Integrable.norm_toL1_eq_lintegral_enorm,
      ← integral_norm_eq_lintegral_enorm (hFint q).aestronglyMeasurable]
  have hLenorm : (∑' q, ‖L q‖ₑ) ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hLnorm
  let S : ℝ →₁[μ] ℂ := ∑' q, L q
  have hScoe : (fun u => S u) =ᵐ[μ] fun u => ∑' q, L q u := by
    simpa only [S] using (Lp.coeFn_tsum hLenorm)
  have hLcoe : ∀ᵐ u ∂μ, ∀ q, L q u = F q u := by
    rw [ae_all_iff]
    intro q
    exact Integrable.coeFn_toL1 (hFint q)
  have hseries : (fun u => S u) =ᵐ[μ]
      fun u => selbergJGlobalPairSeries delta theta u X := by
    filter_upwards [hScoe, hLcoe] with u hsum hterm
    rw [hsum]
    unfold selbergJGlobalPairSeries
    apply tsum_congr
    intro q
    exact hterm q
  exact (L1.integrable_coeFn S).congr hseries

/-- The nonnegative physical kernel occurring in `J` is genuinely
integrable after multiplication by `u^(-theta)`.  This is extracted from
the already proved six-index absolute-Fubini majorant. -/
theorem integrableOn_selbergJ_weightedPhysicalNormSq
    {delta theta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) {X : ℕ} (hX : 2 ≤ X) :
    IntegrableOn
      (fun u : ℝ => u ^ (-theta) * Complex.normSq
        (selbergPhysicalThetaKernel delta u X)) (Ioi 1) := by
  have hseries := integrableOn_selbergJGlobalPairSeries
    hdelta hdelta1 htheta (le_refl 1) hX
  have hreal : IntegrableOn
      (fun u => (selbergJGlobalPairSeries delta theta u X).re) (Ioi 1) :=
    hseries.re
  apply hreal.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := zero_lt_one.trans hu
  rw [selbergJGlobalPairSeries_eq_physicalPairSeries
    hdelta hdelta1 hu0,
    selbergPhysicalPairSeries_eq_weighted_normSq_kernel
      hdelta hdelta1 hu0]
  simp

/-- The unweighted physical theta mass is integrable on the full positive
tail. -/
theorem integrableOn_selbergPhysicalThetaKernel_normSq
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {X : ℕ} (hX : 2 ≤ X) :
    IntegrableOn
      (fun u : ℝ => Complex.normSq
        (selbergPhysicalThetaKernel delta u X)) (Ioi 1) := by
  simpa using integrableOn_selbergJ_weightedPhysicalNormSq
    hdelta hdelta1 (show (0 : ℝ) ≤ 0 by rfl) hX

/-- Measurability on every finite low-mass interval, obtained by restricting
the genuine unweighted integrability theorem. -/
theorem aestronglyMeasurableOn_selbergPhysicalThetaKernel_normSq
    {delta G : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {X : ℕ} (hX : 2 ≤ X) :
    AEStronglyMeasurable
      (fun u : ℝ => Complex.normSq
        (selbergPhysicalThetaKernel delta u X))
      (volume.restrict (Ioc 1 G)) := by
  exact (integrableOn_selbergPhysicalThetaKernel_normSq
    hdelta hdelta1 hX).aestronglyMeasurable.mono_measure
      (Measure.restrict_mono (fun _u hu => hu.1) le_rfl)

end HardyTheorem
