import MathlibAux.SlidingIntervalCorrelation

open MeasureTheory Set

namespace MathlibAux

/-- The mass of `g` in the length-`H` interval starting at `t`. -/
noncomputable def slidingWindowMass (g : ℝ → ℝ) (H t : ℝ) : ℝ :=
  ∫ u in t..t + H, g u

/-- Chebyshev's inequality for sliding-window masses on a restricted interval.

The explicit integrability hypothesis is necessary: the Bochner integral is
defined to be zero for non-integrable functions. -/
theorem volume_slidingWindowMass_ge_le
    {g : ℝ → ℝ} {A B H M lambda : ℝ}
    (hg : Measurable g) (hg_nonneg : ∀ u, 0 ≤ g u) (hH : 0 < H)
    (hmass_integrable :
      Integrable (slidingWindowMass g H) (volume.restrict (Icc A B)))
    (hmass_bound :
      (∫ t, slidingWindowMass g H t ∂volume.restrict (Icc A B)) ≤ M)
    (hlambda : 0 < lambda) :
    volume.real ({t | lambda ≤ slidingWindowMass g H t} ∩ Icc A B) ≤
      M / lambda := by
  have _hg_ae : AEMeasurable g volume := hg.aemeasurable
  have hmass_nonneg :
      0 ≤ᵐ[volume.restrict (Icc A B)] slidingWindowMass g H := by
    filter_upwards with t
    exact intervalIntegral.integral_nonneg_of_forall
      (by linarith) hg_nonneg
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := volume.restrict (Icc A B)) hmass_nonneg hmass_integrable lambda
  rw [measureReal_restrict_apply' measurableSet_Icc] at hmarkov
  have hscaled :
      lambda * volume.real
          ({t | lambda ≤ slidingWindowMass g H t} ∩ Icc A B) ≤ M :=
    hmarkov.trans hmass_bound
  exact (le_div_iff₀ hlambda).2 (by simpa [mul_comm] using hscaled)

/-- Strict-threshold version of `volume_slidingWindowMass_ge_le`. -/
theorem volume_slidingWindowMass_gt_le
    {g : ℝ → ℝ} {A B H M lambda : ℝ}
    (hg : Measurable g) (hg_nonneg : ∀ u, 0 ≤ g u) (hH : 0 < H)
    (hmass_integrable :
      Integrable (slidingWindowMass g H) (volume.restrict (Icc A B)))
    (hmass_bound :
      (∫ t, slidingWindowMass g H t ∂volume.restrict (Icc A B)) ≤ M)
    (hlambda : 0 < lambda) :
    volume.real ({t | lambda < slidingWindowMass g H t} ∩ Icc A B) ≤
      M / lambda := by
  have hsubset :
      ({t | lambda < slidingWindowMass g H t} ∩ Icc A B) ⊆
        ({t | lambda ≤ slidingWindowMass g H t} ∩ Icc A B) := by
    intro t ht
    constructor
    · change lambda ≤ slidingWindowMass g H t
      exact ht.1.le
    · exact ht.2
  have hfinite :
      volume ({t | lambda ≤ slidingWindowMass g H t} ∩ Icc A B) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  exact (measureReal_mono hsubset hfinite).trans
    (volume_slidingWindowMass_ge_le hg hg_nonneg hH
      hmass_integrable hmass_bound hlambda)

end MathlibAux
