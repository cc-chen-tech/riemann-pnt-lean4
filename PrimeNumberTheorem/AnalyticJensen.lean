import PrimeNumberTheorem.CarlsonZeroDetector
import Mathlib.Analysis.Meromorphic.Divisor

open Complex MeasureTheory MeromorphicOn Real

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- A uniform norm bound on a circle gives the corresponding logarithmic
circle-average bound for every meromorphic function on the enclosed disk. -/
theorem circleAverage_log_norm_le_log_of_norm_le
    {f : ℂ → ℂ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R)
    (hmeromorphic : MeromorphicOn f (Metric.closedBall c R))
    (hM : 1 ≤ M)
    (hsphere : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ M) :
    circleAverage (Real.log ‖f ·‖) c R ≤ Real.log M := by
  have hcircle_integrable :
      CircleIntegrable (Real.log ‖f ·‖) c R := by
    apply circleIntegrable_log_norm_meromorphicOn
    intro z hz
    exact hmeromorphic z
      (Metric.sphere_subset_closedBall (by simpa [abs_of_pos hR] using hz))
  refine circleAverage_mono_on_of_le_circle hcircle_integrable ?_
  intro z hz
  by_cases hfz : f z = 0
  · simp [hfz, Real.log_nonneg hM]
  · exact Real.log_le_log (norm_pos_iff.mpr hfz)
      (hsphere z (by simpa [abs_of_pos hR] using hz))

/-- Jensen's formula bounds the weighted zero mass of any analytic function by
its boundary average, provided the value at the center is bounded away from
zero.  This is the function-agnostic input needed for Carlson's detector. -/
theorem jensen_weighted_zero_mass_le_of_circleAverage_le
    {f : ℂ → ℂ} {c : ℂ} {R K m : ℝ}
    (hR : 0 < R)
    (hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hm : 0 < m) (hcenter : m ≤ ‖f c‖)
    (hcircle : circleAverage (Real.log ‖f ·‖) c R ≤ K) :
    (∑ᶠ u, (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ) *
        Real.log (R * ‖c - u‖⁻¹)) ≤
      K - Real.log m := by
  have hc_mem : c ∈ Metric.closedBall c R := by simp [hR.le]
  have hc_analytic : AnalyticAt ℂ f c := hanalytic c hc_mem
  have hc_pos : 0 < ‖f c‖ := hm.trans_le hcenter
  have hc_ne : f c ≠ 0 := norm_pos_iff.mp hc_pos
  have hdiv_center :
      MeromorphicOn.divisor f (Metric.closedBall c R) c = 0 := by
    rw [MeromorphicOn.divisor_apply hanalytic.meromorphicOn hc_mem]
    rw [(hc_analytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).2 hc_ne]
    simp
  have htrail : meromorphicTrailingCoeffAt f c = f c :=
    hc_analytic.meromorphicTrailingCoeffAt_of_ne_zero hc_ne
  have hAbs : |R| = R := abs_of_pos hR
  have hmeromorphic :
      MeromorphicOn f (Metric.closedBall c |R|) := by
    simpa [hAbs] using hanalytic.meromorphicOn
  have hjensen := hmeromorphic.circleAverage_log_norm hR.ne'
  rw [hAbs] at hjensen
  simp only [hdiv_center, Int.cast_zero, zero_mul, add_zero, htrail] at hjensen
  have hlog_center : Real.log m ≤ Real.log ‖f c‖ :=
    Real.log_le_log hm hcenter
  linarith

/-- Jensen's weighted estimate controls the total analytic zero multiplicity
inside every strictly smaller concentric disk. -/
theorem jensen_inner_zero_multiplicity_le_of_circleAverage_le
    {f : ℂ → ℂ} {c : ℂ} {r R K m : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hm : 0 < m) (hcenter : m ≤ ‖f c‖)
    (hcircle : circleAverage (Real.log ‖f ·‖) c R ≤ K) :
    Real.log (R / r) *
        (∑ᶠ u ∈ (Metric.closedBall c r : Set ℂ),
          (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ)) ≤
      K - Real.log m := by
  classical
  let D := MeromorphicOn.divisor f (Metric.closedBall c R)
  have hR : 0 < R := hr.trans hrR
  have hD_nonneg : 0 ≤ D := hanalytic.divisor_nonneg
  have hD_finite : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall c R)
  have hc_mem : c ∈ Metric.closedBall c R := by simp [hR.le]
  have hc_analytic : AnalyticAt ℂ f c := hanalytic c hc_mem
  have hc_pos : 0 < ‖f c‖ := hm.trans_le hcenter
  have hc_ne : f c ≠ 0 := norm_pos_iff.mp hc_pos
  have hD_center : D c = 0 := by
    dsimp [D]
    rw [MeromorphicOn.divisor_apply hanalytic.meromorphicOn hc_mem]
    rw [(hc_analytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).2 hc_ne]
    simp
  have hpoint : ∀ u : ℂ,
      (Metric.closedBall c r).indicator
          (fun v : ℂ => Real.log (R / r) * (D v : ℝ)) u ≤
        (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := by
    intro u
    by_cases hDu : D u = 0
    · by_cases hu_inner : u ∈ Metric.closedBall c r
      · simp [Set.indicator_of_mem hu_inner, hDu]
      · simp [hu_inner, hDu]
    have hu_support : u ∈ D.support := by
      simpa [Function.mem_support] using hDu
    have hu_outer : u ∈ Metric.closedBall c R :=
      D.supportWithinDomain hu_support
    have hDu_nonneg : 0 ≤ (D u : ℝ) := by
      exact_mod_cast hD_nonneg u
    have hu_ne : u ≠ c := by
      intro huc
      subst u
      exact hDu hD_center
    have hnorm_pos : 0 < ‖c - u‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hu_ne.symm)
    have hnorm_outer : ‖c - u‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hu_outer
    by_cases hu_inner : u ∈ Metric.closedBall c r
    · have hnorm_inner : ‖c - u‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hu_inner
      have hratio_pos : 0 < R / r := div_pos hR hr
      have hratio_le : R / r ≤ R / ‖c - u‖ :=
        div_le_div_of_nonneg_left hR.le hnorm_pos hnorm_inner
      have hlog_le : Real.log (R / r) ≤ Real.log (R / ‖c - u‖) :=
        Real.log_le_log hratio_pos hratio_le
      simpa [Set.indicator_of_mem hu_inner, div_eq_mul_inv, mul_comm] using
        (mul_le_mul_of_nonneg_left hlog_le hDu_nonneg)
    · have hone_le : (1 : ℝ) ≤ R / ‖c - u‖ := by
        apply (le_div_iff₀ hnorm_pos).2
        simpa using hnorm_outer
      have hlog_nonneg : 0 ≤ Real.log (R / ‖c - u‖) :=
        Real.log_nonneg hone_le
      simpa [hu_inner, div_eq_mul_inv] using
        mul_nonneg hDu_nonneg hlog_nonneg
  have hleft_support :
      ((Metric.closedBall c r).indicator
        (fun u : ℂ => Real.log (R / r) * (D u : ℝ))).support ⊆
        hD_finite.toFinset := by
    intro u hu
    apply hD_finite.mem_toFinset.mpr
    by_contra hDu
    have hDu_zero : D u = 0 := by
      simpa [Function.mem_support] using hDu
    simp [hDu_zero] at hu
  have hright_support :
      (fun u : ℂ => (D u : ℝ) *
        Real.log (R * ‖c - u‖⁻¹)).support ⊆ hD_finite.toFinset := by
    intro u hu
    apply hD_finite.mem_toFinset.mpr
    by_contra hDu
    have hDu_zero : D u = 0 := by
      simpa [Function.mem_support] using hDu
    simp [hDu_zero] at hu
  have hsum_le :
      (∑ᶠ u ∈ (Metric.closedBall c r : Set ℂ),
        Real.log (R / r) * (D u : ℝ)) ≤
        ∑ᶠ u : ℂ, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := by
    rw [finsum_mem_def]
    rw [finsum_eq_sum_of_support_subset _ hleft_support]
    rw [finsum_eq_sum_of_support_subset _ hright_support]
    exact Finset.sum_le_sum fun u _hu => hpoint u
  have hmass := jensen_weighted_zero_mass_le_of_circleAverage_le
    hR hanalytic hm hcenter hcircle
  calc
    Real.log (R / r) *
        (∑ᶠ u ∈ (Metric.closedBall c r : Set ℂ),
          (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ)) =
        ∑ᶠ u ∈ (Metric.closedBall c r : Set ℂ),
          Real.log (R / r) * (D u : ℝ) := by
            rw [mul_finsum_mem]
    _ ≤ ∑ᶠ u : ℂ, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := hsum_le
    _ ≤ K - Real.log m := by simpa [D] using hmass

/-- Division form of the generic Jensen inner zero-multiplicity bound. -/
theorem jensen_inner_zero_multiplicity_le_log_div
    {f : ℂ → ℂ} {c : ℂ} {r R K m : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hm : 0 < m) (hcenter : m ≤ ‖f c‖)
    (hcircle : circleAverage (Real.log ‖f ·‖) c R ≤ K) :
    (∑ᶠ u ∈ (Metric.closedBall c r : Set ℂ),
        (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ)) ≤
      (K - Real.log m) / Real.log (R / r) := by
  have hlog : 0 < Real.log (R / r) :=
    Real.log_pos ((one_lt_div hr).mpr hrR)
  apply (le_div_iff₀ hlog).2
  simpa [mul_comm] using
    jensen_inner_zero_multiplicity_le_of_circleAverage_le
      hr hrR hanalytic hm hcenter hcircle

/-- On an analytic disk of radius at least one, the center-evaluated divisor
contribution is at most `log b` times the total zero multiplicity. -/
theorem finsum_divisor_mul_log_norm_center_sub_le_log_mul_mass
    {f : ℂ → ℂ} {c : ℂ} {b : ℝ} (hb : 1 ≤ b)
    (hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall c b))
    (hc : f c ≠ 0) :
    (∑ᶠ u,
        (MeromorphicOn.divisor f (Metric.closedBall c b) u : ℝ) *
          Real.log ‖c - u‖) ≤
      Real.log b *
        (∑ᶠ u,
          (MeromorphicOn.divisor f (Metric.closedBall c b) u : ℝ)) := by
  classical
  let U : Set ℂ := Metric.closedBall c b
  let D := MeromorphicOn.divisor f U
  have hD_nonneg : 0 ≤ D := hanalytic.divisor_nonneg
  have hD_finite : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall c b)
  have hcU : c ∈ U := by simp [U, (zero_le_one.trans hb)]
  have hDc : D c = 0 := by
    rw [show D c = MeromorphicOn.divisor f U c by rfl]
    rw [MeromorphicOn.divisor_apply hanalytic.meromorphicOn hcU]
    have hnormal := (hanalytic c hcU).meromorphicNFAt
    rw [(hnormal.meromorphicOrderAt_eq_zero_iff).2 hc]
    simp
  have hleft_support :
      (fun u : ℂ => (D u : ℝ) * Real.log ‖c - u‖).support ⊆
        hD_finite.toFinset := by
    intro u hu
    apply hD_finite.mem_toFinset.mpr
    by_contra hDu
    have hDu_zero : D u = 0 := by
      simpa [Function.mem_support] using hDu
    simp [hDu_zero] at hu
  have hright_support :
      (fun u : ℂ => (D u : ℝ)).support ⊆ hD_finite.toFinset := by
    intro u hu
    exact hD_finite.mem_toFinset.mpr (by
      simpa [Function.mem_support] using hu)
  rw [show (∑ᶠ u,
      (MeromorphicOn.divisor f (Metric.closedBall c b) u : ℝ) *
        Real.log ‖c - u‖) =
      ∑ᶠ u, (D u : ℝ) * Real.log ‖c - u‖ by rfl]
  rw [show (∑ᶠ u,
      (MeromorphicOn.divisor f (Metric.closedBall c b) u : ℝ)) =
      ∑ᶠ u, (D u : ℝ) by rfl]
  rw [finsum_eq_sum_of_support_subset _ hleft_support,
    finsum_eq_sum_of_support_subset _ hright_support, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hu_support : u ∈ D.support := hD_finite.mem_toFinset.mp hu
  have huU : u ∈ U := D.supportWithinDomain hu_support
  have huc : u ≠ c := by
    intro h
    subst u
    have hne : D c ≠ 0 := by
      simpa [Function.mem_support] using hu_support
    exact hne hDc
  have hnorm_pos : 0 < ‖c - u‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr huc.symm)
  have hnorm_le : ‖c - u‖ ≤ b := by
    simpa [U, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using huU
  have hlog : Real.log ‖c - u‖ ≤ Real.log b :=
    Real.log_le_log hnorm_pos hnorm_le
  have hDreal : (0 : ℝ) ≤ (D u : ℝ) := by
    exact_mod_cast hD_nonneg u
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hlog hDreal

/-- Extract all zeros of an analytic function on a closed disk and identify
the logarithmic norm of the resulting nonvanishing factor at the center. -/
theorem exists_analytic_nonzero_factor_log_norm_at_center
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hnotop : ∀ u : (Metric.closedBall c R : Set ℂ),
      meromorphicOrderAt f u ≠ ⊤)
    (hc : f c ≠ 0) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.closedBall c R) ∧
      (∀ u : (Metric.closedBall c R : Set ℂ), g u ≠ 0) ∧
      Real.log ‖f c‖ =
        (∑ᶠ u,
          (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ) *
            Real.log ‖c - u‖) + Real.log ‖g c‖ := by
  let U : Set ℂ := Metric.closedBall c R
  have hmer : MeromorphicOn f U := hanalytic.meromorphicOn
  have hfinite : (MeromorphicOn.divisor f U).support.Finite :=
    (MeromorphicOn.divisor f U).finiteSupport (isCompact_closedBall c R)
  rcases hmer.extract_zeros_poles hnotop hfinite with ⟨g, hg, hgne, hfactor⟩
  have hcU : c ∈ U := by simp [U, hR.le]
  have hcBall : c ∈ Metric.ball c R := by simp [hR]
  have haccUniv : AccPt c (Filter.principal (Set.univ : Set ℂ)) :=
    PerfectSpace.univ_preperfect c (Set.mem_univ c)
  have hacc : AccPt c (Filter.principal U) := by
    have hnhds : U ∈ nhds c := by
      exact Metric.closedBall_mem_nhds_of_mem hcBall
    simpa [U] using haccUniv.nhds_inter hnhds
  have hlog :=
    MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles
      hfinite hcU hacc (hmer c hcU) (hg c hcU)
        (hgne ⟨c, hcU⟩) hfactor
  rw [(hanalytic c hcU).meromorphicTrailingCoeffAt_of_ne_zero hc] at hlog
  refine ⟨g, by simpa [U] using hg, by simpa [U] using hgne, ?_⟩
  simpa [U] using hlog

/-- Divisor mass is local on nested closed disks: the divisor computed on the
inner disk equals the outer divisor restricted to that disk. -/
theorem finsum_divisor_closedBall_eq_finsum_mem_of_le
    {f : ℂ → ℂ} {c : ℂ} {b R : ℝ} (hbR : b ≤ R)
    (hmeromorphic : MeromorphicOn f (Metric.closedBall c R)) :
    (∑ᶠ u,
        (MeromorphicOn.divisor f (Metric.closedBall c b) u : ℝ)) =
      ∑ᶠ u ∈ (Metric.closedBall c b : Set ℂ),
        (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ) := by
  rw [finsum_mem_def]
  apply finsum_congr
  intro u
  by_cases hu : u ∈ Metric.closedBall c b
  · rw [Set.indicator_of_mem hu,
      MeromorphicOn.divisor_apply
        (hmeromorphic.mono_set (Metric.closedBall_subset_closedBall hbR)) hu,
      MeromorphicOn.divisor_apply hmeromorphic
        (Metric.closedBall_subset_closedBall hbR hu)]
  · simp [hu, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem]

end CarlsonZeroDensity
end PrimeNumberTheorem
