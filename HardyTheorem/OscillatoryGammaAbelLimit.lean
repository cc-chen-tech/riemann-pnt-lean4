import HardyTheorem.OscillatoryGammaAbelTail

open Real Complex Set MeasureTheory Filter Topology

namespace HardyTheorem.OscillatoryGammaAbelLimit

/-!
# Abel boundary value of the negative-phase Gamma integral

For `0 < Re z < 1`, the conditionally convergent integral with phase
`exp (-i c u)` is assembled from its integrable origin and the canonical
oscillatory tail.  Positive exponential damping converges to that value as
the damping parameter tends to zero from the right.
-/

open HardyTheorem.OscillatoryGammaAbelTail
open HardyTheorem.OscillatoryGammaCompactLimit

/-- The absolutely convergent negative-phase Gamma integral with positive
damping. -/
noncomputable def dampedGammaNegWhole (z : ℂ) (c r : ℝ) : ℂ :=
  ∫ u in Ioi (0 : ℝ),
    (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
      Complex.exp (-I * (c * u))

/-- The canonical negative-phase Gamma boundary value.  The origin is an
ordinary integral and the tail is the natural oscillatory limit. -/
noncomputable def oscillatoryGammaNegWhole (z : ℂ) (c : ℝ) : ℂ :=
  (∫ u in (0 : ℝ)..1,
    (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u))) +
      oscillatoryGammaNegBoundary z c

private theorem intervalIntegrable_gammaNeg_zero_right
    {z : ℂ} {c b : ℝ} (hz0 : 0 < z.re) (hb : 0 ≤ b) :
    IntervalIntegrable
      (fun u : ℝ => (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u)))
      volume 0 b := by
  let f : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u))
  let G : ℝ → ℝ := fun u => u ^ (z.re - 1)
  have hG : IntervalIntegrable G volume 0 b := by
    dsimp only [G]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hfcont : ContinuousOn f (uIoc (0 : ℝ) b) := by
    intro u hu
    have huIoc : u ∈ Ioc (0 : ℝ) b := by
      simpa [uIoc_of_le hb] using hu
    have hupos : 0 < u := huIoc.1
    have hpow : ContinuousAt (fun v : ℝ => (v : ℂ) ^ (z - 1)) u :=
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hupos.ne')
    have hphase : ContinuousAt (fun v : ℝ => Complex.exp (-I * (c * v))) u := by
      fun_prop
    exact (hpow.mul hphase).continuousWithinAt
  rw [intervalIntegrable_iff]
  apply hG.def'.mono' (hfcont.aestronglyMeasurable measurableSet_uIoc)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  have huIoc : u ∈ Ioc (0 : ℝ) b := by
    simpa [uIoc_of_le hb] using hu
  have hupos : 0 < u := huIoc.1
  dsimp only [f, G]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hupos]
  have hphaseNorm : ‖Complex.exp (-I * (c * u))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hphaseNorm, mul_one]
  simp

private theorem dampedGammaNegWhole_eq_interval_add_tail
    {z : ℂ} {c r b : ℝ} (hz0 : 0 < z.re) (hr : 0 < r) (hb : 0 ≤ b) :
    dampedGammaNegWhole z c r =
      (∫ u in (0 : ℝ)..b,
        (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
          Complex.exp (-I * (c * u))) +
      ∫ u in Ioi b,
        (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
          Complex.exp (-I * (c * u)) := by
  let g : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
      Complex.exp (-I * (c * u))
  have hfull : IntegrableOn g (Ioi 0) :=
    integrableOn_dampedGammaNeg_Ioi_zero hz0 hr
  have htail : IntegrableOn g (Ioi b) :=
    hfull.mono_set (Ioi_subset_Ioi hb)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hfull htail
  simpa [dampedGammaNegWhole, g] using hsplit.symm

private theorem oscillatoryGammaNegWhole_sub_interval
    {z : ℂ} {c : ℝ} (hz0 : 0 < z.re) {N : ℕ} (hN : 1 ≤ N) :
    oscillatoryGammaNegWhole z c -
        (∫ u in (0 : ℝ)..(N : ℝ),
          (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u))) =
      oscillatoryGammaNegBoundary z c - oscillatoryGammaNegPartial z c N := by
  let f : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u))
  have h01 : IntervalIntegrable f volume 0 1 :=
    intervalIntegrable_gammaNeg_zero_right hz0 (by norm_num)
  have h1N : IntervalIntegrable f volume 1 (N : ℝ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc
    · exact_mod_cast hN
    · intro u hu
      have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu.1
      have hpow : ContinuousAt (fun v : ℝ => (v : ℂ) ^ (z - 1)) u :=
        Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hupos.ne')
      have hphase : ContinuousAt (fun v : ℝ => Complex.exp (-I * (c * v))) u := by
        fun_prop
      exact (hpow.mul hphase).continuousWithinAt
  have hadd := intervalIntegral.integral_add_adjacent_intervals h01 h1N
  dsimp only [oscillatoryGammaNegWhole, oscillatoryGammaNegPartial]
  change ((∫ u in (0 : ℝ)..1, f u) + oscillatoryGammaNegBoundary z c) -
      (∫ u in (0 : ℝ)..(N : ℝ), f u) =
    oscillatoryGammaNegBoundary z c - (∫ u in (1 : ℝ)..(N : ℝ), f u)
  rw [← hadd]
  ring

/-- Abel damping converges to the canonical negative-phase Gamma boundary
value throughout the critical strip `0 < Re z < 1`. -/
theorem tendsto_dampedGammaNegWhole_nhdsWithin_zero
    {z : ℂ} {c : ℝ} (hz0 : 0 < z.re) (hz1 : z.re < 1) (hc : 0 < c) :
    Tendsto (dampedGammaNegWhole z c) (nhdsWithin 0 (Ioi 0))
      (nhds (oscillatoryGammaNegWhole z c)) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  have hp : 0 < 1 - z.re := by linarith
  have hpowReal :
      Tendsto (fun A : ℝ => 8 * A ^ (z.re - 1) / c) atTop (nhds 0) := by
    have hbase := tendsto_rpow_neg_atTop hp
    have hmul : Tendsto
        (fun A : ℝ => (8 / c) * A ^ (-(1 - z.re))) atTop
        (nhds ((8 / c) * 0)) := tendsto_const_nhds.mul hbase
    convert hmul using 1
    · funext A
      rw [show z.re - 1 = -(1 - z.re) by ring]
      ring
    · simp
  have hpowNat : Tendsto
      (fun N : ℕ => 8 * (N : ℝ) ^ (z.re - 1) / c) atTop (nhds 0) :=
    hpowReal.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ N : ℕ in atTop,
      8 * (N : ℝ) ^ (z.re - 1) / c < eps / 3 :=
    (tendsto_order.1 hpowNat).2 (eps / 3) (by positivity)
  have hlarge : ∀ᶠ N : ℕ in atTop,
      2 * |z.im| / c ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * |z.im| / c)
  have hgood : ∀ᶠ N : ℕ in atTop,
      1 ≤ N ∧ 2 * |z.im| / c ≤ (N : ℝ) ∧
        8 * (N : ℝ) ^ (z.re - 1) / c < eps / 3 := by
    filter_upwards [eventually_ge_atTop 1, hlarge, hsmall] with N hN hNl hNs
    exact ⟨hN, hNl, hNs⟩
  obtain ⟨N, hN, hNlarge, hNsmall⟩ := hgood.exists
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have himN : 2 * |z.im| ≤ c * (N : ℝ) := by
    rw [div_le_iff₀ hc] at hNlarge
    nlinarith
  have hcompact :=
    tendsto_intervalIntegral_dampedGamma_zero_right_nhdsWithin_zero
      (z := z) (c := c) hz0 hNpos.le
  have hcompactStrict : Tendsto
      (fun r : ℝ => ∫ u in (0 : ℝ)..(N : ℝ),
        (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
          Complex.exp (-I * (c * u)))
      (nhdsWithin 0 (Ioi 0))
      (nhds (∫ u in (0 : ℝ)..(N : ℝ),
        (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u)))) :=
    hcompact.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hcompactSmall : ∀ᶠ (r : ℝ) in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)),
      ‖(∫ u in (0 : ℝ)..(N : ℝ),
          (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
            Complex.exp (-I * (c * u))) -
        (∫ u in (0 : ℝ)..(N : ℝ),
          (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u)))‖ < eps / 3 := by
    have h := (Metric.tendsto_nhds.1 hcompactStrict) (eps / 3) (by positivity)
    simpa [dist_eq_norm] using h
  filter_upwards [self_mem_nhdsWithin, hcompactSmall] with r hr hrCompact
  have hdampedSplit := dampedGammaNegWhole_eq_interval_add_tail
    (z := z) (c := c) (r := r) (b := (N : ℝ)) hz0 hr hNpos.le
  have hboundarySplit := oscillatoryGammaNegWhole_sub_interval
    (z := z) (c := c) hz0 hN
  have hdampedTail := norm_integral_dampedGammaNeg_Ioi_le
    (z := z) (r := r) (c := c) (A := (N : ℝ))
    hz0 hz1 hr hc hNpos himN
  have hboundaryTail := norm_oscillatoryGammaNegBoundary_sub_partial_le
    (z := z) (c := c) hz1 hc hN himN
  rw [dist_eq_norm]
  have hidentity :
      dampedGammaNegWhole z c r - oscillatoryGammaNegWhole z c =
        ((∫ u in (0 : ℝ)..(N : ℝ),
            (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
              Complex.exp (-I * (c * u))) -
          (∫ u in (0 : ℝ)..(N : ℝ),
            (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u)))) +
        (∫ u in Ioi (N : ℝ),
          (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
            Complex.exp (-I * (c * u))) -
        (oscillatoryGammaNegBoundary z c - oscillatoryGammaNegPartial z c N) := by
    rw [hdampedSplit]
    linear_combination -hboundarySplit
  rw [hidentity]
  calc
    _ ≤ ‖(∫ u in (0 : ℝ)..(N : ℝ),
            (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
              Complex.exp (-I * (c * u))) -
          (∫ u in (0 : ℝ)..(N : ℝ),
            (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u)))‖ +
        ‖∫ u in Ioi (N : ℝ),
          (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
            Complex.exp (-I * (c * u))‖ +
        ‖oscillatoryGammaNegBoundary z c - oscillatoryGammaNegPartial z c N‖ := by
      exact (norm_sub_le _ _).trans
        (add_le_add (norm_add_le _ _) (le_refl _))
    _ < eps / 3 + eps / 3 + eps / 3 := by
      gcongr
      · exact hdampedTail.trans_lt hNsmall
      · exact hboundaryTail.trans_lt hNsmall
    _ = eps := by ring

end HardyTheorem.OscillatoryGammaAbelLimit
