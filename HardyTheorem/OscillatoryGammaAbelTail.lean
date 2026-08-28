import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import HardyTheorem.OscillatoryGammaCompactLimit

open Real Complex Set MeasureTheory Filter Topology

namespace HardyTheorem.OscillatoryGammaAbelTail

/-!
# Negative-phase Gamma boundary and its damped improper tail

The positive Gamma-ray rotation naturally approaches `exp (-i c u)`.  This
file gives that phase its own canonical conditional value and passes the
damping-uniform finite-interval estimate to a genuine `Ioi` integral.
-/

noncomputable def oscillatoryGammaNegPartial (z : ℂ) (c : ℝ) (N : ℕ) : ℂ :=
  ∫ u in (1 : ℝ)..(N : ℝ),
    (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u))

private theorem intervalIntegrable_cpow_mul_cexp_neg_linear
    (z : ℂ) (c : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun u : ℝ => (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u)))
      volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro u hu
  have hu0 : u ≠ 0 := ne_of_gt (ha.trans_le hu.1)
  have hpow : ContinuousAt (fun v : ℝ => (v : ℂ) ^ (z - 1)) u :=
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hu0)
  have hphase : ContinuousAt (fun v : ℝ => Complex.exp (-I * (c * v))) u := by
    fun_prop
  exact (hpow.mul hphase).continuousWithinAt

private theorem exists_tendsto_oscillatoryGammaNegPartial_atTop
    {z : ℂ} {c : ℝ} (hz1 : z.re < 1) (hc : 0 < c) :
    ∃ L : ℂ, Tendsto (oscillatoryGammaNegPartial z c) atTop (nhds L) := by
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
  have hcauchy : CauchySeq (oscillatoryGammaNegPartial z c) := by
    apply Metric.cauchySeq_iff'.2
    intro eps heps
    have hsmall : ∀ᶠ N : ℕ in atTop,
        8 * (N : ℝ) ^ (z.re - 1) / c < eps :=
      (tendsto_order.1 hpowNat).2 eps heps
    have hlarge : ∀ᶠ N : ℕ in atTop,
        2 * |z.im| / c ≤ (N : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * |z.im| / c)
    have hgood : ∀ᶠ N : ℕ in atTop,
        1 ≤ N ∧ 2 * |z.im| / c ≤ (N : ℝ) ∧
          8 * (N : ℝ) ^ (z.re - 1) / c < eps := by
      filter_upwards [eventually_ge_atTop 1, hlarge, hsmall] with N hN hNl hNs
      exact ⟨hN, hNl, hNs⟩
    obtain ⟨N, hN, hNlarge, hNsmall⟩ := hgood.exists
    refine ⟨N, ?_⟩
    intro n hn
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have himN : 2 * |z.im| ≤ c * (N : ℝ) := by
      rw [div_le_iff₀ hc] at hNlarge
      nlinarith
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hbase := intervalIntegrable_cpow_mul_cexp_neg_linear z c
      (a := 1) (b := (N : ℝ)) (by norm_num) h1N
    have htail := intervalIntegrable_cpow_mul_cexp_neg_linear z c
      (a := (N : ℝ)) (b := (n : ℝ)) hNpos hNn
    have hadd := intervalIntegral.integral_add_adjacent_intervals hbase htail
    have hdiff :
        oscillatoryGammaNegPartial z c n - oscillatoryGammaNegPartial z c N =
          ∫ u in (N : ℝ)..(n : ℝ),
            (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u)) := by
      dsimp only [oscillatoryGammaNegPartial]
      rw [← hadd]
      ring
    rw [dist_eq_norm, hdiff]
    have hbound :=
      HardyTheorem.OscillatoryDampedGammaTail.norm_intervalIntegral_cpow_mul_exp_neg_mul_cexp_neg_linear_le
        hNn hNpos hz1 (by norm_num : (0 : ℝ) ≤ 0) hc himN
    have hbound' :
        ‖∫ u in (N : ℝ)..(n : ℝ),
          (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u))‖ ≤
            8 * (N : ℝ) ^ (z.re - 1) / c := by
      simpa using hbound
    exact hbound'.trans_lt hNsmall
  exact cauchySeq_tendsto_of_complete hcauchy

noncomputable def oscillatoryGammaNegBoundary (z : ℂ) (c : ℝ) : ℂ :=
  limUnder atTop (oscillatoryGammaNegPartial z c)

theorem tendsto_oscillatoryGammaNegPartial_atTop
    {z : ℂ} {c : ℝ} (hz1 : z.re < 1) (hc : 0 < c) :
    Tendsto (oscillatoryGammaNegPartial z c) atTop
      (nhds (oscillatoryGammaNegBoundary z c)) := by
  apply tendsto_nhds_limUnder
  exact exists_tendsto_oscillatoryGammaNegPartial_atTop hz1 hc

theorem norm_oscillatoryGammaNegBoundary_sub_partial_le
    {z : ℂ} {c : ℝ} (hz1 : z.re < 1) (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (him : 2 * |z.im| ≤ c * (N : ℝ)) :
    ‖oscillatoryGammaNegBoundary z c - oscillatoryGammaNegPartial z c N‖ ≤
      8 * (N : ℝ) ^ (z.re - 1) / c := by
  have hlim := (tendsto_oscillatoryGammaNegPartial_atTop hz1 hc).sub_const
    (oscillatoryGammaNegPartial z c N)
  apply le_of_tendsto hlim.norm
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hbase := intervalIntegrable_cpow_mul_cexp_neg_linear z c
    (a := 1) (b := (N : ℝ)) (by norm_num) h1N
  have htail := intervalIntegrable_cpow_mul_cexp_neg_linear z c
    (a := (N : ℝ)) (b := (n : ℝ)) hNpos hNn
  have hadd := intervalIntegral.integral_add_adjacent_intervals hbase htail
  have hdiff :
      oscillatoryGammaNegPartial z c n - oscillatoryGammaNegPartial z c N =
        ∫ u in (N : ℝ)..(n : ℝ),
          (u : ℂ) ^ (z - 1) * Complex.exp (-I * (c * u)) := by
    dsimp only [oscillatoryGammaNegPartial]
    rw [← hadd]
    ring
  rw [hdiff]
  have hbound :=
    HardyTheorem.OscillatoryDampedGammaTail.norm_intervalIntegral_cpow_mul_exp_neg_mul_cexp_neg_linear_le
      hNn hNpos hz1 (by norm_num : (0 : ℝ) ≤ 0) hc him
  simpa using hbound

/-- Positive damping makes the negative-phase Gamma tail absolutely
integrable. -/
theorem integrableOn_dampedGammaNeg_Ioi_zero
    {z : ℂ} {r c : ℝ} (hz0 : 0 < z.re) (hr : 0 < r) :
    IntegrableOn
      (fun u : ℝ => (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
        Complex.exp (-I * (c * u))) (Ioi 0) := by
  let g : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
      Complex.exp (-I * (c * u))
  let G : ℝ → ℝ := fun u => u ^ (z.re - 1) * Real.exp (-r * u)
  have hG : IntegrableOn G (Ioi 0) := by
    simpa [G] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := z.re - 1) (p := 1) (b := r) (by linarith) (by norm_num) hr)
  have hgcont : ContinuousOn g (Ioi 0) := by
    intro u hu
    have hupos : 0 < u := hu
    have hpow : ContinuousAt (fun v : ℝ => (v : ℂ) ^ (z - 1)) u :=
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hupos.ne')
    have hdamp : ContinuousAt (fun v : ℝ => Complex.exp (-(r * v))) u := by
      fun_prop
    have hphase : ContinuousAt (fun v : ℝ => Complex.exp (-I * (c * v))) u := by
      fun_prop
    exact ((hpow.mul hdamp).mul hphase).continuousWithinAt
  apply hG.mono' (hgcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hupos : 0 < u := hu
  dsimp only [g, G]
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hupos]
  have hdampNorm : ‖Complex.exp (-(r * u))‖ = Real.exp (-(r * u)) := by
    rw [Complex.norm_exp]
    simp
  have hphaseNorm : ‖Complex.exp (-I * (c * u))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hdampNorm, hphaseNorm, mul_one]
  simp

/-- Positive damping makes the negative-phase Gamma tail absolutely
integrable. -/
theorem integrableOn_dampedGammaNeg_Ioi
    {z : ℂ} {r c A : ℝ} (hz0 : 0 < z.re) (hr : 0 < r) (hA : 0 < A) :
    IntegrableOn
      (fun u : ℝ => (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
        Complex.exp (-I * (c * u))) (Ioi A) := by
  let g : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
      Complex.exp (-I * (c * u))
  let G : ℝ → ℝ := fun u => u ^ (z.re - 1) * Real.exp (-r * u)
  have hG0 : IntegrableOn G (Ioi 0) := by
    simpa [G] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := z.re - 1) (p := 1) (b := r) (by linarith) (by norm_num) hr)
  have hGA : IntegrableOn G (Ioi A) :=
    hG0.mono_set (Ioi_subset_Ioi hA.le)
  have hgcont : ContinuousOn g (Ioi A) := by
    intro u hu
    have hupos : 0 < u := hA.trans hu
    have hpow : ContinuousAt (fun v : ℝ => (v : ℂ) ^ (z - 1)) u :=
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hupos.ne')
    have hdamp : ContinuousAt (fun v : ℝ => Complex.exp (-(r * v))) u := by
      fun_prop
    have hphase : ContinuousAt (fun v : ℝ => Complex.exp (-I * (c * v))) u := by
      fun_prop
    exact ((hpow.mul hdamp).mul hphase).continuousWithinAt
  apply hGA.mono' (hgcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hupos : 0 < u := hA.trans hu
  dsimp only [g, G]
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hupos]
  have hdampNorm : ‖Complex.exp (-(r * u))‖ = Real.exp (-(r * u)) := by
    rw [Complex.norm_exp]
    simp
  have hphaseNorm : ‖Complex.exp (-I * (c * u))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hdampNorm, hphaseNorm, mul_one]
  simp

/-- The finite damping-uniform estimate passes to the improper `Ioi` tail. -/
theorem norm_integral_dampedGammaNeg_Ioi_le
    {z : ℂ} {r c A : ℝ} (hz0 : 0 < z.re) (hz1 : z.re < 1)
    (hr : 0 < r) (hc : 0 < c) (hA : 0 < A)
    (him : 2 * |z.im| ≤ c * A) :
    ‖∫ u in Ioi A,
        (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
          Complex.exp (-I * (c * u))‖ ≤
      8 * A ^ (z.re - 1) / c := by
  let g : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
      Complex.exp (-I * (c * u))
  have hg := integrableOn_dampedGammaNeg_Ioi
    (z := z) (r := r) (c := c) (A := A) hz0 hr hA
  have hlim : Tendsto (fun B : ℝ => ∫ u in A..B, g u) atTop
      (nhds (∫ u in Ioi A, g u)) :=
    intervalIntegral_tendsto_integral_Ioi A hg tendsto_id
  apply le_of_tendsto hlim.norm
  filter_upwards [eventually_ge_atTop A] with B hAB
  exact
    HardyTheorem.OscillatoryDampedGammaTail.norm_intervalIntegral_cpow_mul_exp_neg_mul_cexp_neg_linear_le
      hAB hA hz1 hr.le hc him

end HardyTheorem.OscillatoryGammaAbelTail
