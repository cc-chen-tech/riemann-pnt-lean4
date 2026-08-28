import HardyTheorem.OscillatoryIntegral

open Real Complex Set MeasureTheory Filter Topology

namespace HardyTheorem.OscillatoryGammaTail

/-!
# The non-stationary tail of the oscillatory Gamma integral

For `0 < Re z < 1`, the boundary Gamma integrand
`u ^ (z - 1) * exp (i c u)` has decreasing radial weight.  Once
`c A >= 2 |Im z|`, its logarithmic phase has derivative bounded away from
zero on `[A, B]`.  This is the uniform right-tail estimate needed to pass
from a damped Gamma ray to the boundary ray in Titchmarsh's approximate
functional equation.
-/

private noncomputable def gammaBoundaryPhase (z : ℂ) (c u : ℝ) : ℝ :=
  c * u + z.im * Real.log u

private lemma cpow_sub_one_mul_cexp_linear_eq
    (z : ℂ) (c : ℝ) {u : ℝ} (hu : 0 < u) :
    (u : ℂ) ^ (z - 1) * Complex.exp (I * (c * u)) =
      u ^ (-(1 - z.re)) •
        Complex.exp (I * gammaBoundaryPhase z c u) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne')]
  rw [Complex.real_smul, Real.rpow_def_of_pos hu]
  calc
    Complex.exp (Complex.log (u : ℂ) * (z - 1)) *
          Complex.exp (I * (c * u)) =
        Complex.exp
          (Complex.log (u : ℂ) * (z - 1) + I * (c * u)) := by
            rw [Complex.exp_add]
    _ = Complex.exp
          (((Real.log u * -(1 - z.re) : ℝ) : ℂ) +
            I * gammaBoundaryPhase z c u) := by
          congr 1
          rw [← Complex.ofReal_log hu.le]
          simp only [gammaBoundaryPhase]
          apply Complex.ext
          · simp
          · simp
            ring
    _ = (Real.exp (Real.log u * -(1 - z.re)) : ℂ) *
          Complex.exp (I * gammaBoundaryPhase z c u) := by
            rw [Complex.exp_add, Complex.ofReal_exp]

private lemma hasDerivAt_gammaBoundaryPhase
    (z : ℂ) (c : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (gammaBoundaryPhase z c)
      (c + z.im / u) u := by
  unfold gammaBoundaryPhase
  simpa [div_eq_mul_inv, Pi.add_def, Pi.mul_def] using
    ((hasDerivAt_id u).const_mul c).add
      ((Real.hasDerivAt_log hu).const_mul z.im)

/-- Uniform right-tail estimate for the oscillatory Gamma integrand.  The
constant is deliberately non-sharp; crucially it is independent of `B`. -/
theorem norm_intervalIntegral_cpow_mul_cexp_linear_le
    {z : ℂ} {c A B : ℝ}
    (hAB : A ≤ B) (hA : 0 < A) (hz1 : z.re < 1)
    (hc : 0 < c) (him : 2 * |z.im| ≤ c * A) :
    ‖∫ u in A..B,
        (u : ℂ) ^ (z - 1) * Complex.exp (I * (c * u))‖ ≤
      8 * A ^ (z.re - 1) / c := by
  let p : ℝ := 1 - z.re
  let m : ℝ := c / 2
  let F : ℝ → ℝ := gammaBoundaryPhase z c
  have hp : 0 < p := by dsimp [p]; linarith
  have hm : 0 < m := by dsimp [m]; positivity
  have hF : ∀ u ∈ Icc A B, ContDiffAt ℝ 2 F u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (hA.trans_le hu.1)
    dsimp only [F, gammaBoundaryPhase]
    exact (contDiffAt_const.mul contDiffAt_id).add
      (contDiffAt_const.mul (Real.contDiffAt_log.2 hu0))
  have hderiv : ∀ u ∈ Icc A B, deriv F u = c + z.im / u := by
    intro u hu
    exact (hasDerivAt_gammaBoundaryPhase z c
      (ne_of_gt (hA.trans_le hu.1))).deriv
  have hmono :
      MonotoneOn (deriv F) (Icc A B) ∨
        AntitoneOn (deriv F) (Icc A B) := by
    rcases le_total 0 z.im with him0 | him0
    · right
      intro u hu v hv huv
      rw [hderiv u hu, hderiv v hv]
      have hupos : 0 < u := hA.trans_le hu.1
      have hvpos : 0 < v := hupos.trans_le huv
      have hdiv : z.im / v ≤ z.im / u := by
        exact (div_le_div_iff₀ hvpos hupos).2
          (mul_le_mul_of_nonneg_left huv him0)
      linarith
    · left
      intro u hu v hv huv
      rw [hderiv u hu, hderiv v hv]
      have hupos : 0 < u := hA.trans_le hu.1
      have hvpos : 0 < v := hupos.trans_le huv
      have hdiv : z.im / u ≤ z.im / v := by
        exact (div_le_div_iff₀ hupos hvpos).2
          (mul_le_mul_of_nonpos_left huv him0)
      linarith
  have haway : ∀ u ∈ Icc A B, m ≤ |deriv F u| := by
    intro u hu
    rw [hderiv u hu]
    have hupos : 0 < u := hA.trans_le hu.1
    have hAu : A ≤ u := hu.1
    have hcA : 0 < c * A := mul_pos hc hA
    have himA : |z.im| ≤ c * A / 2 := by linarith
    have hratio : |z.im / u| ≤ c / 2 := by
      rw [abs_div, abs_of_pos hupos]
      rw [div_le_iff₀ hupos]
      have hcu : c * A ≤ c * u := mul_le_mul_of_nonneg_left hAu hc.le
      nlinarith
    have htriangle : c ≤ |c + z.im / u| + |z.im / u| := by
      calc
        c = |c| := (abs_of_pos hc).symm
        _ = |(c + z.im / u) + (-(z.im / u))| := by ring_nf
        _ ≤ |c + z.im / u| + |-(z.im / u)| := abs_add_le _ _
        _ = |c + z.im / u| + |z.im / u| := by rw [abs_neg]
    dsimp only [m]
    linarith
  have hraw :=
    OscillatoryIntegral.norm_integral_rpow_smul_cexp_phase_le_of_monotone_deriv_local
      hAB hA hm hp hF hmono haway
  have heq :
      (∫ u in A..B,
          (u : ℂ) ^ (z - 1) * Complex.exp (I * (c * u))) =
        ∫ u in A..B,
          u ^ (-p) • Complex.exp (I * F u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have huIcc : u ∈ Icc A B := by
      simpa [uIcc_of_le hAB] using hu
    simpa [p, F] using
      cpow_sub_one_mul_cexp_linear_eq z c (hA.trans_le huIcc.1)
  rw [heq]
  exact hraw.trans_eq (by
    dsimp [m, p]
    rw [show -(1 - z.re) = z.re - 1 by ring]
    field_simp [hc.ne']
    norm_num)

/-- Natural truncations of the boundary Gamma integral, based at `1`.  The
segment `(0,1]` is kept separate because its convergence uses `0 < Re z`,
whereas the oscillatory right tail only uses `Re z < 1`. -/
noncomputable def oscillatoryGammaPartial (z : ℂ) (c : ℝ) (N : ℕ) : ℂ :=
  ∫ u in (1 : ℝ)..(N : ℝ),
    (u : ℂ) ^ (z - 1) * Complex.exp (I * (c * u))

private theorem intervalIntegrable_cpow_mul_cexp_linear
    (z : ℂ) (c : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun u : ℝ =>
        (u : ℂ) ^ (z - 1) * Complex.exp (I * (c * u))) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro u hu
  have hu0 : u ≠ 0 := ne_of_gt (ha.trans_le hu.1)
  have hpow : ContinuousAt (fun v : ℝ => (v : ℂ) ^ (z - 1)) u :=
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hu0)
  have hexp : ContinuousAt
      (fun v : ℝ => Complex.exp (I * (c * v))) u := by
    fun_prop
  exact (hpow.mul hexp).continuousWithinAt

/-- The natural truncations of the boundary Gamma integral have a limit.
This is conditional convergence: the proof is the Cauchy criterion plus the
uniform right-tail estimate above, not absolute integrability. -/
theorem exists_tendsto_oscillatoryGammaPartial_atTop
    {z : ℂ} {c : ℝ} (hz1 : z.re < 1) (hc : 0 < c) :
    ∃ L : ℂ,
      Tendsto (oscillatoryGammaPartial z c) atTop (nhds L) := by
  have hp : 0 < 1 - z.re := by linarith
  have hpowReal :
      Tendsto (fun A : ℝ => 8 * A ^ (z.re - 1) / c) atTop (nhds 0) := by
    have hbase := tendsto_rpow_neg_atTop hp
    have hmul :
        Tendsto (fun A : ℝ => (8 / c) * A ^ (-(1 - z.re))) atTop
          (nhds ((8 / c) * 0)) := tendsto_const_nhds.mul hbase
    convert hmul using 1
    · funext A
      rw [show z.re - 1 = -(1 - z.re) by ring]
      ring
    · simp
  have hpowNat :
      Tendsto (fun N : ℕ => 8 * (N : ℝ) ^ (z.re - 1) / c) atTop
        (nhds 0) :=
    hpowReal.comp tendsto_natCast_atTop_atTop
  have hcauchy : CauchySeq (oscillatoryGammaPartial z c) := by
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
      filter_upwards [eventually_ge_atTop 1, hlarge, hsmall] with N hN hNlarge hNsmall
      exact ⟨hN, hNlarge, hNsmall⟩
    obtain ⟨N, hN, hNlarge, hNsmall⟩ := hgood.exists
    refine ⟨N, ?_⟩
    intro n hn
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hN)
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have himN : 2 * |z.im| ≤ c * (N : ℝ) := by
      rw [div_le_iff₀ hc] at hNlarge
      nlinarith
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hbase := intervalIntegrable_cpow_mul_cexp_linear z c
      (a := 1) (b := (N : ℝ)) (by norm_num) h1N
    have htail := intervalIntegrable_cpow_mul_cexp_linear z c
      (a := (N : ℝ)) (b := (n : ℝ)) hNpos hNn
    have hadd := intervalIntegral.integral_add_adjacent_intervals hbase htail
    have hdiff :
        oscillatoryGammaPartial z c n - oscillatoryGammaPartial z c N =
          ∫ u in (N : ℝ)..(n : ℝ),
            (u : ℂ) ^ (z - 1) * Complex.exp (I * (c * u)) := by
      dsimp only [oscillatoryGammaPartial]
      rw [← hadd]
      ring
    rw [dist_eq_norm, hdiff]
    exact (norm_intervalIntegral_cpow_mul_cexp_linear_le
      hNn hNpos hz1 hc himN).trans_lt hNsmall
  exact cauchySeq_tendsto_of_complete hcauchy

end HardyTheorem.OscillatoryGammaTail
