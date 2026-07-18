import HardyTheorem.FirstZetaApproximation
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import PrimeNumberTheorem.DigammaBounds

open Complex Filter MeasureTheory Set Topology

namespace HardyTheorem

private noncomputable def localBernoulliOne (n : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun 1 (x - n)

private noncomputable def localBernoulliTwoHalf (n : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun 2 (x - n) / 2

private lemma periodizedBernoulli_two_ae_eq_local (n : ℕ) :
    (fun x : ℝ => periodizedBernoulli 2 (x : AddCircle (1 : ℝ))) =ᵐ[
      volume.restrict (Set.Ioc (n : ℝ) (n + 1 : ℕ))]
      (fun x : ℝ => bernoulliFun 2 (x - n)) := by
  have hend : ∀ᵐ x : ℝ, x ≠ (n + 1 : ℕ) := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hend] with x hx hne
  have hx' : (n : ℝ) < x ∧ x ≤ (n : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hx
  have hy : x - (n : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · linarith [hx'.1]
    · have hxlt : x < (n + 1 : ℕ) := lt_of_le_of_ne hx.2 hne
      push_cast at hxlt
      linarith
  have hcoe : (x : AddCircle (1 : ℝ)) =
      ((x - (n : ℝ)) : AddCircle (1 : ℝ)) := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change x - (x - (n : ℝ)) ∈ AddSubgroup.zmultiples (1 : ℝ)
    rw [sub_sub_cancel]
    exact ⟨n, by simp⟩
  rw [hcoe, periodizedBernoulli]
  exact AddCircle.liftIco_coe_apply (show x - (n : ℝ) ∈ Set.Ico 0 (0 + 1) by
    simpa only [zero_add] using hy)

private lemma hasDerivAt_inv_const_add_ofReal {z : ℂ} {x : ℝ}
    (hzx : z + x ≠ 0) :
    HasDerivAt (fun y : ℝ => (z + (y : ℂ))⁻¹) (-((z + x)⁻¹) ^ 2) x := by
  have h := ((hasDerivAt_id (x : ℂ)).const_add z).inv hzx
  simpa [div_eq_mul_inv] using h.comp_ofReal

private lemma hasDerivAt_neg_inv_sq_const_add_ofReal {z : ℂ} {x : ℝ}
    (hzx : z + x ≠ 0) :
    HasDerivAt (fun y : ℝ => -((z + (y : ℂ))⁻¹) ^ 2)
      (2 * ((z + x)⁻¹) ^ 3) x := by
  have hg : HasDerivAt (fun w : ℂ => z + w) 1 (x : ℂ) :=
    (hasDerivAt_id (x : ℂ)).const_add z
  have hi := hg.inv hzx
  have hp := hi.pow 2
  have hn := hp.neg
  convert hn.comp_ofReal using 1
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.inv_apply]
  field_simp [hzx]

/-- The second-order Euler--Maclaurin identity on one unit interval for
`x ↦ (z+x)⁻¹`. -/
private theorem inv_const_add_unit_eulerMaclaurin
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    (z + (n + 1 : ℕ))⁻¹ =
      (∫ x in (n : ℝ)..(n + 1 : ℕ), (z + (x : ℂ))⁻¹) +
        ((z + (n + 1 : ℕ))⁻¹ - (z + n)⁻¹) / 2 +
        (((z + n)⁻¹) ^ 2 - ((z + (n + 1 : ℕ))⁻¹) ^ 2) / 12 -
        ∫ x in (n : ℝ)..(n + 1 : ℕ),
          ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) /
            (z + x) ^ 3 := by
  let F : ℝ → ℂ := fun x => (z + (x : ℂ))⁻¹
  let F' : ℝ → ℂ := fun x => -((z + (x : ℂ))⁻¹) ^ 2
  let F'' : ℝ → ℂ := fun x => 2 * ((z + (x : ℂ))⁻¹) ^ 3
  let B1 : ℝ → ℝ := localBernoulliOne n
  let B2h : ℝ → ℝ := localBernoulliTwoHalf n
  have hnn : (n : ℝ) ≤ (n + 1 : ℕ) := by norm_num
  have hne : ∀ {x : ℝ}, 0 ≤ x → z + (x : ℂ) ≠ 0 := by
    intro x hx hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hF : ∀ x ∈ Set.Icc (n : ℝ) (n + 1 : ℕ), HasDerivAt F (F' x) x := by
    intro x hx
    have hx0 : 0 ≤ x := (Nat.cast_nonneg n).trans hx.1
    exact hasDerivAt_inv_const_add_ofReal (hne hx0)
  have hF' : ∀ x ∈ Set.Icc (n : ℝ) (n + 1 : ℕ), HasDerivAt F' (F'' x) x := by
    intro x hx
    have hx0 : 0 ≤ x := (Nat.cast_nonneg n).trans hx.1
    exact hasDerivAt_neg_inv_sq_const_add_ofReal (hne hx0)
  have hB1 : ∀ x ∈ Set.Icc (n : ℝ) (n + 1 : ℕ), HasDerivAt B1 1 x := by
    intro x _hx
    have hsub : HasDerivAt (fun y : ℝ => y - (n : ℝ)) 1 x :=
      (hasDerivAt_id x).sub_const (n : ℝ)
    dsimp only [B1, localBernoulliOne]
    convert (hasDerivAt_bernoulliFun 1 (x - n)).comp x hsub using 1 <;>
      norm_num
  have hB2 : ∀ x ∈ Set.Icc (n : ℝ) (n + 1 : ℕ), HasDerivAt B2h (B1 x) x := by
    intro x _hx
    have hsub : HasDerivAt (fun y : ℝ => y - (n : ℝ)) 1 x :=
      (hasDerivAt_id x).sub_const (n : ℝ)
    dsimp only [B2h, B1, localBernoulliTwoHalf, localBernoulliOne]
    convert ((hasDerivAt_bernoulliFun 2 (x - n)).comp x hsub).div_const 2 using 1
    all_goals norm_num
  have hB1int : IntervalIntegrable B1 volume (n : ℝ) (n + 1 : ℕ) := by
    apply Continuous.intervalIntegrable
    dsimp only [B1, localBernoulliOne]
    exact (continuous_bernoulliFun 1).comp (continuous_id.sub continuous_const)
  have hB2int : IntervalIntegrable B2h volume (n : ℝ) (n + 1 : ℕ) := by
    apply Continuous.intervalIntegrable
    dsimp only [B2h, localBernoulliTwoHalf]
    exact ((continuous_bernoulliFun 2).comp
      (continuous_id.sub continuous_const)).div_const 2
  have hF'int : IntervalIntegrable F' volume (n : ℝ) (n + 1 : ℕ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hnn
    intro x hx
    exact (hF' x hx).continuousAt.continuousWithinAt
  have hF''int : IntervalIntegrable F'' volume (n : ℝ) (n + 1 : ℕ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hnn
    intro x hx
    have hx0 : 0 ≤ x := (Nat.cast_nonneg n).trans hx.1
    have hg : ContinuousAt (fun y : ℝ => z + (y : ℂ)) x :=
      continuousAt_const.add Complex.continuous_ofReal.continuousAt
    exact (continuousAt_const.mul
      ((hg.inv₀ (hne hx0)).pow 3)).continuousWithinAt
  have hp1 := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (a := (n : ℝ)) (b := (n + 1 : ℕ))
    (u := B1) (u' := fun _ => (1 : ℝ)) (v := F) (v' := F')
    (fun x hx => hB1 x (by simpa [Set.uIcc_of_le hnn] using hx))
    (fun x hx => hF x (by simpa [Set.uIcc_of_le hnn] using hx))
    ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable _ _) hF'int
  have hp2 := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (a := (n : ℝ)) (b := (n + 1 : ℕ))
    (u := B2h) (u' := B1) (v := F') (v' := F'')
    (fun x hx => hB2 x (by simpa [Set.uIcc_of_le hnn] using hx))
    (fun x hx => hF' x (by simpa [Set.uIcc_of_le hnn] using hx))
    hB1int hF''int
  have hperiodic :
      (∫ x in (n : ℝ)..(n + 1 : ℕ), B2h x • F'' x) =
        ∫ x in (n : ℝ)..(n + 1 : ℕ),
          ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) /
            (z + x) ^ 3 := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [Set.uIoc_of_le hnn]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      periodizedBernoulli_two_ae_eq_local n] with x hxmem hx
    rw [hx]
    dsimp only [B2h, F'', localBernoulliTwoHalf]
    simp only [Complex.real_smul]
    push_cast
    have hx0 : 0 ≤ x := (Nat.cast_nonneg n).trans hxmem.1.le
    field_simp [hne hx0]
  have hB1n : B1 n = -1 / 2 := by norm_num [B1, localBernoulliOne, bernoulliFun_one]
  have hB1s : B1 (n + 1 : ℕ) = 1 / 2 := by
    norm_num [B1, localBernoulliOne, bernoulliFun_one]
  have hB2n : B2h n = 1 / 12 := by
    norm_num [B2h, localBernoulliTwoHalf, bernoulliFun_two]
  have hB2s : B2h (n + 1 : ℕ) = 1 / 12 := by
    norm_num [B2h, localBernoulliTwoHalf, bernoulliFun_two]
  rw [hB1n, hB1s] at hp1
  have hp2' :
      (∫ x in (n : ℝ)..(n + 1 : ℕ),
          ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) /
            (z + x) ^ 3) =
        B2h (n + 1 : ℕ) • F' (n + 1 : ℕ) - B2h n • F' n -
          ∫ x in (n : ℝ)..(n + 1 : ℕ), B1 x • F' x := by
    rw [← hperiodic]
    exact hp2
  rw [hB2n, hB2s] at hp2'
  dsimp only [F, F', F''] at hp1 hp2 ⊢
  dsimp only [F, F', F''] at hp2'
  simp_rw [Complex.real_smul] at hp2'
  push_cast at hp2' ⊢
  have hp1cast :
      (∫ x in (n : ℝ)..(n + 1 : ℕ),
          ((B1 x : ℝ) : ℂ) * -((z + (x : ℂ))⁻¹) ^ 2) =
        (1 / 2 : ℂ) * (z + (n + 1 : ℕ))⁻¹ -
          (-1 / 2 : ℂ) * (z + n)⁻¹ -
            ∫ x in (n : ℝ)..(n + 1 : ℕ), (z + (x : ℂ))⁻¹ := by
    calc
      (∫ x in (n : ℝ)..(n + 1 : ℕ),
          ((B1 x : ℝ) : ℂ) * -((z + (x : ℂ))⁻¹) ^ 2) =
          ∫ x in (n : ℝ)..(n + 1 : ℕ), B1 x • -((z + (x : ℂ))⁻¹) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x _hx
        exact Complex.real_smul.symm
      _ = (1 / 2 : ℝ) • (z + (n + 1 : ℕ))⁻¹ -
          (-1 / 2 : ℝ) • (z + n)⁻¹ -
            ∫ x in (n : ℝ)..(n + 1 : ℕ), (1 : ℝ) • (z + (x : ℂ))⁻¹ := hp1
      _ = (1 / 2 : ℂ) * (z + (n + 1 : ℕ))⁻¹ -
          (-1 / 2 : ℂ) * (z + n)⁻¹ -
            ∫ x in (n : ℝ)..(n + 1 : ℕ), (z + (x : ℂ))⁻¹ := by
        simp only [Complex.real_smul, ofReal_one, one_mul]
        norm_num
  push_cast at hp1cast
  rw [hp2', hp1cast]
  ring

private lemma intervalIntegrable_inv_const_add_of_nonneg
    {z : ℂ} (hz : 0 < z.re) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => (z + (x : ℂ))⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro x hx
  have hx0 : 0 ≤ x := ha.trans hx.1
  exact (hasDerivAt_inv_const_add_ofReal (by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith)).continuousAt.continuousWithinAt

private lemma intervalIntegrable_periodizedBernoulli_div_const_add_cube
    {z : ℂ} (hz : 0 < z.re) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun x : ℝ =>
        ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) /
          (z + x) ^ 3) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro x hx
  have hx0 : 0 ≤ x := ha.trans hx.1
  have hden : z + (x : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div
  · exact Complex.continuous_ofReal.continuousAt.comp
      ((periodizedBernoulli.continuous (by norm_num : 2 ≠ 1)).continuousAt.comp
        continuous_quotient_mk'.continuousAt)
  · exact ((continuousAt_const.add Complex.continuous_ofReal.continuousAt).pow 3)
  · exact pow_ne_zero 3 hden

/-- Finite second-order Euler--Maclaurin formula for the shifted harmonic
sum. -/
private theorem sum_range_inv_const_add_eulerMaclaurin
    {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    (∑ k ∈ Finset.range N, (z + (k + 1 : ℕ))⁻¹) =
      (∫ x in (0 : ℝ)..N, (z + (x : ℂ))⁻¹) +
        ((z + N)⁻¹ - z⁻¹) / 2 +
        ((z⁻¹) ^ 2 - ((z + N)⁻¹) ^ 2) / 12 -
        ∫ x in (0 : ℝ)..N,
          ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) /
            (z + x) ^ 3 := by
  induction N with
  | zero => simp
  | succ N ih =>
      have h0N : (0 : ℝ) ≤ N := by positivity
      have hNN : (N : ℝ) ≤ (N + 1 : ℕ) := by norm_num
      have hFin0 := intervalIntegrable_inv_const_add_of_nonneg hz
        (a := (0 : ℝ)) (b := (N : ℝ)) (by norm_num) h0N
      have hFin1 := intervalIntegrable_inv_const_add_of_nonneg hz
        (a := (N : ℝ)) (b := (N + 1 : ℕ)) h0N hNN
      have hKin0 := intervalIntegrable_periodizedBernoulli_div_const_add_cube hz
        (a := (0 : ℝ)) (b := (N : ℝ)) (by norm_num) h0N
      have hKin1 := intervalIntegrable_periodizedBernoulli_div_const_add_cube hz
        (a := (N : ℝ)) (b := (N + 1 : ℕ)) h0N hNN
      rw [Finset.sum_range_succ]
      rw [ih]
      have hunit := inv_const_add_unit_eulerMaclaurin hz N
      have hFadd := intervalIntegral.integral_add_adjacent_intervals hFin0 hFin1
      have hKadd := intervalIntegral.integral_add_adjacent_intervals hKin0 hKin1
      push_cast at hunit hFadd hKadd ⊢
      linear_combination hunit + hFadd - hKadd

private theorem intervalIntegral_inv_const_add_eq_log_sub
    {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    (∫ x in (0 : ℝ)..N, (z + (x : ℂ))⁻¹) =
      Complex.log (z + N) - Complex.log z := by
  have h0N : (0 : ℝ) ≤ N := by positivity
  have hint := intervalIntegrable_inv_const_add_of_nonneg hz
    (a := (0 : ℝ)) (b := (N : ℝ)) (by norm_num) h0N
  have hder : ∀ x ∈ Set.uIcc (0 : ℝ) (N : ℝ),
      HasDerivAt (fun x : ℝ => Complex.log (z + (x : ℂ)))
        ((z + (x : ℂ))⁻¹) x := by
    intro x hx
    have hx0 : 0 ≤ x := by
      rw [Set.uIcc_of_le h0N] at hx
      exact hx.1
    have hslit : z + (x : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simp
      linarith
    have hg : HasDerivAt (fun w : ℂ => z + w) 1 (x : ℂ) :=
      (hasDerivAt_id (x : ℂ)).const_add z
    simpa [Function.comp_def] using
      ((Complex.hasDerivAt_log hslit).comp (x : ℂ) hg).comp_ofReal
  have hres := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  simpa using hres

private theorem tendsto_log_const_add_natCast_sub_log (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun N : ℕ => Complex.log (z + N) - (Real.log N : ℂ)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℂ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hsmall : Tendsto (fun N : ℕ => 1 + z * (N : ℂ)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  have hlog : Tendsto (fun N : ℕ => Complex.log (1 + z * (N : ℂ)⁻¹))
      atTop (𝓝 0) := by
    simpa using (Complex.hasDerivAt_log Complex.one_mem_slitPlane).continuousAt.tendsto.comp hsmall
  apply hlog.congr'
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hfactor : z + (N : ℂ) =
      (N : ℂ) * (1 + z * (N : ℂ)⁻¹) := by
    field_simp [hNC]
    ring
  have hone : 1 + z * (N : ℂ)⁻¹ ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [Complex.inv_re, Complex.inv_im, Complex.normSq_apply] at hre
    have : 0 < 1 + z.re / (N : ℝ) := by positivity
    exact this.ne' hre
  calc
    Complex.log (1 + z * (N : ℂ)⁻¹) =
        ((Real.log N : ℂ) + Complex.log (1 + z * (N : ℂ)⁻¹)) -
          (Real.log N : ℂ) := by ring
    _ = Complex.log ((N : ℂ) * (1 + z * (N : ℂ)⁻¹)) -
          (Real.log N : ℂ) :=
      congrArg (fun w : ℂ => w - (Real.log N : ℂ))
        (Complex.log_ofReal_mul hNpos hone).symm
    _ = Complex.log (z + N) - (Real.log N : ℂ) := by rw [hfactor]

/-- The elementary phase occurring in the vertical Stirling approximation to
`Gammaℝ (1 / 2 + I * t)`. -/
noncomputable def thetaModel (t : ℝ) : ℝ :=
  t / 2 * Real.log (t / (2 * Real.pi)) - t / 2 - Real.pi / 8

/-- The derivative of the smooth vertical `Gammaℝ` phase, written in terms of
the real part of the digamma function. -/
noncomputable def verticalGammaPhaseVelocity (t : ℝ) : ℝ :=
  (Complex.digamma ((1 / 4 : ℂ) + I * t / 2)).re / 2 - Real.log Real.pi / 2

private lemma analyticAt_Gamma_of_pos_re {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.Gamma z := by
  rw [analyticAt_iff_eventually_differentiableAt]
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hz] with w hw
  apply Complex.differentiableAt_Gamma
  intro m hzero
  have hre := congrArg Complex.re hzero
  simp at hre
  linarith

private lemma continuousAt_digamma_of_pos_re {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt Complex.digamma z := by
  have hGamma := analyticAt_Gamma_of_pos_re hz
  rw [Complex.digamma_def]
  change ContinuousAt (fun w => deriv Complex.Gamma w / Complex.Gamma w) z
  exact (hGamma.deriv.div hGamma (Complex.Gamma_ne_zero_of_re_pos hz)).continuousAt

private theorem continuous_verticalGammaPhaseVelocity :
    Continuous verticalGammaPhaseVelocity := by
  rw [continuous_iff_continuousAt]
  intro t
  let z : ℝ → ℂ := fun x => (1 / 4 : ℂ) + I * x / 2
  have hzre : 0 < (z t).re := by
    dsimp [z]
    norm_num
  have hzcont : ContinuousAt z t := by
    dsimp [z]
    fun_prop
  have hdig := (continuousAt_digamma_of_pos_re hzre).comp hzcont
  change ContinuousAt
    (fun x : ℝ => (Complex.digamma (z x)).re / 2 - Real.log Real.pi / 2) t
  exact ((Complex.continuous_re.continuousAt.comp hdig).div_const 2).sub_const _

private noncomputable def gammaQuarterVertical (t : ℝ) : ℂ :=
  Complex.Gamma ((1 / 4 : ℂ) + I * t / 2)

private noncomputable def gammaQuarterLogDerivative (t : ℝ) : ℂ :=
  I * Complex.digamma ((1 / 4 : ℂ) + I * t / 2) / 2

private noncomputable def gammaQuarterLogIntegral (t : ℝ) : ℂ :=
  ∫ x in (1 : ℝ)..t, gammaQuarterLogDerivative x

private theorem continuous_gammaQuarterLogDerivative :
    Continuous gammaQuarterLogDerivative := by
  rw [continuous_iff_continuousAt]
  intro t
  let z : ℝ → ℂ := fun x => (1 / 4 : ℂ) + I * x / 2
  have hzre : 0 < (z t).re := by
    dsimp [z]
    norm_num
  have hzcont : ContinuousAt z t := by
    dsimp [z]
    fun_prop
  have hdig := (continuousAt_digamma_of_pos_re hzre).comp hzcont
  change ContinuousAt (fun x : ℝ => I * Complex.digamma (z x) / 2) t
  exact (continuousAt_const.mul hdig).div_const 2

private theorem hasDerivAt_gammaQuarterVertical (t : ℝ) :
    HasDerivAt gammaQuarterVertical
      (gammaQuarterLogDerivative t * gammaQuarterVertical t) t := by
  let W : ℂ → ℂ := fun w => (1 / 4 : ℂ) + I * w / 2
  have hW : HasDerivAt W (I / 2) (t : ℂ) := by
    simpa [W] using
      (((hasDerivAt_id (t : ℂ)).const_mul I).div_const 2).const_add (1 / 4 : ℂ)
  have hWre : 0 < (W (t : ℂ)).re := by
    dsimp [W]
    norm_num
  have hGamma : HasDerivAt Complex.Gamma
      (deriv Complex.Gamma (W (t : ℂ))) (W (t : ℂ)) :=
    (Complex.differentiableAt_Gamma _ (fun m hzero => by
      have hre := congrArg Complex.re hzero
      simp [W] at hre
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      norm_num at hre
      linarith)).hasDerivAt
  have hlogDeriv :
      deriv Complex.Gamma (W (t : ℂ)) =
        Complex.digamma (W (t : ℂ)) * Complex.Gamma (W (t : ℂ)) := by
    rw [Complex.digamma_def, logDeriv_apply]
    field_simp [Complex.Gamma_ne_zero_of_re_pos hWre]
  rw [hlogDeriv] at hGamma
  have hcomp := (hGamma.comp (t : ℂ) hW).comp_ofReal
  convert hcomp using 1 <;>
    simp [gammaQuarterLogDerivative, gammaQuarterVertical, W] <;> ring

private theorem hasDerivAt_gammaQuarterLogIntegral (t : ℝ) :
    HasDerivAt gammaQuarterLogIntegral (gammaQuarterLogDerivative t) t := by
  have hcont := continuous_gammaQuarterLogDerivative
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable (1 : ℝ) t)
    hcont.stronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt

private theorem gammaQuarterVertical_eq_base_mul_exp_logIntegral
    {t : ℝ} (ht : 1 ≤ t) :
    gammaQuarterVertical t =
      gammaQuarterVertical 1 * Complex.exp (gammaQuarterLogIntegral t) := by
  let Q : ℝ → ℂ := fun x =>
    gammaQuarterVertical x * Complex.exp (-gammaQuarterLogIntegral x)
  have hQ : ∀ x ∈ Set.uIcc (1 : ℝ) t, HasDerivAt Q 0 x := by
    intro x _hx
    have hG := hasDerivAt_gammaQuarterVertical x
    have hA := hasDerivAt_gammaQuarterLogIntegral x
    dsimp only [Q]
    convert hG.mul hA.neg.cexp using 1
    ring
  have hzeroInt : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume 1 t :=
    (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ))).intervalIntegrable _ _
  have hconst := intervalIntegral.integral_eq_sub_of_hasDerivAt hQ hzeroInt
  simp only [intervalIntegral.integral_zero] at hconst
  have hA1 : gammaQuarterLogIntegral 1 = 0 := by
    simp [gammaQuarterLogIntegral]
  dsimp only [Q] at hconst
  rw [hA1, neg_zero, Complex.exp_zero, mul_one] at hconst
  have hconst' :
      gammaQuarterVertical t * Complex.exp (-gammaQuarterLogIntegral t) =
        gammaQuarterVertical 1 := sub_eq_zero.mp hconst.symm
  calc
    gammaQuarterVertical t =
        (gammaQuarterVertical t * Complex.exp (-gammaQuarterLogIntegral t)) *
          Complex.exp (gammaQuarterLogIntegral t) := by
      rw [mul_assoc, ← Complex.exp_add]
      simp
    _ = gammaQuarterVertical 1 * Complex.exp (gammaQuarterLogIntegral t) := by
      rw [hconst']

private theorem gammaQuarterVertical_unit_eq_base_mul_exp_im_logIntegral
    {t : ℝ} (ht : 1 ≤ t) :
    gammaQuarterVertical t / ‖gammaQuarterVertical t‖ =
      (gammaQuarterVertical 1 / ‖gammaQuarterVertical 1‖) *
        Complex.exp (I * (gammaQuarterLogIntegral t).im) := by
  have hGamma := gammaQuarterVertical_eq_base_mul_exp_logIntegral ht
  have hbase : gammaQuarterVertical 1 ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num [gammaQuarterVertical]
  have hbaseNorm : ‖gammaQuarterVertical 1‖ ≠ 0 := norm_ne_zero_iff.mpr hbase
  have hExp :
      Complex.exp (gammaQuarterLogIntegral t) =
        (Real.exp (gammaQuarterLogIntegral t).re : ℂ) *
          Complex.exp (I * (gammaQuarterLogIntegral t).im) := by
    rw [Complex.exp_eq_exp_re_mul_sin_add_cos]
    rw [← Complex.exp_mul_I]
    rw [← Complex.ofReal_exp]
    congr 1
    ring
  rw [hGamma, norm_mul, Complex.norm_exp, hExp]
  field_simp [hbaseNorm, Real.exp_ne_zero]
  norm_cast
  ring

private theorem gammaQuarterLogIntegral_im (t : ℝ) :
    (gammaQuarterLogIntegral t).im =
      ∫ x in (1 : ℝ)..t,
        (Complex.digamma ((1 / 4 : ℂ) + I * x / 2)).re / 2 := by
  have hint : IntervalIntegrable gammaQuarterLogDerivative volume 1 t :=
    continuous_gammaQuarterLogDerivative.intervalIntegrable _ _
  have hmap := Complex.imCLM.intervalIntegral_comp_comm hint
  have hmap' :
      (∫ x in (1 : ℝ)..t, (gammaQuarterLogDerivative x).im) =
        (∫ x in (1 : ℝ)..t, gammaQuarterLogDerivative x).im := by
    simpa using hmap
  rw [gammaQuarterLogIntegral, ← hmap']
  apply intervalIntegral.integral_congr
  intro x _hx
  simp [gammaQuarterLogDerivative, Complex.mul_im]

private theorem exp_I_arg_gammaQuarterVertical (t : ℝ) :
    Complex.exp (I * Complex.arg (gammaQuarterVertical t)) =
      gammaQuarterVertical t / ‖gammaQuarterVertical t‖ := by
  have hGamma : gammaQuarterVertical t ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num [gammaQuarterVertical]
  have hnorm : (‖gammaQuarterVertical t‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hGamma
  rw [eq_div_iff hnorm]
  rw [show I * (Complex.arg (gammaQuarterVertical t) : ℂ) =
      (Complex.arg (gammaQuarterVertical t) : ℂ) * I by ring]
  rw [mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I (gammaQuarterVertical t)

private theorem exp_I_arg_gammaQuarterVertical_eq_base_add_integral
    {t : ℝ} (ht : 1 ≤ t) :
    Complex.exp (I * Complex.arg (gammaQuarterVertical t)) =
      Complex.exp
        (I * (Complex.arg (gammaQuarterVertical 1) +
          (gammaQuarterLogIntegral t).im)) := by
  rw [exp_I_arg_gammaQuarterVertical,
    gammaQuarterVertical_unit_eq_base_mul_exp_im_logIntegral ht,
    ← exp_I_arg_gammaQuarterVertical]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem deriv_thetaModel {t : ℝ} (ht : 0 < t) :
    deriv thetaModel t = (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) := by
  have hfun : thetaModel = HardyTheorem.OscillatoryIntegral.hardyPhase 1 := by
    funext x
    simp [thetaModel, HardyTheorem.OscillatoryIntegral.hardyPhase]
    ring
  rw [hfun]
  simpa using
    (HardyTheorem.OscillatoryIntegral.deriv_hardyPhase
      (n := 1) (by norm_num) ht)

/-- The periodic Bernoulli remainder kernel in the first neglected term of
the logarithmic Stirling expansion at `1 / 4 + I * t / 2`. -/
noncomputable def verticalStirlingBernoulliKernel (t u : ℝ) : ℂ :=
  ((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ) /
    (((1 / 4 : ℂ) + I * t / 2 + u) ^ 2)

/-- The periodic Bernoulli remainder kernel in the differentiated vertical
Stirling formula. -/
noncomputable def verticalDigammaBernoulliKernel (t u : ℝ) : ℂ :=
  ((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ) /
    (((1 / 4 : ℂ) + I * t / 2 + u) ^ 3)

private lemma exists_periodizedBernoulli_two_norm_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℝ,
      ‖((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ ≤ A := by
  let f : AddCircle (1 : ℝ) → ℝ := fun x =>
    ‖((periodizedBernoulli 2 x : ℝ) : ℂ)‖
  have hf : Continuous f := by
    dsimp [f]
    exact continuous_norm.comp
      (Complex.continuous_ofReal.comp
        (periodizedBernoulli.continuous (by norm_num : 2 ≠ 1)))
  obtain ⟨M, hM⟩ := bddAbove_def.mp
    (isCompact_univ.bddAbove_image hf.continuousOn)
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro u
  exact (hM _ ⟨(u : AddCircle (1 : ℝ)), Set.mem_univ _, rfl⟩).trans
    (le_max_left _ _)

private lemma norm_verticalDigammaBernoulliKernel_le
    {A t u : ℝ} (hA : 0 ≤ A) (ht : 0 < t) (htu : t ≤ u)
    (hbern :
      ‖((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ ≤ A) :
    ‖verticalDigammaBernoulliKernel t u‖ ≤ A * u ^ (-3 : ℝ) := by
  have hu : 0 < u := ht.trans_le htu
  let z : ℂ := (1 / 4 : ℂ) + I * t / 2 + u
  have hre : u ≤ z.re := by
    dsimp [z]
    norm_num
  have huz : u ≤ ‖z‖ :=
    hre.trans (le_abs_self z.re |>.trans (Complex.abs_re_le_norm z))
  have hzpos : 0 < ‖z‖ := hu.trans_le huz
  rw [verticalDigammaBernoulliKernel, norm_div, norm_pow]
  change
    ‖((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ / ‖z‖ ^ 3 ≤
      A * u ^ (-3 : ℝ)
  rw [Real.rpow_neg hu.le]
  rw [show u ^ (3 : ℝ) = u ^ (3 : ℕ) by norm_num [Real.rpow_natCast]]
  have hu3 : 0 < u ^ 3 := pow_pos hu _
  have hden3 : u ^ 3 ≤ ‖z‖ ^ 3 := pow_le_pow_left₀ hu.le huz 3
  rw [div_eq_mul_inv]
  exact mul_le_mul hbern (inv_anti₀ hu3 hden3)
    (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) 3)) hA

private lemma norm_verticalDigammaBernoulliKernel_le_low
    {A t u : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    (hbern :
      ‖((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ ≤ A) :
    ‖verticalDigammaBernoulliKernel t u‖ ≤ 8 * A / t ^ 3 := by
  let z : ℂ := (1 / 4 : ℂ) + I * t / 2 + u
  have him_eq : z.im = t / 2 := by
    dsimp [z]
    simp
  have him : t / 2 ≤ ‖z‖ := by
    rw [← him_eq]
    exact (le_abs_self z.im).trans (Complex.abs_im_le_norm z)
  have him0 : 0 < t / 2 := half_pos ht
  have hpow : (t / 2) ^ 3 ≤ ‖z‖ ^ 3 :=
    pow_le_pow_left₀ him0.le him 3
  rw [verticalDigammaBernoulliKernel, norm_div, norm_pow]
  change
    ‖((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ / ‖z‖ ^ 3 ≤
      8 * A / t ^ 3
  calc
    _ ≤ A / ‖z‖ ^ 3 :=
      div_le_div_of_nonneg_right hbern (pow_nonneg (norm_nonneg _) 3)
    _ ≤ A / (t / 2) ^ 3 :=
      div_le_div_of_nonneg_left hA (pow_pos him0 3) hpow
    _ = 8 * A / t ^ 3 := by field_simp [ht.ne']; ring

/-- The differentiated periodic-Bernoulli remainder on the vertical line is
`O(1/t²)`. -/
theorem exists_norm_integral_Ioi_verticalDigammaBernoulliKernel_le_inv_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖∫ u in Set.Ioi (0 : ℝ), verticalDigammaBernoulliKernel t u‖ ≤
        C / t ^ 2 := by
  obtain ⟨A, hA, hbern⟩ := exists_periodizedBernoulli_two_norm_bound
  refine ⟨9 * A, mul_nonneg (by norm_num) hA, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let F : ℝ → ℂ := verticalDigammaBernoulliKernel t
  let g : ℝ → ℝ := fun u => A * u ^ (-3 : ℝ)
  have hFcont : Continuous F := by
    dsimp [F, verticalDigammaBernoulliKernel]
    apply Continuous.div
    · exact Complex.continuous_ofReal.comp
        ((periodizedBernoulli.continuous (by norm_num : 2 ≠ 1)).comp
          continuous_quotient_mk')
    · fun_prop
    · intro u
      apply pow_ne_zero
      intro hzero
      have him := congrArg Complex.im hzero
      simp at him
      linarith
  have hinterval : IntervalIntegrable F volume 0 t := hFcont.intervalIntegrable _ _
  have hg : IntegrableOn g (Set.Ioi t) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ht0).const_mul A
  have hpoint : ∀ᵐ u ∂volume.restrict (Set.Ioi t), ‖F u‖ ≤ g u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_verticalDigammaBernoulliKernel_le hA ht0 hu.le (hbern u)
  have hFtail : IntegrableOn F (Set.Ioi t) := by
    change Integrable F (volume.restrict (Set.Ioi t))
    change Integrable g (volume.restrict (Set.Ioi t)) at hg
    exact hg.mono' hFcont.aestronglyMeasurable.restrict hpoint
  have htail : ‖∫ u in Set.Ioi t, F u‖ ≤ A / (2 * t ^ 2) := by
    calc
      ‖∫ u in Set.Ioi t, F u‖ ≤ ∫ u in Set.Ioi t, g u :=
        MeasureTheory.norm_integral_le_of_norm_le hg hpoint
      _ = A * (∫ u in Set.Ioi t, u ^ (-3 : ℝ)) := by
        dsimp [g]
        rw [MeasureTheory.integral_const_mul]
      _ = A / (2 * t ^ 2) := by
        rw [integral_Ioi_rpow_of_lt (by norm_num) ht0]
        rw [show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg ht0.le,
          show t ^ (2 : ℝ) = t ^ (2 : ℕ) by norm_num [Real.rpow_natCast]]
        field_simp [ht0.ne']
  have hlow : ‖∫ u in (0 : ℝ)..t, F u‖ ≤ 8 * A / t ^ 2 := by
    have hconst := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := F) (a := 0) (b := t) (C := 8 * A / t ^ 3)
      (fun u _hu => norm_verticalDigammaBernoulliKernel_le_low hA ht0 (hbern u))
    rw [sub_zero, abs_of_pos ht0] at hconst
    calc
      _ ≤ (8 * A / t ^ 3) * t := hconst
      _ = 8 * A / t ^ 2 := by field_simp [ht0.ne']
  have hsplit :
      (∫ u in (0 : ℝ)..t, F u) + ∫ u in Set.Ioi t, F u =
        ∫ u in Set.Ioi (0 : ℝ), F u :=
    intervalIntegral.integral_interval_add_Ioi' hinterval hFtail
  rw [← hsplit]
  calc
    ‖(∫ u in (0 : ℝ)..t, F u) + ∫ u in Set.Ioi t, F u‖ ≤
        ‖∫ u in (0 : ℝ)..t, F u‖ + ‖∫ u in Set.Ioi t, F u‖ := norm_add_le _ _
    _ ≤ 8 * A / t ^ 2 + A / (2 * t ^ 2) := add_le_add hlow htail
    _ ≤ 9 * A / t ^ 2 := by
      field_simp [ht0.ne']
      nlinarith

private lemma log_norm_quarter_add_I_mul_half_sub_log_half_eq
    {t : ℝ} (ht : 0 < t) :
    Real.log ‖(1 / 4 : ℂ) + I * t / 2‖ - Real.log (t / 2) =
      Real.log (1 + 1 / (4 * t ^ 2)) / 2 := by
  let z : ℂ := (1 / 4 : ℂ) + I * t / 2
  let q : ℝ := 1 + 1 / (4 * t ^ 2)
  have ht2 : 0 < t / 2 := half_pos ht
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hnormSq : Complex.normSq z = (t / 2) ^ 2 * q := by
    dsimp [z, q]
    norm_num [Complex.normSq_apply]
    field_simp [ht.ne']
    ring
  rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg z), hnormSq,
    Real.log_mul (pow_ne_zero 2 ht2.ne') hq.ne', Real.log_pow]
  dsimp only [q]
  ring

private lemma abs_log_norm_quarter_add_I_mul_half_sub_log_half_le_inv_sq
    {t : ℝ} (ht : 1 ≤ t) :
    |Real.log ‖(1 / 4 : ℂ) + I * t / 2‖ - Real.log (t / 2)| ≤
      1 / (8 * t ^ 2) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let q : ℝ := 1 + 1 / (4 * t ^ 2)
  have hq1 : 1 ≤ q := by
    dsimp [q]
    exact le_add_of_nonneg_right (by positivity)
  have hq0 : 0 < q := zero_lt_one.trans_le hq1
  rw [log_norm_quarter_add_I_mul_half_sub_log_half_eq ht0]
  rw [abs_of_nonneg (div_nonneg (Real.log_nonneg hq1) (by norm_num))]
  calc
    Real.log q / 2 ≤ (q - 1) / 2 :=
      div_le_div_of_nonneg_right (Real.log_le_sub_one_of_pos hq0) (by norm_num)
    _ = 1 / (8 * t ^ 2) := by
      dsimp [q]
      field_simp [ht0.ne']
      ring

private lemma half_le_norm_quarter_add_I_mul_half {t : ℝ} :
    t / 2 ≤ ‖(1 / 4 : ℂ) + I * t / 2‖ := by
  have him : ((1 / 4 : ℂ) + I * t / 2).im = t / 2 := by simp
  rw [← him]
  exact (le_abs_self _).trans (Complex.abs_im_le_norm _)

private lemma abs_inv_two_mul_quarter_add_I_mul_half_re_div_two_le_inv_sq
    {t : ℝ} (ht : 1 ≤ t) :
    |(((2 : ℂ) * ((1 / 4 : ℂ) + I * t / 2))⁻¹).re / 2| ≤ 1 / t ^ 2 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hden : 0 < t ^ 2 + 1 / 4 := by positivity
  have hvalue :
      (((2 : ℂ) * ((1 / 4 : ℂ) + I * t / 2))⁻¹).re / 2 =
        1 / (4 * (t ^ 2 + 1 / 4)) := by
    rw [Complex.inv_re]
    norm_num [Complex.normSq_apply]
    field_simp [hden.ne']
    ring
  rw [hvalue, abs_of_nonneg (by positivity)]
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * (t ^ 2 + 1 / 4))
    (sq_pos_of_pos ht0)).2
  nlinarith [sq_nonneg t]

private lemma abs_inv_twelve_mul_quarter_add_I_mul_half_sq_re_div_two_le_inv_sq
    {t : ℝ} (ht : 1 ≤ t) :
    |(((12 : ℂ) * ((1 / 4 : ℂ) + I * t / 2) ^ 2)⁻¹).re / 2| ≤
      1 / t ^ 2 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let z : ℂ := (1 / 4 : ℂ) + I * t / 2
  have hz : t / 2 ≤ ‖z‖ := half_le_norm_quarter_add_I_mul_half
  have hz0 : 0 < ‖z‖ := (half_pos ht0).trans_le hz
  calc
    |(((12 : ℂ) * z ^ 2)⁻¹).re / 2| =
        |(((12 : ℂ) * z ^ 2)⁻¹).re| / 2 := by
      conv_lhs => rw [abs_div]
      norm_num
    _ ≤ ‖((12 : ℂ) * z ^ 2)⁻¹‖ / 2 :=
      div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (by norm_num)
    _ = 1 / (24 * ‖z‖ ^ 2) := by
      rw [norm_inv, norm_mul, norm_pow]
      norm_num
      field_simp [hz0.ne']
      ring
    _ ≤ 1 / (6 * t ^ 2) := by
      have hsq : (t / 2) ^ 2 ≤ ‖z‖ ^ 2 :=
        pow_le_pow_left₀ (half_pos ht0).le hz 2
      apply (div_le_div_iff₀ (by positivity : 0 < 24 * ‖z‖ ^ 2)
        (by positivity : 0 < 6 * t ^ 2)).2
      nlinarith
    _ ≤ 1 / t ^ 2 := by
      field_simp [ht0.ne']
      norm_num

private lemma integrableOn_Ioi_periodizedBernoulli_div_const_add_cube
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn
      (fun u : ℝ =>
        ((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ) /
          (z + u) ^ 3) (Set.Ioi (0 : ℝ)) := by
  obtain ⟨A, hA, hbern⟩ := exists_periodizedBernoulli_two_norm_bound
  let F : ℝ → ℂ := fun u =>
    ((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ) / (z + u) ^ 3
  let g : ℝ → ℝ := fun u => A * u ^ (-3 : ℝ)
  have hFcont : ContinuousOn F (Set.Ici (0 : ℝ)) := by
    intro u hu
    have hden : z + (u : ℂ) ≠ 0 := by
      intro hzero
      have hrepos : 0 < (z + (u : ℂ)).re := by
        simpa using add_pos_of_pos_of_nonneg hz hu
      exact hrepos.ne' (by rw [hzero]; simp)
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div
    · exact Complex.continuous_ofReal.continuousAt.comp
        ((periodizedBernoulli.continuous (by norm_num : 2 ≠ 1)).continuousAt.comp
          continuous_quotient_mk'.continuousAt)
    · exact ((continuousAt_const.add Complex.continuous_ofReal.continuousAt).pow 3)
    · exact pow_ne_zero 3 hden
  have hlow : IntegrableOn F (Set.Ioc (0 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have hsub : Set.uIcc (0 : ℝ) 1 ⊆ Set.Ici 0 := by
      intro x hx
      rw [Set.uIcc_of_le zero_le_one] at hx
      exact hx.1
    exact (hFcont.mono hsub).intervalIntegrable
  have hg : IntegrableOn g (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul A
  have hpoint : ∀ᵐ u ∂volume.restrict (Set.Ioi (1 : ℝ)), ‖F u‖ ≤ g u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := zero_lt_one.trans hu
    have hre : u ≤ (z + (u : ℂ)).re := by simp; exact hz.le
    have hunorm : u ≤ ‖z + (u : ℂ)‖ :=
      hre.trans (le_abs_self _ |>.trans (Complex.abs_re_le_norm _))
    rw [show F u =
      ((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ) /
        (z + u) ^ 3 by rfl, norm_div, norm_pow]
    dsimp only [g]
    rw [Real.rpow_neg hu0.le]
    rw [show u ^ (3 : ℝ) = u ^ (3 : ℕ) by norm_num [Real.rpow_natCast]]
    change
      ‖((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ /
          ‖z + (u : ℂ)‖ ^ 3 ≤ A * (u ^ 3)⁻¹
    have hu3 : 0 < u ^ 3 := pow_pos hu0 _
    have hden3 : u ^ 3 ≤ ‖z + (u : ℂ)‖ ^ 3 :=
      pow_le_pow_left₀ hu0.le hunorm 3
    rw [div_eq_mul_inv]
    exact mul_le_mul (hbern u) (inv_anti₀ hu3 hden3)
      (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) 3)) hA
  have htail : IntegrableOn F (Set.Ioi (1 : ℝ)) := by
    change Integrable F (volume.restrict (Set.Ioi (1 : ℝ)))
    change Integrable g (volume.restrict (Set.Ioi (1 : ℝ))) at hg
    exact hg.mono'
      ((hFcont.mono (Set.Ioi_subset_Ici zero_le_one)).aestronglyMeasurable measurableSet_Ioi)
      hpoint
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact hlow.union htail

private theorem tendsto_inv_const_add_natCast (z : ℂ) :
    Tendsto (fun N : ℕ => (z + N)⁻¹) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℂ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hsmall : Tendsto (fun N : ℕ => 1 + z * (N : ℂ)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  have hprod := hinv.mul (hsmall.inv₀ (by norm_num : (1 : ℂ) ≠ 0))
  have hprod' : Tendsto
      (fun N : ℕ => (N : ℂ)⁻¹ * (1 + z * (N : ℂ)⁻¹)⁻¹) atTop (𝓝 0) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hfactor : z + (N : ℂ) =
      (N : ℂ) * (1 + z * (N : ℂ)⁻¹) := by
    field_simp [hNC]
    ring
  rw [hfactor, mul_inv_rev]
  exact mul_comm _ _

/-- Second-order Euler--Maclaurin expansion of the digamma function on the
right half-plane, with the remainder expressed by the periodic Bernoulli
function. -/
theorem digamma_eq_stirling_with_periodizedBernoulli {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z =
      Complex.log z - (2 * z)⁻¹ - (12 * z ^ 2)⁻¹ +
        ∫ u in Set.Ioi (0 : ℝ),
          ((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ) /
            (z + u) ^ 3 := by
  let K : ℝ → ℂ := fun u =>
    ((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ) / (z + u) ^ 3
  let E : ℕ → ℂ := fun N =>
    (((harmonic N : ℚ) : ℂ) - (Real.log N : ℂ) - Real.eulerMascheroniConstant) -
      (Complex.log (z + N) - (Real.log N : ℂ)) + Complex.log z - z⁻¹ / 2 -
      (z⁻¹) ^ 2 / 12 - (z + N)⁻¹ / 2 + ((z + N)⁻¹) ^ 2 / 12 +
      ∫ u in (0 : ℝ)..N, K u
  have hharmReal := Real.tendsto_harmonic_sub_log
  have hharmCast :
      Tendsto (fun N : ℕ => ((harmonic N : ℚ) : ℂ) - (Real.log N : ℂ)) atTop
        (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
    simpa [Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hharmReal
  have hharm :
      Tendsto
        (fun N : ℕ =>
          ((harmonic N : ℚ) : ℂ) - (Real.log N : ℂ) - Real.eulerMascheroniConstant)
        atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => (Real.eulerMascheroniConstant : ℂ)) atTop
        (𝓝 (Real.eulerMascheroniConstant : ℂ)) := tendsto_const_nhds
    simpa using hharmCast.sub hconst
  have hlog := tendsto_log_const_add_natCast_sub_log z hz
  have hinv := tendsto_inv_const_add_natCast z
  have hinvSq : Tendsto (fun N : ℕ => ((z + N)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using hinv.pow 2
  have hK : Tendsto (fun N : ℕ => ∫ u in (0 : ℝ)..N, K u) atTop
      (𝓝 (∫ u in Set.Ioi (0 : ℝ), K u)) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_Ioi_periodizedBernoulli_div_const_add_cube hz)
      tendsto_natCast_atTop_atTop
  have hE : Tendsto E atTop
      (𝓝 (Complex.log z - z⁻¹ / 2 - (z⁻¹) ^ 2 / 12 +
        ∫ u in Set.Ioi (0 : ℝ), K u)) := by
    dsimp only [E]
    convert (((((((hharm.sub hlog).add tendsto_const_nhds).sub
      (tendsto_const_nhds.div_const 2)).sub
      ((tendsto_const_nhds.pow 2).div_const 12)).sub
      (hinv.div_const 2)).add (hinvSq.div_const 12)).add hK) using 1 <;> ring
  have hsum := (PrimeNumberTheorem.summable_digammaGaussTerm hz).hasSum.tendsto_sum_nat
  have hpartial : Tendsto
      (fun N : ℕ =>
        -Real.eulerMascheroniConstant - z⁻¹ +
          ∑ n ∈ Finset.range N, PrimeNumberTheorem.digammaGaussTerm z n)
      atTop (𝓝 (Complex.digamma z)) := by
    have hconst : Tendsto
        (fun _ : ℕ => (-Real.eulerMascheroniConstant : ℂ) - z⁻¹) atTop
        (𝓝 ((-Real.eulerMascheroniConstant : ℂ) - z⁻¹)) := tendsto_const_nhds
    have h := hconst.add hsum
    rw [PrimeNumberTheorem.digamma_eq_gauss_series hz]
    exact h
  have hfinite : ∀ N : ℕ,
      -Real.eulerMascheroniConstant - z⁻¹ +
          ∑ n ∈ Finset.range N, PrimeNumberTheorem.digammaGaussTerm z n = E N := by
    intro N
    have hgauss :
        (∑ n ∈ Finset.range N, PrimeNumberTheorem.digammaGaussTerm z n) =
          ((harmonic N : ℚ) : ℂ) -
            ∑ n ∈ Finset.range N, (z + (n + 1 : ℕ))⁻¹ := by
      simp only [PrimeNumberTheorem.digammaGaussTerm, Finset.sum_sub_distrib]
      congr 1
      simp [harmonic]
    rw [hgauss, sum_range_inv_const_add_eulerMaclaurin hz N,
      intervalIntegral_inv_const_add_eq_log_sub hz N]
    dsimp only [E, K]
    ring
  have hpartial' : Tendsto E atTop (𝓝 (Complex.digamma z)) :=
    hpartial.congr' (Filter.Eventually.of_forall hfinite)
  have hmain := tendsto_nhds_unique hpartial' hE
  dsimp only [K] at hmain
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero] at hz
    simp at hz
  rw [show (2 * z)⁻¹ = z⁻¹ / 2 by field_simp [hz0],
    show (12 * z ^ 2)⁻¹ = (z⁻¹) ^ 2 / 12 by field_simp [hz0]]
  exact hmain

/-- The smooth vertical `Gammaℝ` phase velocity differs from the elementary
Stirling phase velocity by `O(1/t²)`. -/
theorem exists_abs_verticalGammaPhaseVelocity_sub_deriv_thetaModel_le_inv_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      |verticalGammaPhaseVelocity t - deriv thetaModel t| ≤ C / t ^ 2 := by
  obtain ⟨C, hC, hrem⟩ :=
    exists_norm_integral_Ioi_verticalDigammaBernoulliKernel_le_inv_sq
  refine ⟨3 + C, add_nonneg (by norm_num) hC, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let z : ℂ := (1 / 4 : ℂ) + I * t / 2
  let R : ℂ := ∫ u in Set.Ioi (0 : ℝ), verticalDigammaBernoulliKernel t u
  have hz : 0 < z.re := by
    dsimp [z]
    norm_num
  have hdig := digamma_eq_stirling_with_periodizedBernoulli hz
  have hR : ‖R‖ ≤ C / t ^ 2 := hrem t ht
  have hlogdiv :
      Real.log (t / (2 * Real.pi)) = Real.log (t / 2) - Real.log Real.pi := by
    rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring,
      Real.log_div (half_pos ht0).ne' Real.pi_ne_zero]
  have hdecomp :
      verticalGammaPhaseVelocity t - deriv thetaModel t =
        (Real.log ‖z‖ - Real.log (t / 2)) / 2 -
          (((2 : ℂ) * z)⁻¹).re / 2 -
          (((12 : ℂ) * z ^ 2)⁻¹).re / 2 + R.re / 2 := by
    rw [verticalGammaPhaseVelocity, deriv_thetaModel ht0]
    rw [show (1 / 4 : ℂ) + I * t / 2 = z by rfl, hdig]
    simp only [Complex.sub_re, Complex.add_re, Complex.log_re, Complex.ofReal_re]
    rw [hlogdiv]
    change
      (Real.log ‖z‖ - ((2 * z)⁻¹).re - ((12 * z ^ 2)⁻¹).re + R.re) / 2 -
          Real.log Real.pi / 2 -
          (1 / 2 * (Real.log (t / 2) - Real.log Real.pi)) = _
    ring
  have hlogTerm :
      |(Real.log ‖z‖ - Real.log (t / 2)) / 2| ≤ 1 / t ^ 2 := by
    have hlog := abs_log_norm_quarter_add_I_mul_half_sub_log_half_le_inv_sq ht
    change |Real.log ‖z‖ - Real.log (t / 2)| ≤ 1 / (8 * t ^ 2) at hlog
    calc
      |(Real.log ‖z‖ - Real.log (t / 2)) / 2| =
          |Real.log ‖z‖ - Real.log (t / 2)| / 2 := by
        conv_lhs => rw [abs_div]
        norm_num
      _ ≤ (1 / (8 * t ^ 2)) / 2 :=
        div_le_div_of_nonneg_right hlog (by norm_num)
      _ ≤ 1 / t ^ 2 := by
        field_simp [ht0.ne']
        norm_num
  have hfirst : |(((2 : ℂ) * z)⁻¹).re / 2| ≤ 1 / t ^ 2 := by
    exact abs_inv_two_mul_quarter_add_I_mul_half_re_div_two_le_inv_sq ht
  have hsecond : |(((12 : ℂ) * z ^ 2)⁻¹).re / 2| ≤ 1 / t ^ 2 := by
    exact abs_inv_twelve_mul_quarter_add_I_mul_half_sq_re_div_two_le_inv_sq ht
  have hremTerm : |R.re / 2| ≤ C / t ^ 2 := by
    calc
      |R.re / 2| = |R.re| / 2 := by
        conv_lhs => rw [abs_div]
        norm_num
      _ ≤ ‖R‖ / 2 :=
        div_le_div_of_nonneg_right (Complex.abs_re_le_norm R) (by norm_num)
      _ ≤ (C / t ^ 2) / 2 :=
        div_le_div_of_nonneg_right hR (by norm_num)
      _ ≤ C / t ^ 2 := by
        have hCt : 0 ≤ C / t ^ 2 := div_nonneg hC (sq_nonneg t)
        linarith
  rw [hdecomp]
  calc
    |(Real.log ‖z‖ - Real.log (t / 2)) / 2 -
        ((2 * z)⁻¹).re / 2 - ((12 * z ^ 2)⁻¹).re / 2 + R.re / 2| ≤
        |(Real.log ‖z‖ - Real.log (t / 2)) / 2| +
          |((2 * z)⁻¹).re / 2| + |((12 * z ^ 2)⁻¹).re / 2| + |R.re / 2| := by
      calc
        _ ≤ |(Real.log ‖z‖ - Real.log (t / 2)) / 2 -
              ((2 * z)⁻¹).re / 2 - ((12 * z ^ 2)⁻¹).re / 2| + |R.re / 2| :=
          abs_add_le _ _
        _ ≤ (|(Real.log ‖z‖ - Real.log (t / 2)) / 2 -
              ((2 * z)⁻¹).re / 2| + |((12 * z ^ 2)⁻¹).re / 2|) + |R.re / 2| :=
          by
            gcongr
            exact abs_sub _ _
        _ ≤ (|(Real.log ‖z‖ - Real.log (t / 2)) / 2| +
              |((2 * z)⁻¹).re / 2| + |((12 * z ^ 2)⁻¹).re / 2|) + |R.re / 2| :=
          by
            gcongr
            exact abs_sub _ _
        _ = _ := by ring
    _ ≤ 1 / t ^ 2 + 1 / t ^ 2 + 1 / t ^ 2 + C / t ^ 2 :=
      add_le_add (add_le_add (add_le_add hlogTerm hfirst) hsecond) hremTerm
    _ = (3 + C) / t ^ 2 := by ring

/-- A smooth lift of the vertical `Gammaℝ` phase, anchored at `t = 1`. -/
noncomputable def verticalGammaUnwrappedPhase (t : ℝ) : ℝ :=
  thetaPhase 1 + ∫ x in (1 : ℝ)..t, verticalGammaPhaseVelocity x

theorem continuous_verticalGammaUnwrappedPhase :
    Continuous verticalGammaUnwrappedPhase := by
  change Continuous (fun t : ℝ =>
    thetaPhase 1 + ∫ x in (1 : ℝ)..t, verticalGammaPhaseVelocity x)
  exact continuous_const.add
    (intervalIntegral.differentiable_integral_of_continuous
      continuous_verticalGammaPhaseVelocity).continuous

/-- The smooth phase is an actual lift of the principal `Gammaℝ` phase: their
complex unit phases agree exactly. -/
theorem exp_I_verticalGammaUnwrappedPhase_eq_exp_I_thetaPhase
    {t : ℝ} (ht : 1 ≤ t) :
    Complex.exp (I * verticalGammaUnwrappedPhase t) =
      Complex.exp (I * thetaPhase t) := by
  let D : ℝ → ℝ := fun x =>
    (Complex.digamma ((1 / 4 : ℂ) + I * x / 2)).re / 2
  have hDCont : Continuous D := by
    have him := Complex.continuous_im.comp continuous_gammaQuarterLogDerivative
    convert him using 1
    funext x
    simp [D, gammaQuarterLogDerivative, Complex.mul_im]
  have hDInt : IntervalIntegrable D volume 1 t := hDCont.intervalIntegrable _ _
  have hconstInt : IntervalIntegrable (fun _ : ℝ => Real.log Real.pi / 2) volume 1 t :=
    continuous_const.intervalIntegrable _ _
  have hvelIntegral :
      (∫ x in (1 : ℝ)..t, verticalGammaPhaseVelocity x) =
        (gammaQuarterLogIntegral t).im - (t - 1) * (Real.log Real.pi / 2) := by
    rw [show verticalGammaPhaseVelocity =
        fun x => D x - Real.log Real.pi / 2 by rfl]
    rw [intervalIntegral.integral_sub hDInt hconstInt,
      intervalIntegral.integral_const, ← gammaQuarterLogIntegral_im]
    simp only [smul_eq_mul]
  have harg := exp_I_arg_gammaQuarterVertical_eq_base_add_integral ht
  rw [verticalGammaUnwrappedPhase, hvelIntegral]
  have hleft :
      I * (thetaPhase 1 +
        ((gammaQuarterLogIntegral t).im -
          (t - 1) * (Real.log Real.pi / 2)) : ℂ) =
        I * (Complex.arg (gammaQuarterVertical 1) +
          (gammaQuarterLogIntegral t).im) +
        (-I * (t / 2 * Real.log Real.pi)) := by
    simp only [thetaPhase, gammaQuarterVertical]
    push_cast
    ring
  have hright :
      I * (thetaPhase t : ℂ) =
        I * Complex.arg (gammaQuarterVertical t) +
          (-I * (t / 2 * Real.log Real.pi)) := by
    simp only [thetaPhase, gammaQuarterVertical]
    push_cast
    ring
  push_cast
  rw [hleft, Complex.exp_add, ← harg, ← Complex.exp_add, ← hright]

theorem continuousOn_exp_I_thetaPhase_Ici_one :
    ContinuousOn (fun t : ℝ => Complex.exp (I * thetaPhase t)) (Set.Ici 1) := by
  have hlift : Continuous (fun t : ℝ =>
      Complex.exp (I * verticalGammaUnwrappedPhase t)) :=
    (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_verticalGammaUnwrappedPhase)).cexp
  apply hlift.continuousOn.congr
  intro t ht
  exact (exp_I_verticalGammaUnwrappedPhase_eq_exp_I_thetaPhase ht).symm

/-- The smooth vertical Gamma phase differs from the elementary Stirling phase
by a fixed constant and an `O(1/t)` tail. -/
theorem exists_verticalGammaUnwrappedPhase_sub_thetaModel_tendsto_const_inv :
    ∃ κ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      |verticalGammaUnwrappedPhase t - thetaModel t - κ| ≤ C / t := by
  obtain ⟨C, hC, herr⟩ :=
    exists_abs_verticalGammaPhaseVelocity_sub_deriv_thetaModel_le_inv_sq
  let modelVelocity : ℝ → ℝ := fun x =>
    (1 / 2 : ℝ) * Real.log (x / (2 * Real.pi))
  let e : ℝ → ℝ := fun x => verticalGammaPhaseVelocity x - modelVelocity x
  let g : ℝ → ℝ := fun x => C * x ^ (-2 : ℝ)
  have hmodelCont : ContinuousOn modelVelocity (Set.Ici (1 : ℝ)) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    dsimp only [modelVelocity]
    apply ContinuousAt.const_mul
    apply ContinuousAt.log
    · fun_prop
    · have hxpos : 0 < x := zero_lt_one.trans_le hx
      exact div_ne_zero hxpos.ne' (by positivity)
  have heCont : ContinuousOn e (Set.Ici (1 : ℝ)) := by
    exact continuous_verticalGammaPhaseVelocity.continuousOn.sub hmodelCont
  have hg1 : IntegrableOn g (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul C
  have hpoint1 : ∀ᵐ x ∂volume.restrict (Set.Ioi (1 : ℝ)), ‖e x‖ ≤ g x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := hx.le
    have hx0 : 0 < x := zero_lt_one.trans hx
    have h := herr x hx1
    rw [deriv_thetaModel hx0] at h
    change |e x| ≤ C / x ^ 2 at h
    rw [Real.norm_eq_abs]
    dsimp only [g]
    rw [Real.rpow_neg hx0.le,
      show x ^ (2 : ℝ) = x ^ (2 : ℕ) by norm_num [Real.rpow_natCast]]
    simpa [div_eq_mul_inv] using h
  have heInt1 : IntegrableOn e (Set.Ioi (1 : ℝ)) := by
    change Integrable e (volume.restrict (Set.Ioi (1 : ℝ)))
    change Integrable g (volume.restrict (Set.Ioi (1 : ℝ))) at hg1
    exact hg1.mono'
      ((heCont.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
      hpoint1
  refine ⟨thetaPhase 1 - thetaModel 1 + ∫ x in Set.Ioi (1 : ℝ), e x, C, hC, ?_⟩
  intro t ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hIcc : Set.uIcc (1 : ℝ) t = Set.Icc 1 t := Set.uIcc_of_le ht
  have hvelInt : IntervalIntegrable verticalGammaPhaseVelocity volume 1 t :=
    continuous_verticalGammaPhaseVelocity.intervalIntegrable _ _
  have hmodelIcc : ContinuousOn modelVelocity (Set.Icc (1 : ℝ) t) :=
    hmodelCont.mono (Set.Icc_subset_Ici_self)
  have hmodelInt : IntervalIntegrable modelVelocity volume 1 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht hmodelIcc
  have hmodelDeriv : ∀ x ∈ Set.uIcc (1 : ℝ) t,
      HasDerivAt thetaModel (modelVelocity x) x := by
    intro x hx
    rw [hIcc] at hx
    have hx0 : 0 < x := zero_lt_one.trans_le hx.1
    have hdiff : DifferentiableAt ℝ thetaModel x := by
      change DifferentiableAt ℝ
        (fun y : ℝ =>
          y / 2 * Real.log (y / (2 * Real.pi)) - y / 2 - Real.pi / 8) x
      fun_prop (disch := positivity)
    have hder := hdiff.hasDerivAt
    rw [deriv_thetaModel hx0] at hder
    exact hder
  have hmodelIntegral :
      (∫ x in (1 : ℝ)..t, modelVelocity x) = thetaModel t - thetaModel 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hmodelDeriv hmodelInt
  have heInterval : IntervalIntegrable e volume 1 t := by
    exact hvelInt.sub hmodelInt
  have heIntegral :
      (∫ x in (1 : ℝ)..t, e x) =
        (∫ x in (1 : ℝ)..t, verticalGammaPhaseVelocity x) -
          ∫ x in (1 : ℝ)..t, modelVelocity x := by
    exact intervalIntegral.integral_sub hvelInt hmodelInt
  have hcorrection :
      verticalGammaUnwrappedPhase t - thetaModel t =
        thetaPhase 1 - thetaModel 1 + ∫ x in (1 : ℝ)..t, e x := by
    rw [verticalGammaUnwrappedPhase, heIntegral, hmodelIntegral]
    ring
  have hgTail : IntegrableOn g (Set.Ioi t) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ht0).const_mul C
  have hpointTail : ∀ᵐ x ∂volume.restrict (Set.Ioi t), ‖e x‖ ≤ g x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := ht.trans hx.le
    have hx0 : 0 < x := ht0.trans hx
    have h := herr x hx1
    rw [deriv_thetaModel hx0] at h
    change |e x| ≤ C / x ^ 2 at h
    rw [Real.norm_eq_abs]
    dsimp only [g]
    rw [Real.rpow_neg hx0.le,
      show x ^ (2 : ℝ) = x ^ (2 : ℕ) by norm_num [Real.rpow_natCast]]
    simpa [div_eq_mul_inv] using h
  have heIntTail : IntegrableOn e (Set.Ioi t) := heInt1.mono_set (Set.Ioi_subset_Ioi ht)
  have htail : |∫ x in Set.Ioi t, e x| ≤ C / t := by
    calc
      |∫ x in Set.Ioi t, e x| = ‖∫ x in Set.Ioi t, e x‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ x in Set.Ioi t, g x :=
        MeasureTheory.norm_integral_le_of_norm_le hgTail hpointTail
      _ = C * (∫ x in Set.Ioi t, x ^ (-2 : ℝ)) := by
        dsimp [g]
        rw [MeasureTheory.integral_const_mul]
      _ = C / t := by
        rw [integral_Ioi_rpow_of_lt (by norm_num) ht0]
        rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
        ring
  have hsplit :
      (∫ x in (1 : ℝ)..t, e x) + ∫ x in Set.Ioi t, e x =
        ∫ x in Set.Ioi (1 : ℝ), e x :=
    intervalIntegral.integral_interval_add_Ioi' heInterval heIntTail
  rw [hcorrection]
  have heq :
      thetaPhase 1 - thetaModel 1 + (∫ x in (1 : ℝ)..t, e x) -
          (thetaPhase 1 - thetaModel 1 + ∫ x in Set.Ioi (1 : ℝ), e x) =
        -(∫ x in Set.Ioi t, e x) := by
    rw [← hsplit]
    ring
  rw [heq, abs_neg]
  exact htail

/-- The actual `Gammaℝ` unit phase has the elementary Stirling phase as its
leading term, up to one fixed unit phase and an `O(1/t)` error. -/
theorem exists_norm_exp_I_thetaPhase_sub_const_mul_exp_I_thetaModel_le_inv :
    ∃ κ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖Complex.exp (I * thetaPhase t) -
          Complex.exp (I * κ) * Complex.exp (I * thetaModel t)‖ ≤ C / t := by
  obtain ⟨κ, C, hC, hphase⟩ :=
    exists_verticalGammaUnwrappedPhase_sub_thetaModel_tendsto_const_inv
  refine ⟨κ, C, hC, ?_⟩
  intro t ht
  have hactual := exp_I_verticalGammaUnwrappedPhase_eq_exp_I_thetaPhase ht
  have hmodel :
      Complex.exp (I * κ) * Complex.exp (I * thetaModel t) =
        Complex.exp (I * (thetaModel t + κ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfactor :
      Complex.exp (I * verticalGammaUnwrappedPhase t) -
          Complex.exp (I * (thetaModel t + κ)) =
        Complex.exp (I * (thetaModel t + κ)) *
          (Complex.exp
            (I * (verticalGammaUnwrappedPhase t - thetaModel t - κ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hunit :
      ‖Complex.exp (I * (thetaModel t + κ))‖ = 1 :=
    by
      convert Complex.norm_exp_I_mul_ofReal (thetaModel t + κ) using 1
      all_goals push_cast
      all_goals rfl
  rw [← hactual, hmodel, hfactor, norm_mul, hunit, one_mul]
  calc
    ‖Complex.exp
          (I * (verticalGammaUnwrappedPhase t - thetaModel t - κ)) - 1‖ ≤
        ‖verticalGammaUnwrappedPhase t - thetaModel t - κ‖ :=
      by
        convert (Real.norm_exp_I_mul_ofReal_sub_one_le
          (x := verticalGammaUnwrappedPhase t - thetaModel t - κ)) using 1
        all_goals push_cast
        all_goals rfl
    _ = |verticalGammaUnwrappedPhase t - thetaModel t - κ| := Real.norm_eq_abs _
    _ ≤ C / t := hphase t ht

private lemma norm_verticalStirlingBernoulliKernel_le
    {A t u : ℝ} (hA : 0 ≤ A) (ht : 0 < t) (htu : t ≤ u)
    (hbern :
      ‖((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ ≤ A) :
    ‖verticalStirlingBernoulliKernel t u‖ ≤ A * u ^ (-2 : ℝ) := by
  have hu : 0 < u := ht.trans_le htu
  let z : ℂ := (1 / 4 : ℂ) + I * t / 2 + u
  have hre : u ≤ z.re := by
    dsimp [z]
    norm_num
  have huz : u ≤ ‖z‖ :=
    hre.trans (le_abs_self z.re |>.trans (Complex.abs_re_le_norm z))
  have hzpos : 0 < ‖z‖ := hu.trans_le huz
  rw [verticalStirlingBernoulliKernel, norm_div, norm_pow]
  change
    ‖((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ / ‖z‖ ^ 2 ≤
      A * u ^ (-2 : ℝ)
  rw [Real.rpow_neg (le_of_lt hu), Real.rpow_two]
  have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
  have hz2 : 0 < ‖z‖ ^ 2 := sq_pos_of_pos hzpos
  have hsq : u ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  calc
    _ ≤ A / ‖z‖ ^ 2 := div_le_div_of_nonneg_right hbern hz2.le
    _ ≤ A / u ^ 2 := div_le_div_of_nonneg_left hA hu2 hsq
    _ = A * (u ^ 2)⁻¹ := by rw [div_eq_mul_inv]

private lemma norm_verticalStirlingBernoulliKernel_le_low
    {A t u : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    (hbern :
      ‖((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ ≤ A) :
    ‖verticalStirlingBernoulliKernel t u‖ ≤ 4 * A / t ^ 2 := by
  let z : ℂ := (1 / 4 : ℂ) + I * t / 2 + u
  have him_eq : z.im = t / 2 := by
    dsimp [z]
    simp
  have him : t / 2 ≤ ‖z‖ := by
    rw [← him_eq]
    exact (le_abs_self z.im).trans (Complex.abs_im_le_norm z)
  have him0 : 0 < t / 2 := half_pos ht
  have hz0 : 0 < ‖z‖ := him0.trans_le him
  have hsq : (t / 2) ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  rw [verticalStirlingBernoulliKernel, norm_div, norm_pow]
  change
    ‖((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ)‖ / ‖z‖ ^ 2 ≤
      4 * A / t ^ 2
  calc
    _ ≤ A / ‖z‖ ^ 2 :=
      div_le_div_of_nonneg_right hbern (sq_nonneg _)
    _ ≤ A / (t / 2) ^ 2 :=
      div_le_div_of_nonneg_left hA (sq_pos_of_pos him0) hsq
    _ = 4 * A / t ^ 2 := by field_simp [ht.ne']; ring

/-- The high tail of the periodic-Bernoulli remainder in vertical Stirling is
`O(1/t)`.  This is the quantitative part of the Euler-summation remainder;
the omitted compact interval is handled separately in the full formula. -/
theorem exists_norm_integral_Ioi_verticalStirlingBernoulliKernel_le_inv :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖∫ u in Set.Ioi t, verticalStirlingBernoulliKernel t u‖ ≤ C / t := by
  obtain ⟨A, hA, hbern⟩ := exists_periodizedBernoulli_two_norm_bound
  refine ⟨A, hA, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let g : ℝ → ℝ := fun u => A * u ^ (-2 : ℝ)
  have hg : IntegrableOn g (Set.Ioi t) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ht0).const_mul A
  have hpoint : ∀ᵐ u ∂volume.restrict (Set.Ioi t),
      ‖verticalStirlingBernoulliKernel t u‖ ≤ g u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_verticalStirlingBernoulliKernel_le hA ht0 hu.le (hbern u)
  calc
    ‖∫ u in Set.Ioi t, verticalStirlingBernoulliKernel t u‖ ≤
        ∫ u in Set.Ioi t, g u :=
      MeasureTheory.norm_integral_le_of_norm_le hg hpoint
    _ = A * (∫ u in Set.Ioi t, u ^ (-2 : ℝ)) :=
      by dsimp [g]; rw [MeasureTheory.integral_const_mul]
    _ = A / t := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) ht0]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      field_simp [ht0.ne']

/-- The complete periodic-Bernoulli remainder integral in the vertical
logarithmic Stirling formula is `O(1/t)`. -/
theorem exists_norm_integral_Ioi_zero_verticalStirlingBernoulliKernel_le_inv :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖∫ u in Set.Ioi (0 : ℝ), verticalStirlingBernoulliKernel t u‖ ≤ C / t := by
  obtain ⟨A, hA, hbern⟩ := exists_periodizedBernoulli_two_norm_bound
  refine ⟨5 * A, mul_nonneg (by norm_num) hA, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let F : ℝ → ℂ := verticalStirlingBernoulliKernel t
  let g : ℝ → ℝ := fun u => A * u ^ (-2 : ℝ)
  have hFcont : Continuous F := by
    dsimp [F, verticalStirlingBernoulliKernel]
    apply Continuous.div
    · exact Complex.continuous_ofReal.comp
        ((periodizedBernoulli.continuous (by norm_num : 2 ≠ 1)).comp
          continuous_quotient_mk')
    · fun_prop
    · intro u
      apply pow_ne_zero
      intro hzero
      have him := congrArg Complex.im hzero
      simp at him
      linarith
  have hinterval : IntervalIntegrable F volume 0 t := hFcont.intervalIntegrable _ _
  have hg : IntegrableOn g (Set.Ioi t) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ht0).const_mul A
  have hpoint : ∀ᵐ u ∂volume.restrict (Set.Ioi t), ‖F u‖ ≤ g u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_verticalStirlingBernoulliKernel_le hA ht0 hu.le (hbern u)
  have hFtail : IntegrableOn F (Set.Ioi t) := by
    change Integrable F (volume.restrict (Set.Ioi t))
    change Integrable g (volume.restrict (Set.Ioi t)) at hg
    exact hg.mono' hFcont.aestronglyMeasurable.restrict hpoint
  have htail : ‖∫ u in Set.Ioi t, F u‖ ≤ A / t := by
    calc
      ‖∫ u in Set.Ioi t, F u‖ ≤ ∫ u in Set.Ioi t, g u :=
        MeasureTheory.norm_integral_le_of_norm_le hg hpoint
      _ = A * (∫ u in Set.Ioi t, u ^ (-2 : ℝ)) := by
        dsimp [g]
        rw [MeasureTheory.integral_const_mul]
      _ = A / t := by
        rw [integral_Ioi_rpow_of_lt (by norm_num) ht0]
        rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
        field_simp [ht0.ne']
  have hlow : ‖∫ u in (0 : ℝ)..t, F u‖ ≤ 4 * A / t := by
    have hconst := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := F) (a := 0) (b := t) (C := 4 * A / t ^ 2)
      (fun u _hu => norm_verticalStirlingBernoulliKernel_le_low hA ht0 (hbern u))
    rw [sub_zero, abs_of_pos ht0] at hconst
    calc
      _ ≤ (4 * A / t ^ 2) * t := hconst
      _ = 4 * A / t := by field_simp [ht0.ne']
  have hsplit :
      (∫ u in (0 : ℝ)..t, F u) + ∫ u in Set.Ioi t, F u =
        ∫ u in Set.Ioi (0 : ℝ), F u :=
    intervalIntegral.integral_interval_add_Ioi' hinterval hFtail
  rw [← hsplit]
  calc
    ‖(∫ u in (0 : ℝ)..t, F u) + ∫ u in Set.Ioi t, F u‖ ≤
        ‖∫ u in (0 : ℝ)..t, F u‖ + ‖∫ u in Set.Ioi t, F u‖ := norm_add_le _ _
    _ ≤ 4 * A / t + A / t := add_le_add hlow htail
    _ = 5 * A / t := by ring

end HardyTheorem
