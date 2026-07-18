import HardyTheorem.FirstZetaApproximation
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

/-- The periodic Bernoulli remainder kernel in the first neglected term of
the logarithmic Stirling expansion at `1 / 4 + I * t / 2`. -/
noncomputable def verticalStirlingBernoulliKernel (t u : ℝ) : ℂ :=
  ((periodizedBernoulli 2 (u : AddCircle (1 : ℝ)) : ℝ) : ℂ) /
    (((1 / 4 : ℂ) + I * t / 2 + u) ^ 2)

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
