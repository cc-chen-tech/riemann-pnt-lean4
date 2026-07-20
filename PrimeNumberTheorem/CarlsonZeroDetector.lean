import PrimeNumberTheorem.MollifiedZetaError
import Mathlib.NumberTheory.LSeries.Injectivity

open Complex
open Filter Topology
open scoped Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Along the positive real axis, the Riemann zeta function tends to its
first Dirichlet-series coefficient. -/
theorem tendsto_riemannZeta_real_atTop :
    Tendsto (fun x : ℝ => riemannZeta (x : ℂ)) atTop (𝓝 1) := by
  have hL :
      Tendsto (fun x : ℝ => LSeries (ArithmeticFunction.zeta ·) (x : ℂ))
        atTop (𝓝 1) := by
    simpa using LSeries.tendsto_atTop
      (f := (ArithmeticFunction.zeta ·))
      (by
        rw [ArithmeticFunction.abscissaOfAbsConv_zeta]
        exact EReal.coe_lt_top 1)
  apply hL.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact ArithmeticFunction.LSeries_zeta_eq_riemannZeta
    (s := (x : ℂ)) (by simpa using hx)

/-- The mollified zeta error tends to zero along the positive real axis. -/
theorem tendsto_mollifiedZetaError_real_atTop (X : ℕ) (hX : 1 ≤ X) :
    Tendsto (fun x : ℝ => mollifiedZetaError X (x : ℂ)) atTop (𝓝 0) := by
  have hmul := tendsto_riemannZeta_real_atTop.mul
    (tendsto_mobiusMollifier_atTop X hX)
  have hsub := hmul.sub
    (tendsto_const_nhds :
      Tendsto (fun _x : ℝ => (1 : ℂ)) atTop (𝓝 1))
  simpa [mollifiedZetaError] using hsub

/-- Carlson's auxiliary zero detector `h_X = 1 - f_X^2`, where
`f_X = zeta * M_X - 1`. -/
noncomputable def carlsonZeroDetector (X : ℕ) (s : ℂ) : ℂ :=
  1 - mollifiedZetaError X s ^ 2

/-- Carlson's original detector is analytic away from the zeta pole at
`s = 1`. -/
theorem analyticAt_carlsonZeroDetector_of_ne_one
    (X : ℕ) {s : ℂ} (hs1 : s ≠ 1) :
    AnalyticAt ℂ (carlsonZeroDetector X) s := by
  have hzeta : AnalyticAt ℂ riemannZeta s :=
    ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one s hs1
  have hm : AnalyticAt ℂ (mobiusMollifier X) s :=
    analyticAt_mobiusMollifier X s
  have herr : AnalyticAt ℂ (mollifiedZetaError X) s := by
    unfold mollifiedZetaError
    exact (hzeta.mul hm).sub analyticAt_const
  unfold carlsonZeroDetector
  exact analyticAt_const.sub (herr.pow 2)

/-- Carlson's detector tends to one along the positive real axis. -/
theorem tendsto_carlsonZeroDetector_real_atTop (X : ℕ) (hX : 1 ≤ X) :
    Tendsto (fun x : ℝ => carlsonZeroDetector X (x : ℂ)) atTop (𝓝 1) := by
  have hpow := (tendsto_mollifiedZetaError_real_atTop X hX).pow 2
  have hsub :=
    (tendsto_const_nhds :
      Tendsto (fun _x : ℝ => (1 : ℂ)) atTop (𝓝 1)).sub hpow
  simpa [carlsonZeroDetector] using hsub

/-- Pole-free Carlson detector on the right half-plane.  Replacing zeta by
its analytic pole unit makes this function analytic across `s = 1`; away
from `0` and `1` it is `(s - 1)^2 * carlsonZeroDetector X s`. -/
noncomputable def regularizedCarlsonZeroDetector (X : ℕ) (s : ℂ) : ℂ :=
  let q := ZeroFreeRegion.riemannZetaPoleUnitAtOne s
  let m := mobiusMollifier X s
  q * m * (2 * (s - 1) - q * m)

/-- The pole-free Carlson detector is analytic on every right half-plane
contained in `Re(s) > 0`. -/
theorem analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
    {theta : ℝ} (htheta : 0 ≤ theta) (X : ℕ) :
    AnalyticOnNhd ℂ (regularizedCarlsonZeroDetector X)
      {s : ℂ | theta < s.re} := by
  intro s hs
  have hq : AnalyticAt ℂ ZeroFreeRegion.riemannZetaPoleUnitAtOne s :=
    ZeroFreeRegion.analyticOnNhd_riemannZetaPoleUnitAtOne_re_gt htheta s hs
  have hm : AnalyticAt ℂ (mobiusMollifier X) s :=
    analyticAt_mobiusMollifier X s
  have hlinear : AnalyticAt ℂ (fun z : ℂ => 2 * (z - 1)) s :=
    analyticAt_const.mul (analyticAt_id.sub analyticAt_const)
  unfold regularizedCarlsonZeroDetector
  exact (hq.mul hm).mul (hlinear.sub (hq.mul hm))

/-- Globally the pole-free detector is meromorphic.  Its possible behavior at
`0` is harmless for Carlson rectangles, which lie in `Re(s) > 1/2`. -/
theorem meromorphic_regularizedCarlsonZeroDetector (X : ℕ) :
    Meromorphic (regularizedCarlsonZeroDetector X) := by
  intro s
  have hcompleted : MeromorphicAt completedRiemannZeta₀ s :=
    (differentiable_completedZeta₀.analyticAt s).meromorphicAt
  have hid : MeromorphicAt (fun z : ℂ => z) s :=
    analyticAt_id.meromorphicAt
  have honeDiv : MeromorphicAt (fun z : ℂ => 1 / z) s :=
    (MeromorphicAt.const 1 s).div hid
  have hgammaInv : MeromorphicAt (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
    (differentiable_Gammaℝ_inv.analyticAt s).meromorphicAt
  have hregular : MeromorphicAt ZeroFreeRegion.riemannZetaRegularAtOne s := by
    unfold ZeroFreeRegion.riemannZetaRegularAtOne
    exact (hcompleted.sub honeDiv).mul hgammaInv
  have hq : MeromorphicAt ZeroFreeRegion.riemannZetaPoleUnitAtOne s := by
    unfold ZeroFreeRegion.riemannZetaPoleUnitAtOne
    exact (((analyticAt_id.sub analyticAt_const).meromorphicAt.mul hregular).add
      hgammaInv)
  have hm : MeromorphicAt (mobiusMollifier X) s :=
    (analyticAt_mobiusMollifier X s).meromorphicAt
  have hlinear : MeromorphicAt (fun z : ℂ => 2 * (z - 1)) s :=
    (analyticAt_const.mul
      (analyticAt_id.sub analyticAt_const)).meromorphicAt
  unfold regularizedCarlsonZeroDetector
  exact (hq.mul hm).mul (hlinear.sub (hq.mul hm))

/-- The detector factors through zeta, so every zeta zero is a detector zero. -/
theorem carlsonZeroDetector_eq_zeta_mul_mollifier_factorization
    (X : ℕ) (s : ℂ) :
    carlsonZeroDetector X s =
      (riemannZeta s * mobiusMollifier X s) *
        (2 - riemannZeta s * mobiusMollifier X s) := by
  unfold carlsonZeroDetector mollifiedZetaError
  ring

/-- Away from the removable points, the analytic detector is the original
Carlson detector multiplied by the square cancelling its pole at `1`. -/
theorem regularizedCarlsonZeroDetector_eq_sub_one_sq_mul
    (X : ℕ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    regularizedCarlsonZeroDetector X s =
      (s - 1) ^ 2 * carlsonZeroDetector X s := by
  unfold regularizedCarlsonZeroDetector
  rw [ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
    hs0 hs1,
    carlsonZeroDetector_eq_zeta_mul_mollifier_factorization]
  ring

/-- Away from `0`, `1`, and detector zeros, the logarithmic derivative of
the regularized detector splits into the two pole-cancelling linear factors
and the original Carlson detector. -/
theorem logDeriv_regularizedCarlsonZeroDetector_eq_two_inv_add
    (X : ℕ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hdet : carlsonZeroDetector X s ≠ 0) :
    logDeriv (regularizedCarlsonZeroDetector X) s =
      2 * (s - 1)⁻¹ + logDeriv (carlsonZeroDetector X) s := by
  let p : ℂ → ℂ := fun z => (z - 1) ^ 2
  have hfactor : regularizedCarlsonZeroDetector X =ᶠ[𝓝 s]
      fun z => p z * carlsonZeroDetector X z := by
    filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1]
      with z hz0 hz1
    exact regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X hz0 hz1
  have hlogDerivEq :
      logDeriv (regularizedCarlsonZeroDetector X) s =
        logDeriv (fun z => p z * carlsonZeroDetector X z) s := by
    unfold logDeriv
    change deriv (regularizedCarlsonZeroDetector X) s /
        regularizedCarlsonZeroDetector X s =
      deriv (fun z => p z * carlsonZeroDetector X z) s /
        (p s * carlsonZeroDetector X s)
    rw [hfactor.deriv_eq, hfactor.eq_of_nhds]
  have hpne : p s ≠ 0 := by
    exact pow_ne_zero 2 (sub_ne_zero.mpr hs1)
  have hpdiff : DifferentiableAt ℂ p s := by
    dsimp [p]
    fun_prop
  have hdetdiff : DifferentiableAt ℂ (carlsonZeroDetector X) s :=
    (analyticAt_carlsonZeroDetector_of_ne_one X hs1).differentiableAt
  rw [hlogDerivEq, logDeriv_mul s hpne hdet hpdiff hdetdiff]
  have hpLog : logDeriv p s = 2 * (s - 1)⁻¹ := by
    dsimp [p]
    rw [logDeriv_fun_pow (n := 2) (by fun_prop)]
    simp [logDeriv_apply]
  rw [hpLog]

/-- Carlson's detector has no zeros on the fixed far-right half-plane. -/
theorem carlsonZeroDetector_ne_zero_of_four_le_re
    {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    carlsonZeroDetector X s ≠ 0 := by
  have herr := norm_mollifiedZetaError_lt_one_of_four_le_re hX hs
  intro hdet
  have hsquare : (1 : ℂ) = mollifiedZetaError X s ^ 2 := by
    exact sub_eq_zero.mp (by simpa [carlsonZeroDetector] using hdet)
  have hnorm := congrArg norm hsquare
  simp only [norm_one, norm_pow] at hnorm
  nlinarith [norm_nonneg (mollifiedZetaError X s)]

/-- On the fixed far-right half-plane Carlson's detector stays in a closed
half-plane strictly to the right of the imaginary axis. -/
theorem fiftySix_div_eightyOne_le_re_carlsonZeroDetector_of_four_le_re
    {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    (56 / 81 : ℝ) ≤ (carlsonZeroDetector X s).re := by
  let f : ℂ := mollifiedZetaError X s
  have herr : ‖f‖ ≤ 5 / 9 := by
    simpa [f] using
      norm_mollifiedZetaError_le_five_ninth_of_four_le_re hX hs
  have hre : (f ^ 2).re ≤ ‖f ^ 2‖ :=
    (le_abs_self (f ^ 2).re).trans (Complex.abs_re_le_norm (f ^ 2))
  rw [norm_pow] at hre
  unfold carlsonZeroDetector
  simp only [Complex.sub_re, Complex.one_re]
  nlinarith [norm_nonneg f]

/-- The pole-free detector is also nonzero on the fixed far-right
half-plane. -/
theorem regularizedCarlsonZeroDetector_ne_zero_of_four_le_re
    {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    regularizedCarlsonZeroDetector X s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  rw [regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X hs0 hs1]
  exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hs1))
    (carlsonZeroDetector_ne_zero_of_four_le_re hX hs)

/-- The pole-free detector is uniformly bounded away from zero on the fixed
far-right half-plane.  This supplies the center lower bound for Jensen disks
anchored on `Re(s) = 4`. -/
theorem one_le_norm_regularizedCarlsonZeroDetector_of_four_le_re
    {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    1 ≤ ‖regularizedCarlsonZeroDetector X s‖ := by
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hsub : 3 ≤ ‖s - 1‖ := by
    have hre : 3 ≤ |(s - 1).re| := by
      simp only [Complex.sub_re, Complex.one_re]
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact hre.trans (Complex.abs_re_le_norm (s - 1))
  have hdetRe :=
    fiftySix_div_eightyOne_le_re_carlsonZeroDetector_of_four_le_re hX hs
  have hdetNorm : (56 / 81 : ℝ) ≤ ‖carlsonZeroDetector X s‖ :=
    hdetRe.trans ((le_abs_self _).trans
      (Complex.abs_re_le_norm (carlsonZeroDetector X s)))
  rw [regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X hs0 hs1,
    norm_mul, norm_pow]
  nlinarith [norm_nonneg (s - 1), norm_nonneg (carlsonZeroDetector X s)]

/-- The regularized detector is not identically zero on any right half-plane.
The witness is chosen sufficiently far along the positive real axis. -/
theorem exists_regularizedCarlsonZeroDetector_ne_zero_re_gt
    (X : ℕ) (hX : 1 ≤ X) (sigma : ℝ) :
    ∃ x : ℝ, sigma < x ∧
      regularizedCarlsonZeroDetector X (x : ℂ) ≠ 0 := by
  have hdet : ∀ᶠ x : ℝ in atTop,
      carlsonZeroDetector X (x : ℂ) ≠ 0 :=
    (tendsto_carlsonZeroDetector_real_atTop X hX).eventually_ne one_ne_zero
  have hxgt : ∀ᶠ x : ℝ in atTop, max sigma 1 < x :=
    eventually_gt_atTop (max sigma 1)
  obtain ⟨x, hdetx, hx⟩ := (hdet.and hxgt).exists
  have hx_sigma : sigma < x :=
    lt_of_le_of_lt (le_max_left sigma 1) hx
  have hx_one : 1 < x :=
    lt_of_le_of_lt (le_max_right sigma 1) hx
  have hx0 : (x : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hx_one))
  have hx1 : (x : ℂ) ≠ 1 := by
    exact_mod_cast (ne_of_gt hx_one)
  refine ⟨x, hx_sigma, ?_⟩
  rw [regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X hx0 hx1]
  exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hx1)) hdetx

/-- The regularized detector has finite analytic order at every point of the
open right half-plane. -/
theorem analyticOrderAt_regularizedCarlsonZeroDetector_ne_top
    (X : ℕ) (hX : 1 ≤ X) {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (regularizedCarlsonZeroDetector X) s ≠ ⊤ := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hanalytic : AnalyticOnNhd ℂ (regularizedCarlsonZeroDetector X) U :=
    analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X
  obtain ⟨x, hx, hne⟩ :=
    exists_regularizedCarlsonZeroDetector_ne_zero_re_gt X hX 0
  have hxU : (x : ℂ) ∈ U := by
    simpa [U] using hx
  have hsU : s ∈ U := by
    simpa [U] using hs
  have hxorder :
      analyticOrderAt (regularizedCarlsonZeroDetector X) (x : ℂ) ≠ ⊤ := by
    rw [(hanalytic (x : ℂ) hxU).analyticOrderAt_eq_zero.mpr hne]
    exact ENat.coe_ne_top 0
  exact hanalytic.analyticOrderAt_ne_top_of_isPreconnected
    (convex_halfSpace_re_gt 0).isPreconnected hxU hsU hxorder

theorem carlsonZeroDetector_eq_zero_of_riemannZeta_eq_zero
    {X : ℕ} {s : ℂ} (hs : riemannZeta s = 0) :
    carlsonZeroDetector X s = 0 := by
  rw [carlsonZeroDetector_eq_zeta_mul_mollifier_factorization, hs]
  ring

/-- Every nontrivial zeta zero occurs in Carlson's detector with at least its
zeta multiplicity.  The extra mollifier factor may increase the multiplicity. -/
theorem analyticOrderNatAt_riemannZeta_le_carlsonZeroDetector
    {X : ℕ} {rho : ℂ} (hX : 1 ≤ X)
    (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    analyticOrderNatAt riemannZeta rho ≤
      analyticOrderNatAt (carlsonZeroDetector X) rho := by
  let g : ℂ → ℂ := fun s =>
    mobiusMollifier X s *
      (2 - riemannZeta s * mobiusMollifier X s)
  have hrho1 : rho ≠ 1 := by
    intro hone
    have hre := congrArg Complex.re hone
    simp at hre
    linarith [hrho.2.2]
  have hzeta : AnalyticAt ℂ riemannZeta rho :=
    ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one rho hrho1
  have hmollifier : AnalyticAt ℂ (mobiusMollifier X) rho :=
    analyticAt_mobiusMollifier X rho
  have hcomplement : AnalyticAt ℂ
      (fun s : ℂ => 2 - riemannZeta s * mobiusMollifier X s) rho :=
    analyticAt_const.sub (hzeta.mul hmollifier)
  have hg : AnalyticAt ℂ g rho := by
    dsimp [g]
    exact hmollifier.mul hcomplement
  have hzeta_order_ne_top : analyticOrderAt riemannZeta rho ≠ ⊤ :=
    ZeroFreeRegion.analyticOrderAt_riemannZeta_ne_top_of_ne_one hrho1
  have hcomplement_ne :
      (2 - riemannZeta rho * mobiusMollifier X rho : ℂ) ≠ 0 := by
    rw [hrho.1]
    norm_num
  have hcomplement_order_zero :
      analyticOrderAt
        (fun s : ℂ => 2 - riemannZeta s * mobiusMollifier X s) rho = 0 :=
    hcomplement.analyticOrderAt_eq_zero.mpr hcomplement_ne
  have hmollifier_order_ne_top :
      analyticOrderAt (mobiusMollifier X) rho ≠ ⊤ :=
    analyticOrderAt_mobiusMollifier_ne_top X hX rho
  have hg_order_ne_top : analyticOrderAt g rho ≠ ⊤ := by
    rw [show analyticOrderAt g rho =
        analyticOrderAt (mobiusMollifier X) rho +
          analyticOrderAt
            (fun s : ℂ => 2 - riemannZeta s * mobiusMollifier X s) rho by
      exact analyticOrderAt_mul hmollifier hcomplement,
      hcomplement_order_zero, add_zero]
    exact hmollifier_order_ne_top
  have hfactor : carlsonZeroDetector X = riemannZeta * g := by
    funext s
    simp only [Pi.mul_apply]
    simpa [g, mul_assoc] using
      carlsonZeroDetector_eq_zeta_mul_mollifier_factorization X s
  rw [hfactor,
    analyticOrderNatAt_mul hzeta hg hzeta_order_ne_top hg_order_ne_top]
  exact Nat.le_add_right _ _

/-- Every nontrivial zeta zero occurs in the pole-free Carlson detector with
at least its zeta multiplicity. -/
theorem analyticOrderNatAt_riemannZeta_le_regularizedCarlsonZeroDetector
    {X : ℕ} {rho : ℂ} (hX : 1 ≤ X)
    (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    analyticOrderNatAt riemannZeta rho ≤
      analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho := by
  let q : ℂ → ℂ := ZeroFreeRegion.riemannZetaPoleUnitAtOne
  let complement : ℂ → ℂ := fun s =>
    2 * (s - 1) - q s * mobiusMollifier X s
  let g : ℂ → ℂ := fun s =>
    (s - 1) * (mobiusMollifier X s * complement s)
  have hrho0 : rho ≠ 0 := by
    intro hzero
    subst rho
    have hpos := hrho.2.1
    norm_num at hpos
  have hrho1 : rho ≠ 1 := by
    intro hone
    have hre := congrArg Complex.re hone
    simp at hre
    linarith [hrho.2.2]
  have hzeta : AnalyticAt ℂ riemannZeta rho :=
    ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one rho hrho1
  have hq : AnalyticAt ℂ q rho := by
    dsimp [q]
    exact ZeroFreeRegion.analyticOnNhd_riemannZetaPoleUnitAtOne_re_gt
      (θ := 0) le_rfl rho hrho.2.1
  have hm : AnalyticAt ℂ (mobiusMollifier X) rho :=
    analyticAt_mobiusMollifier X rho
  have hcomplement : AnalyticAt ℂ complement rho := by
    dsimp [complement]
    exact (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).sub
      (hq.mul hm)
  have hq_rho : q rho = 0 := by
    dsimp [q]
    rw [ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
      hrho0 hrho1, hrho.1, mul_zero]
  have hcomplement_ne : complement rho ≠ 0 := by
    dsimp [complement]
    rw [hq_rho, zero_mul, sub_zero]
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hrho1)
  have hcomplement_order_zero : analyticOrderAt complement rho = 0 :=
    hcomplement.analyticOrderAt_eq_zero.mpr hcomplement_ne
  have hm_order_ne_top : analyticOrderAt (mobiusMollifier X) rho ≠ ⊤ :=
    analyticOrderAt_mobiusMollifier_ne_top X hX rho
  have hm_complement_order_ne_top :
      analyticOrderAt ((mobiusMollifier X) * complement) rho ≠ ⊤ := by
    rw [analyticOrderAt_mul hm hcomplement, hcomplement_order_zero, add_zero]
    exact hm_order_ne_top
  have hsub : AnalyticAt ℂ (fun s : ℂ => s - 1) rho :=
    analyticAt_id.sub analyticAt_const
  have hsub_order_zero :
      analyticOrderAt (fun s : ℂ => s - 1) rho = 0 :=
    hsub.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hrho1)
  have hg : AnalyticAt ℂ g rho := by
    dsimp [g]
    exact hsub.mul (hm.mul hcomplement)
  have hg_order_ne_top : analyticOrderAt g rho ≠ ⊤ := by
    rw [show analyticOrderAt g rho =
        analyticOrderAt (fun s : ℂ => s - 1) rho +
          analyticOrderAt ((mobiusMollifier X) * complement) rho by
      exact analyticOrderAt_mul hsub (hm.mul hcomplement),
      hsub_order_zero, zero_add]
    exact hm_complement_order_ne_top
  have hq_eventually :
      q =ᶠ[𝓝 rho]
        fun s : ℂ => (s - 1) * riemannZeta s := by
    filter_upwards [eventually_ne_nhds hrho0, eventually_ne_nhds hrho1]
      with s hs0 hs1
    exact ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
      hs0 hs1
  have hfactor :
      regularizedCarlsonZeroDetector X =ᶠ[𝓝 rho]
        riemannZeta * g := by
    filter_upwards [hq_eventually] with s hqs
    simp only [Pi.mul_apply]
    change ZeroFreeRegion.riemannZetaPoleUnitAtOne s *
        mobiusMollifier X s *
          (2 * (s - 1) - ZeroFreeRegion.riemannZetaPoleUnitAtOne s *
            mobiusMollifier X s) =
      riemannZeta s *
        ((s - 1) * (mobiusMollifier X s *
          (2 * (s - 1) - ZeroFreeRegion.riemannZetaPoleUnitAtOne s *
            mobiusMollifier X s)))
    rw [show ZeroFreeRegion.riemannZetaPoleUnitAtOne s =
        (s - 1) * riemannZeta s by exact hqs]
    ring
  have hzeta_order_ne_top : analyticOrderAt riemannZeta rho ≠ ⊤ :=
    ZeroFreeRegion.analyticOrderAt_riemannZeta_ne_top_of_ne_one hrho1
  have horder_nat :
      analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho =
        analyticOrderNatAt (riemannZeta * g) rho := by
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr hfactor]
  rw [horder_nat,
    analyticOrderNatAt_mul hzeta hg hzeta_order_ne_top hg_order_ne_top]
  exact Nat.le_add_right _ _

/-- The pointwise logarithmic majorant used on the left edge of Littlewood's
rectangle: `log |h_X|` is controlled by the square entering the mean value
estimate for `f_X`. -/
theorem log_norm_carlsonZeroDetector_le_norm_mollifiedZetaError_sq
    (X : ℕ) (s : ℂ) :
    Real.log ‖carlsonZeroDetector X s‖ ≤
      ‖mollifiedZetaError X s‖ ^ 2 := by
  let f : ℂ := mollifiedZetaError X s
  by_cases hdet : carlsonZeroDetector X s = 0
  · rw [hdet, norm_zero, Real.log_zero]
    exact sq_nonneg ‖mollifiedZetaError X s‖
  · have hnorm_pos : 0 < ‖carlsonZeroDetector X s‖ :=
      norm_pos_iff.mpr hdet
    have hnorm_le : ‖carlsonZeroDetector X s‖ ≤ 1 + ‖f‖ ^ 2 := by
      change ‖1 - f ^ 2‖ ≤ 1 + ‖f‖ ^ 2
      calc
        ‖1 - f ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖f ^ 2‖ := norm_sub_le _ _
        _ = 1 + ‖f‖ ^ 2 := by simp
    calc
      Real.log ‖carlsonZeroDetector X s‖ ≤
          Real.log (1 + ‖f‖ ^ 2) :=
        Real.log_le_log hnorm_pos hnorm_le
      _ ≤ ‖f‖ ^ 2 := by
        simpa using Real.log_le_sub_one_of_pos
          (show 0 < 1 + ‖f‖ ^ 2 by positivity)
      _ = ‖mollifiedZetaError X s‖ ^ 2 := rfl

/-- Reverse-triangle lower bound for Carlson's detector. -/
theorem one_sub_norm_mollifiedZetaError_sq_le_norm_carlsonZeroDetector
    (X : ℕ) (s : ℂ) :
    1 - ‖mollifiedZetaError X s‖ ^ 2 ≤ ‖carlsonZeroDetector X s‖ := by
  unfold carlsonZeroDetector
  calc
    1 - ‖mollifiedZetaError X s‖ ^ 2 =
        ‖(1 : ℂ)‖ - ‖mollifiedZetaError X s ^ 2‖ := by simp
    _ ≤ ‖(1 : ℂ) - mollifiedZetaError X s ^ 2‖ :=
      norm_sub_norm_le _ _

/-- If the mollified error is uniformly bounded by a radius below one, then
Carlson's detector is uniformly separated from zero. -/
theorem one_sub_sq_le_norm_carlsonZeroDetector_of_norm_error_le
    {X : ℕ} {s : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (herr : ‖mollifiedZetaError X s‖ ≤ r) :
    1 - r ^ 2 ≤ ‖carlsonZeroDetector X s‖ := by
  calc
    1 - r ^ 2 ≤ 1 - ‖mollifiedZetaError X s‖ ^ 2 := by
      nlinarith [norm_nonneg (mollifiedZetaError X s)]
    _ ≤ ‖carlsonZeroDetector X s‖ :=
      one_sub_norm_mollifiedZetaError_sq_le_norm_carlsonZeroDetector X s

/-- Logarithmic lower bound for the regularized detector under a right-edge
smallness hypothesis for the mollified error. -/
theorem two_log_norm_sub_one_add_log_one_sub_sq_le_log_norm_regularized
    {X : ℕ} {s : ℂ} {r : ℝ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hr : 0 ≤ r) (hr1 : r < 1)
    (herr : ‖mollifiedZetaError X s‖ ≤ r) :
    2 * Real.log ‖s - 1‖ + Real.log (1 - r ^ 2) ≤
      Real.log ‖regularizedCarlsonZeroDetector X s‖ := by
  have hbasePos : 0 < 1 - r ^ 2 := by nlinarith
  have hdetLower : 1 - r ^ 2 ≤ ‖carlsonZeroDetector X s‖ :=
    one_sub_sq_le_norm_carlsonZeroDetector_of_norm_error_le hr herr
  have hdetPos : 0 < ‖carlsonZeroDetector X s‖ :=
    hbasePos.trans_le hdetLower
  have hdet : carlsonZeroDetector X s ≠ 0 := norm_pos_iff.mp hdetPos
  rw [regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X hs0 hs1,
    norm_mul, norm_pow,
    Real.log_mul
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs1)))
      (norm_ne_zero_iff.mpr hdet),
    Real.log_pow]
  have hlog := Real.log_le_log hbasePos hdetLower
  norm_num
  linarith

/-- Numerical logarithmic lower bound for the regularized detector on the
fixed far-right half-plane. -/
theorem log_fiftySix_div_eightyOne_le_log_norm_regularized_of_four_le_re
    {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    2 * Real.log ‖s - 1‖ + Real.log (56 / 81 : ℝ) ≤
      Real.log ‖regularizedCarlsonZeroDetector X s‖ := by
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have herr := norm_mollifiedZetaError_le_five_ninth_of_four_le_re hX hs
  have h := two_log_norm_sub_one_add_log_one_sub_sq_le_log_norm_regularized
    hs0 hs1 (show (0 : ℝ) ≤ 5 / 9 by norm_num)
      (show (5 / 9 : ℝ) < 1 by norm_num) herr
  norm_num at h ⊢
  exact h

/-- Away from the removable points, the logarithmic size of the pole-free
detector differs from the original Carlson detector only by the explicit
geometric factor `(s - 1)^2`. -/
theorem log_norm_regularizedCarlsonZeroDetector_le_two_log_norm_sub_one_add_error_sq
    {X : ℕ} {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hdet : carlsonZeroDetector X s ≠ 0) :
    Real.log ‖regularizedCarlsonZeroDetector X s‖ ≤
      2 * Real.log ‖s - 1‖ + ‖mollifiedZetaError X s‖ ^ 2 := by
  rw [regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X hs0 hs1,
    norm_mul, norm_pow,
    Real.log_mul
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs1)))
      (norm_ne_zero_iff.mpr hdet),
    Real.log_pow]
  simpa using add_le_add_right
    (log_norm_carlsonZeroDetector_le_norm_mollifiedZetaError_sq X s)
    (2 * Real.log ‖s - 1‖)

/-- The pole-free detector is continuous on every vertical line in the right
half-plane. -/
theorem continuous_regularizedCarlsonZeroDetector_verticalLine
    (X : ℕ) {sigma : ℝ} (hsigma0 : 0 < sigma) :
    Continuous (fun t : ℝ =>
      regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have han : AnalyticAt ℂ (regularizedCarlsonZeroDetector X)
      ((sigma : ℂ) + Complex.I * (t : ℂ)) :=
    analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X _ (by simpa using hsigma0)
  have hmap : ContinuousAt
      (fun u : ℝ => (sigma : ℂ) + Complex.I * (u : ℂ)) t := by
    fun_prop
  simpa [Function.comp_def] using han.continuousAt.comp_of_eq hmap rfl

/-- On a zero-free vertical segment, the logarithmic norm of the regularized
Carlson detector is interval integrable. -/
theorem intervalIntegrable_log_norm_regularizedCarlsonZeroDetector
    {X : ℕ} {sigma a b : ℝ} (hsigma0 : 0 < sigma)
    (hboundary : ∀ t ∈ Set.uIcc a b,
      regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t) ≠ 0) :
    IntervalIntegrable
      (fun t : ℝ => Real.log ‖regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t)‖)
      MeasureTheory.volume a b := by
  have hdetector :=
    continuous_regularizedCarlsonZeroDetector_verticalLine X hsigma0
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have hlog : ContinuousAt Real.log
      ‖regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * (t : ℂ))‖ :=
    Real.continuousAt_log (norm_ne_zero_iff.mpr (hboundary t ht))
  have hlogNorm : ContinuousAt (fun z : ℂ => Real.log ‖z‖)
      (regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * (t : ℂ))) :=
    hlog.comp' continuous_norm.continuousAt
  exact (ContinuousAt.comp'
    (f := fun u : ℝ => regularizedCarlsonZeroDetector X
      ((sigma : ℂ) + Complex.I * u))
    hlogNorm hdetector.continuousAt).continuousWithinAt

/-- On a zero-free left boundary, the pole-free detector's logarithmic
integral is controlled by the explicit regularization factor and the same
mollified-zeta mean square used for Carlson's original detector. -/
theorem integral_log_norm_regularizedCarlsonZeroDetector_le_geometric_add_meanSquare
    {X : ℕ} {sigma a b : ℝ} (hab : a ≤ b)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma ≠ 1)
    (hboundary : ∀ t ∈ Set.Icc a b,
      carlsonZeroDetector X ((sigma : ℂ) + Complex.I * t) ≠ 0) :
    (∫ t in a..b,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖) ≤
      2 * (∫ t in a..b,
        Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖) +
      ∫ t in a..b,
        ‖mollifiedZetaError X
          ((sigma : ℂ) + Complex.I * t)‖ ^ 2 := by
  have hregCont :=
    continuous_regularizedCarlsonZeroDetector_verticalLine X hsigma0
  have hzetaCont : Continuous (fun t : ℝ =>
      riemannZeta ((sigma : ℂ) + Complex.I * t)) := by
    simpa [carlsonZetaRemainder] using
      (continuous_carlsonZetaRemainder_verticalLine 0 sigma hsigma1)
  have herrorCont : Continuous (fun t : ℝ =>
      mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)) := by
    unfold mollifiedZetaError
    exact (hzetaCont.mul
      (continuous_mobiusMollifier_verticalLine X sigma)).sub continuous_const
  have hpointNe {t : ℝ} :
      (sigma : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      Complex.zero_re] at hre
    linarith
  have hpointOne {t : ℝ} :
      (sigma : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
    intro hone
    have hre := congrArg Complex.re hone
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      Complex.one_re] at hre
    apply hsigma1
    linarith
  have hregNe {t : ℝ} (ht : t ∈ Set.Icc a b) :
      regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
    rw [regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X
      hpointNe hpointOne]
    exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hpointOne))
      (hboundary t ht)
  have hlogRegContOn : ContinuousOn (fun t : ℝ =>
      Real.log ‖regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t)‖) (Set.Icc a b) := by
    intro t ht
    have hlog : ContinuousAt Real.log
        ‖regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * (t : ℂ))‖ :=
      Real.continuousAt_log (norm_ne_zero_iff.mpr (hregNe ht))
    have hlogNorm : ContinuousAt (fun z : ℂ => Real.log ‖z‖)
        (regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * (t : ℂ))) :=
      hlog.comp' continuous_norm.continuousAt
    exact (ContinuousAt.comp'
      (f := fun u : ℝ => regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * u))
      hlogNorm hregCont.continuousAt).continuousWithinAt
  have hgeomCont : Continuous (fun t : ℝ =>
      Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hlog : ContinuousAt Real.log
        ‖(sigma : ℂ) + Complex.I * (t : ℂ) - 1‖ :=
      Real.continuousAt_log
        (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpointOne))
    have hlogNorm : ContinuousAt (fun z : ℂ => Real.log ‖z‖)
        ((sigma : ℂ) + Complex.I * (t : ℂ) - 1) :=
      hlog.comp' continuous_norm.continuousAt
    have hmap : ContinuousAt
        (fun u : ℝ => (sigma : ℂ) + Complex.I * (u : ℂ) - 1) t := by
      fun_prop
    exact ContinuousAt.comp'
      (f := fun u : ℝ => (sigma : ℂ) + Complex.I * (u : ℂ) - 1)
      hlogNorm hmap
  have hleftInt : IntervalIntegrable (fun t : ℝ =>
      Real.log ‖regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t)‖)
      MeasureTheory.volume a b :=
    hlogRegContOn.intervalIntegrable_of_Icc hab
  have hgeomInt : IntervalIntegrable (fun t : ℝ =>
      2 * Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖)
      MeasureTheory.volume a b :=
    (continuous_const.mul hgeomCont).intervalIntegrable a b
  have herrorInt : IntervalIntegrable (fun t : ℝ =>
      ‖mollifiedZetaError X
        ((sigma : ℂ) + Complex.I * t)‖ ^ 2)
      MeasureTheory.volume a b :=
    (herrorCont.norm.pow 2).intervalIntegrable a b
  calc
    (∫ t in a..b,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖) ≤
        ∫ t in a..b,
          2 * Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖ +
            ‖mollifiedZetaError X
              ((sigma : ℂ) + Complex.I * t)‖ ^ 2 := by
      exact intervalIntegral.integral_mono_on hab hleftInt
        (hgeomInt.add herrorInt) fun t ht =>
          log_norm_regularizedCarlsonZeroDetector_le_two_log_norm_sub_one_add_error_sq
            hpointNe hpointOne (hboundary t ht)
    _ = _ := by
      rw [intervalIntegral.integral_add hgeomInt herrorInt,
        intervalIntegral.integral_const_mul]

/-- Away from the zeta pole, the mollified zeta error is continuous on a
vertical line. -/
theorem continuous_mollifiedZetaError_verticalLine
    (X : ℕ) (sigma : ℝ) (hsigma1 : sigma ≠ 1) :
    Continuous (fun t : ℝ =>
      mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)) := by
  have hzeta : Continuous (fun t : ℝ =>
      riemannZeta ((sigma : ℂ) + Complex.I * t)) := by
    simpa [carlsonZetaRemainder] using
      (continuous_carlsonZetaRemainder_verticalLine 0 sigma hsigma1)
  have hmollifier := continuous_mobiusMollifier_verticalLine X sigma
  unfold mollifiedZetaError
  exact (hzeta.mul hmollifier).sub continuous_const

theorem continuous_carlsonZeroDetector_verticalLine
    (X : ℕ) (sigma : ℝ) (hsigma1 : sigma ≠ 1) :
    Continuous (fun t : ℝ =>
      carlsonZeroDetector X ((sigma : ℂ) + Complex.I * t)) := by
  unfold carlsonZeroDetector
  exact continuous_const.sub
    ((continuous_mollifiedZetaError_verticalLine X sigma hsigma1).pow 2)

/-- On a zero-free vertical boundary, Littlewood's logarithmic left-edge
integral is bounded by the mollified-zeta second moment. -/
theorem integral_log_norm_carlsonZeroDetector_le_meanSquare
    {X : ℕ} {sigma a b : ℝ} (hab : a ≤ b)
    (hsigma1 : sigma ≠ 1)
    (hboundary : ∀ t ∈ Set.Icc a b,
      carlsonZeroDetector X ((sigma : ℂ) + Complex.I * t) ≠ 0) :
    ∫ t in a..b,
        Real.log ‖carlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖ ≤
      ∫ t in a..b,
        ‖mollifiedZetaError X
          ((sigma : ℂ) + Complex.I * t)‖ ^ 2 := by
  have hdetCont := continuous_carlsonZeroDetector_verticalLine X sigma hsigma1
  have herrCont := continuous_mollifiedZetaError_verticalLine X sigma hsigma1
  have hlogContOn : ContinuousOn (fun t : ℝ =>
      Real.log ‖carlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t)‖) (Set.Icc a b) := by
    intro t ht
    have hlogCont : ContinuousAt Real.log
        ‖carlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖ :=
      Real.continuousAt_log (norm_ne_zero_iff.mpr (hboundary t ht))
    have hlogNormCont : ContinuousAt (fun z : ℂ => Real.log ‖z‖)
        (carlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)) :=
      hlogCont.comp' continuous_norm.continuousAt
    exact (ContinuousAt.comp'
      (f := fun u : ℝ =>
        carlsonZeroDetector X ((sigma : ℂ) + Complex.I * u))
      hlogNormCont hdetCont.continuousAt).continuousWithinAt
  have hlogInt : IntervalIntegrable (fun t : ℝ =>
      Real.log ‖carlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t)‖)
      MeasureTheory.volume a b :=
    hlogContOn.intervalIntegrable_of_Icc hab
  have hsquareInt : IntervalIntegrable (fun t : ℝ =>
      ‖mollifiedZetaError X
        ((sigma : ℂ) + Complex.I * t)‖ ^ 2)
      MeasureTheory.volume a b :=
    (herrCont.norm.pow 2).intervalIntegrable a b
  exact intervalIntegral.integral_mono_on hab hlogInt hsquareInt
    (fun t _ =>
      log_norm_carlsonZeroDetector_le_norm_mollifiedZetaError_sq
        X ((sigma : ℂ) + Complex.I * t))

/-- The verified mollified-zeta mean square gives the Carlson/Littlewood
left-edge logarithmic bound with the same endpoint expression. -/
theorem exists_integral_log_norm_carlsonZeroDetector_le_endpoint :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (sigma a b x : ℝ),
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b, |t| ≤ x / 2 ∧ x ≤ 2 * |t|) →
      (∀ t ∈ Set.Icc a b,
        carlsonZeroDetector X ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in a..b,
            Real.log ‖carlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          2 * (((b - a) + 4 * Real.pi) *
            (2 * ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
                (1 - 2 * sigma) *
              ((((Nat.floor x) * X : ℕ) : ℝ) *
                (1 + Real.log (Nat.floor x * X)) ^ 3))) +
          2 * ((C * x ^ (-sigma)) ^ 2 *
            (((b - a) + 4 * Real.pi) *
              (2 * (1 +
                ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                  (2 - 2 * sigma))))) := by
  obtain ⟨C, hC, hmean⟩ :=
    exists_mollifiedZetaError_meanSquare_le_endpoint
  refine ⟨C, hC, ?_⟩
  intro X sigma a b x hX hab hsigma hsigma1 hx hheight hboundary
  exact (integral_log_norm_carlsonZeroDetector_le_meanSquare
    hab (ne_of_lt hsigma1) hboundary).trans
      (hmean X sigma a b x hX hab hsigma hsigma1 hx hheight)

/-- The elementary regularization factor contributes at most interval length
times `log (1 + v)` on a positive-height interval. -/
theorem integral_log_norm_vertical_sub_one_le_length_mul_log
    {sigma u v : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hu : 1 ≤ u) (huv : u ≤ v) :
    (∫ t in u..v,
      Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖) ≤
        (v - u) * Real.log (1 + v) := by
  have hpointOne (t : ℝ) :
      (sigma : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
    intro hone
    have hre := congrArg Complex.re hone
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      Complex.one_re] at hre
    linarith
  have hcont : Continuous (fun t : ℝ =>
      Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hlog : ContinuousAt Real.log
        ‖(sigma : ℂ) + Complex.I * (t : ℂ) - 1‖ :=
      Real.continuousAt_log
        (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hpointOne t)))
    have hlogNorm : ContinuousAt (fun z : ℂ => Real.log ‖z‖)
        ((sigma : ℂ) + Complex.I * (t : ℂ) - 1) :=
      hlog.comp' continuous_norm.continuousAt
    have hmap : ContinuousAt
        (fun r : ℝ => (sigma : ℂ) + Complex.I * (r : ℂ) - 1) t := by
      fun_prop
    exact hlogNorm.comp_of_eq hmap rfl
  have hleftInt : IntervalIntegrable (fun t : ℝ =>
      Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖)
      MeasureTheory.volume u v :=
    hcont.intervalIntegrable u v
  have hrightInt : IntervalIntegrable
      (fun _t : ℝ => Real.log (1 + v)) MeasureTheory.volume u v :=
    continuous_const.intervalIntegrable u v
  have hpoint : ∀ t ∈ Set.Icc u v,
      Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖ ≤
        Real.log (1 + v) := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith [hu, ht.1]
    have hnorm : ‖(sigma : ℂ) + Complex.I * t - 1‖ ≤ 1 + v := by
      calc
        ‖(sigma : ℂ) + Complex.I * t - 1‖ =
            ‖((sigma : ℂ) - 1) + Complex.I * t‖ := by
          congr 1
          ring
        _ ≤ ‖(sigma : ℂ) - 1‖ + ‖Complex.I * (t : ℂ)‖ :=
          norm_add_le _ _
        _ = |sigma - 1| + |t| := by
          have hnormReal : ‖(sigma : ℂ) - 1‖ = |sigma - 1| := by
            rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
            simpa using (RCLike.norm_ofReal (K := ℂ) (sigma - 1))
          rw [hnormReal]
          simp
        _ = (1 - sigma) + t := by
          rw [abs_of_nonpos (by linarith), abs_of_nonneg ht0]
          ring
        _ ≤ 1 + v := by linarith [ht.2, hsigma0]
    have hnormPos : 0 < ‖(sigma : ℂ) + Complex.I * t - 1‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (hpointOne t))
    exact Real.log_le_log hnormPos hnorm
  calc
    (∫ t in u..v,
        Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖) ≤
        ∫ _t in u..v, Real.log (1 + v) :=
      intervalIntegral.integral_mono_on huv hleftInt hrightInt hpoint
    _ = (v - u) * Real.log (1 + v) := by simp

/-- The endpoint expression controlling the logarithmic norm of the
regularized Carlson detector on a height-comparable interval. -/
noncomputable def regularizedCarlsonLogNormEndpoint
    (A kappa : ℝ) (X : ℕ) (sigma a b x : ℝ) : ℝ :=
  2 * (∫ t in a..b,
    Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖) +
  2 * (((b - a) + 4 * Real.pi) *
    (2 * ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
        (1 - 2 * sigma) *
      ((((Nat.floor x) * X : ℕ) : ℝ) *
        (1 + Real.log (Nat.floor x * X)) ^ 3))) +
  2 * (((((A + kappa) * x ^ (-sigma)) ^ 2)) *
    (((b - a) + 4 * Real.pi) *
      (2 * (1 +
        ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
          (2 - 2 * sigma)))))

/-- Integral-free majorant for `regularizedCarlsonLogNormEndpoint`. -/
noncomputable def regularizedCarlsonLogNormEndpointExplicit
    (A kappa : ℝ) (X : ℕ) (sigma a b x : ℝ) : ℝ :=
  2 * ((b - a) * Real.log (1 + b)) +
  2 * (((b - a) + 4 * Real.pi) *
    (2 * ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
        (1 - 2 * sigma) *
      ((((Nat.floor x) * X : ℕ) : ℝ) *
        (1 + Real.log (Nat.floor x * X)) ^ 3))) +
  2 * (((((A + kappa) * x ^ (-sigma)) ^ 2)) *
    (((b - a) + 4 * Real.pi) *
      (2 * (1 +
        ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
          (2 - 2 * sigma)))))

/-- The geometric logarithmic integral can be eliminated from the Carlson
endpoint on positive-height intervals. -/
theorem regularizedCarlsonLogNormEndpoint_le_explicit
    {A kappa sigma a b x : ℝ} {X : ℕ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    regularizedCarlsonLogNormEndpoint A kappa X sigma a b x ≤
      regularizedCarlsonLogNormEndpointExplicit A kappa X sigma a b x := by
  have hgeom := integral_log_norm_vertical_sub_one_le_length_mul_log
    hsigma0 hsigma1 ha hab
  unfold regularizedCarlsonLogNormEndpoint
    regularizedCarlsonLogNormEndpointExplicit
  linarith

/-- The comparable-height Carlson mean-square estimate controls the logarithmic
norm of the pole-free regularized detector on genuine intervals. -/
theorem exists_integral_log_norm_regularizedCarlsonZeroDetector_le_endpoint_of_comparable :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (kappa : ℝ) (X : ℕ)
        (sigma a b x : ℝ),
      0 < kappa →
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b,
        |t| ≤ x / 2 ∧ x ≤ kappa * |t|) →
      (∀ t ∈ Set.Icc a b,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in a..b,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          2 * (∫ t in a..b,
            Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖) +
          2 * (((b - a) + 4 * Real.pi) *
            (2 * ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
                (1 - 2 * sigma) *
              ((((Nat.floor x) * X : ℕ) : ℝ) *
                (1 + Real.log (Nat.floor x * X)) ^ 3))) +
          2 * (((((A + kappa) * x ^ (-sigma)) ^ 2)) *
            (((b - a) + 4 * Real.pi) *
              (2 * (1 +
                ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                  (2 - 2 * sigma))))) := by
  obtain ⟨A, hA, hmean⟩ :=
    exists_mollifiedZetaError_meanSquare_le_endpoint_of_comparable
  refine ⟨A, hA, ?_⟩
  intro kappa X sigma a b x hkappa hX hab hsigma hsigma1 hx hheight hboundary
  have hdetBoundary : ∀ t ∈ Set.Icc a b,
      carlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht hdetZero
    let s : ℂ := (sigma : ℂ) + Complex.I * t
    have hs0 : s ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      dsimp [s] at hre
      norm_num at hre
      linarith
    have hs1 : s ≠ 1 := by
      intro hone
      have hre := congrArg Complex.re hone
      dsimp [s] at hre
      norm_num at hre
      linarith
    change carlsonZeroDetector X s = 0 at hdetZero
    apply hboundary t ht
    rw [show regularizedCarlsonZeroDetector X s =
        (s - 1) ^ 2 * carlsonZeroDetector X s from
      regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X hs0 hs1]
    simp [hdetZero]
  exact
    (integral_log_norm_regularizedCarlsonZeroDetector_le_geometric_add_meanSquare
      hab (by linarith) (ne_of_lt hsigma1) hdetBoundary).trans
      (by
        simpa [add_assoc] using
          (add_le_add_right
            (hmean kappa X sigma a b x hkappa hX hab hsigma hsigma1 hx hheight)
            (2 * (∫ t in a..b,
              Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖))))

/-- The original exact-height `kappa = 2` specialization. -/
theorem exists_integral_log_norm_regularizedCarlsonZeroDetector_le_endpoint :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (sigma a b x : ℝ),
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b, |t| ≤ x / 2 ∧ x ≤ 2 * |t|) →
      (∀ t ∈ Set.Icc a b,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in a..b,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          2 * (∫ t in a..b,
            Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖) +
          2 * (((b - a) + 4 * Real.pi) *
            (2 * ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
                (1 - 2 * sigma) *
              ((((Nat.floor x) * X : ℕ) : ℝ) *
                (1 + Real.log (Nat.floor x * X)) ^ 3))) +
          2 * ((C * x ^ (-sigma)) ^ 2 *
            (((b - a) + 4 * Real.pi) *
              (2 * (1 +
                ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                  (2 - 2 * sigma))))) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_endpoint_of_comparable
  refine ⟨A + 2, by positivity, ?_⟩
  intro X sigma a b x hX hab hsigma hsigma1 hx hheight hboundary
  exact hbound 2 X sigma a b x (by norm_num) hX hab hsigma hsigma1 hx
    hheight hboundary

/-- Every doubling interval `[u, v]` with `v ≤ 2u` is covered by the fixed
choices `x = 4u` and `kappa = 4`. -/
theorem exists_integral_log_norm_regularizedCarlsonZeroDetector_le_doublingInterval :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma u v : ℝ),
      1 ≤ X → 1 ≤ u → u ≤ v → v ≤ 2 * u →
      1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc u v,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in u..v,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma u v (4 * u) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_endpoint_of_comparable
  refine ⟨A, hA, ?_⟩
  intro X sigma u v hX hu huv hvu hsigma hsigma1 hboundary
  have hheight : ∀ t ∈ Set.Icc u v,
      |t| ≤ (4 * u) / 2 ∧ 4 * u ≤ 4 * |t| := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    rw [abs_of_nonneg ht0]
    constructor <;> nlinarith [ht.1, ht.2, hvu]
  have h := hbound 4 X sigma u v (4 * u)
    (by norm_num) hX huv hsigma hsigma1 (by linarith)
    hheight hboundary
  simpa [regularizedCarlsonLogNormEndpoint] using h

/-- The exact dyadic interval `[u, 2u]` specialization. -/
theorem exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadic :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma u : ℝ),
      1 ≤ X → 1 ≤ u → 1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc u (2 * u),
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in u..(2 * u),
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma u (2 * u) (4 * u) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_doublingInterval
  refine ⟨A, hA, ?_⟩
  intro X sigma u hX hu hsigma hsigma1 hboundary
  exact hbound X sigma u (2 * u) hX hu (by linarith) le_rfl
    hsigma hsigma1 hboundary

/-- Integral-free specialization of the dyadic Carlson log-norm estimate. -/
theorem exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicExplicit :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma u : ℝ),
      1 ≤ X → 1 ≤ u → 1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc u (2 * u),
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in u..(2 * u),
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          regularizedCarlsonLogNormEndpointExplicit
            A 4 X sigma u (2 * u) (4 * u) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadic
  refine ⟨A, hA, ?_⟩
  intro X sigma u hX hu hsigma hsigma1 hboundary
  exact (hbound X sigma u hX hu hsigma hsigma1 hboundary).trans
    (regularizedCarlsonLogNormEndpoint_le_explicit
      (by linarith) hsigma1 hu (by linarith))

private theorem integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicSum
    {A : ℝ}
    (hdyadic : ∀ (X : ℕ) (sigma u : ℝ),
      1 ≤ X → 1 ≤ u → 1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc u (2 * u),
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in u..(2 * u),
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma u (2 * u) (4 * u))
    (X : ℕ) (sigma : ℝ) (n : ℕ)
    (hX : 1 ≤ X) (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1)
    (hboundary : ∀ t ∈ Set.Icc 1 ((2 : ℝ) ^ n),
      regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t) ≠ 0) :
    (∫ t in 1..((2 : ℝ) ^ n),
        Real.log ‖regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖) ≤
      ∑ k ∈ Finset.range n,
        regularizedCarlsonLogNormEndpoint
          A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
            (4 * (2 : ℝ) ^ k) := by
  let f : ℝ → ℝ := fun t =>
    Real.log ‖regularizedCarlsonZeroDetector X
      ((sigma : ℂ) + Complex.I * t)‖
  have hpowOne (k : ℕ) : 1 ≤ (2 : ℝ) ^ k :=
    one_le_pow₀ (by norm_num)
  have hpowStep (k : ℕ) :
      (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
  have hpowTop {k : ℕ} (hk : k < n) :
      (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) (Nat.succ_le_iff.mpr hk)
  have hsegmentBoundary {k : ℕ} (hk : k < n) :
      ∀ t ∈ Set.uIcc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)),
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le (hpowStep k)] at ht
    apply hboundary t
    exact ⟨(hpowOne k).trans ht.1, ht.2.trans (hpowTop hk)⟩
  have hint : ∀ k < n,
      IntervalIntegrable f MeasureTheory.volume
        ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)) := by
    intro k hk
    exact intervalIntegrable_log_norm_regularizedCarlsonZeroDetector
      (by linarith) (hsegmentBoundary hk)
  have hpiece {k : ℕ} (hk : k < n) :
      (∫ t in ((2 : ℝ) ^ k)..((2 : ℝ) ^ (k + 1)), f t) ≤
        regularizedCarlsonLogNormEndpoint
          A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
            (4 * (2 : ℝ) ^ k) := by
    have hboundaryDyadic : ∀ t ∈ Set.Icc ((2 : ℝ) ^ k)
        (2 * (2 : ℝ) ^ k),
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0 := by
      intro t ht
      apply hboundary t
      constructor
      · exact (hpowOne k).trans ht.1
      · have ht' : t ≤ (2 : ℝ) ^ (k + 1) := by
          simpa [pow_succ, mul_comm] using ht.2
        exact ht'.trans (hpowTop hk)
    have h := hdyadic X sigma ((2 : ℝ) ^ k) hX (hpowOne k)
      hsigma hsigma1 hboundaryDyadic
    simpa [f, pow_succ, mul_comm] using h
  have hsum :
      (∑ k ∈ Finset.range n,
          ∫ t in ((2 : ℝ) ^ k)..((2 : ℝ) ^ (k + 1)), f t) ≤
        ∑ k ∈ Finset.range n,
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
              (4 * (2 : ℝ) ^ k) := by
    exact Finset.sum_le_sum fun k hk => hpiece (Finset.mem_range.mp hk)
  calc
    (∫ t in 1..((2 : ℝ) ^ n), f t) =
        ∑ k ∈ Finset.range n,
          ∫ t in ((2 : ℝ) ^ k)..((2 : ℝ) ^ (k + 1)), f t := by
      simpa using
        (intervalIntegral.sum_integral_adjacent_intervals
          (a := fun k : ℕ => (2 : ℝ) ^ k) hint).symm
    _ ≤ ∑ k ∈ Finset.range n,
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
              (4 * (2 : ℝ) ^ k) := hsum

/-- Summing the dyadic estimates controls the logarithmic norm on the whole
finite height interval `[1, 2^n]`. -/
theorem exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicSum :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma : ℝ) (n : ℕ),
      1 ≤ X → 1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc 1 ((2 : ℝ) ^ n),
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in 1..((2 : ℝ) ^ n),
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          ∑ k ∈ Finset.range n,
            regularizedCarlsonLogNormEndpoint
              A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
                (4 * (2 : ℝ) ^ k) := by
  obtain ⟨A, hA, hdyadic⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadic
  exact ⟨A, hA, fun X sigma n hX hsigma hsigma1 hboundary =>
    integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicSum
      hdyadic X sigma n hX hsigma hsigma1 hboundary⟩

/-- The full dyadic log-norm sum has no remaining geometric logarithmic
integrals. -/
theorem exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicSumExplicit :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma : ℝ) (n : ℕ),
      1 ≤ X → 1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc 1 ((2 : ℝ) ^ n),
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in 1..((2 : ℝ) ^ n),
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          ∑ k ∈ Finset.range n,
            regularizedCarlsonLogNormEndpointExplicit
              A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
                (4 * (2 : ℝ) ^ k) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicSum
  refine ⟨A, hA, ?_⟩
  intro X sigma n hX hsigma hsigma1 hboundary
  refine (hbound X sigma n hX hsigma hsigma1 hboundary).trans ?_
  apply Finset.sum_le_sum
  intro k hk
  exact regularizedCarlsonLogNormEndpoint_le_explicit
    (by linarith) hsigma1 (one_le_pow₀ (by norm_num))
      (pow_le_pow_right₀ (by norm_num) (Nat.le_succ k))

/-- A dyadic cover with one final partial interval controls every upper
endpoint between two consecutive powers of two. -/
theorem exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicCover :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma v : ℝ) (n : ℕ),
      1 ≤ X → 1 / 2 < sigma → sigma < 1 →
      (2 : ℝ) ^ n ≤ v → v ≤ (2 : ℝ) ^ (n + 1) →
      (∀ t ∈ Set.Icc 1 v,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in 1..v,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          (∑ k ∈ Finset.range n,
            regularizedCarlsonLogNormEndpoint
              A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
                (4 * (2 : ℝ) ^ k)) +
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma ((2 : ℝ) ^ n) v (4 * (2 : ℝ) ^ n) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_doublingInterval
  have hdyadic : ∀ (X : ℕ) (sigma u : ℝ),
      1 ≤ X → 1 ≤ u → 1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc u (2 * u),
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in u..(2 * u),
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma u (2 * u) (4 * u) := by
    intro X sigma u hX hu hsigma hsigma1 hboundary
    exact hbound X sigma u (2 * u) hX hu (by linarith) le_rfl
      hsigma hsigma1 hboundary
  refine ⟨A, hA, ?_⟩
  intro X sigma v n hX hsigma hsigma1 hnv hvn hboundary
  let f : ℝ → ℝ := fun t =>
    Real.log ‖regularizedCarlsonZeroDetector X
      ((sigma : ℂ) + Complex.I * t)‖
  have hpowOne : 1 ≤ (2 : ℝ) ^ n :=
    one_le_pow₀ (by norm_num)
  have hboundaryLeft : ∀ t ∈ Set.Icc 1 ((2 : ℝ) ^ n),
      regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht
    exact hboundary t ⟨ht.1, ht.2.trans hnv⟩
  have hboundaryRight : ∀ t ∈ Set.Icc ((2 : ℝ) ^ n) v,
      regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht
    exact hboundary t ⟨hpowOne.trans ht.1, ht.2⟩
  have hfull :=
    integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicSum
      hdyadic X sigma n hX hsigma hsigma1 hboundaryLeft
  have hvDouble : v ≤ 2 * (2 : ℝ) ^ n := by
    simpa [pow_succ, mul_comm] using hvn
  have hpartial := hbound X sigma ((2 : ℝ) ^ n) v
    hX hpowOne hnv hvDouble hsigma hsigma1 hboundaryRight
  have hleftInt : IntervalIntegrable f MeasureTheory.volume
      1 ((2 : ℝ) ^ n) := by
    apply intervalIntegrable_log_norm_regularizedCarlsonZeroDetector
      (by linarith)
    intro t ht
    rw [Set.uIcc_of_le hpowOne] at ht
    exact hboundaryLeft t ht
  have hrightInt : IntervalIntegrable f MeasureTheory.volume
      ((2 : ℝ) ^ n) v := by
    apply intervalIntegrable_log_norm_regularizedCarlsonZeroDetector
      (by linarith)
    intro t ht
    rw [Set.uIcc_of_le hnv] at ht
    exact hboundaryRight t ht
  calc
    (∫ t in 1..v, f t) =
        (∫ t in 1..((2 : ℝ) ^ n), f t) +
          ∫ t in ((2 : ℝ) ^ n)..v, f t := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        hleftInt hrightInt).symm
    _ ≤ (∑ k ∈ Finset.range n,
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
              (4 * (2 : ℝ) ^ k)) +
        regularizedCarlsonLogNormEndpoint
          A 4 X sigma ((2 : ℝ) ^ n) v (4 * (2 : ℝ) ^ n) :=
      add_le_add hfull hpartial

/-- The arbitrary-height dyadic cover with every high-height endpoint made
explicit. -/
theorem exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicCoverExplicit :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma v : ℝ) (n : ℕ),
      1 ≤ X → 1 / 2 < sigma → sigma < 1 →
      (2 : ℝ) ^ n ≤ v → v ≤ (2 : ℝ) ^ (n + 1) →
      (∀ t ∈ Set.Icc 1 v,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in 1..v,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          (∑ k ∈ Finset.range n,
            regularizedCarlsonLogNormEndpointExplicit
              A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
                (4 * (2 : ℝ) ^ k)) +
          regularizedCarlsonLogNormEndpointExplicit
            A 4 X sigma ((2 : ℝ) ^ n) v (4 * (2 : ℝ) ^ n) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicCover
  refine ⟨A, hA, ?_⟩
  intro X sigma v n hX hsigma hsigma1 hnv hvn hboundary
  refine (hbound X sigma v n hX hsigma hsigma1 hnv hvn hboundary).trans ?_
  apply add_le_add
  · apply Finset.sum_le_sum
    intro k hk
    exact regularizedCarlsonLogNormEndpoint_le_explicit
      (by linarith) hsigma1 (one_le_pow₀ (by norm_num))
        (pow_le_pow_right₀ (by norm_num) (Nat.le_succ k))
  · exact regularizedCarlsonLogNormEndpoint_le_explicit
      (by linarith) hsigma1 (one_le_pow₀ (by norm_num)) hnv

/-- The full left vertical edge is a fixed low-height segment plus the
dyadic high-height cover.  All height growth is isolated in the endpoint
sum; the remaining low segment has length at most two in Carlson's good
rectangle. -/
theorem exists_integral_log_norm_regularizedCarlsonZeroDetector_le_low_add_dyadicCover :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma y0 v : ℝ) (n : ℕ),
      1 ≤ X → 1 / 2 < sigma → sigma < 1 → y0 ≤ 1 →
      (2 : ℝ) ^ n ≤ v → v ≤ (2 : ℝ) ^ (n + 1) →
      (∀ t ∈ Set.Icc y0 v,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in y0..v,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          (∫ t in y0..1,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖) +
          (∑ k ∈ Finset.range n,
            regularizedCarlsonLogNormEndpoint
              A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
                (4 * (2 : ℝ) ^ k)) +
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma ((2 : ℝ) ^ n) v (4 * (2 : ℝ) ^ n) := by
  obtain ⟨A, hA, hcover⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicCover
  refine ⟨A, hA, ?_⟩
  intro X sigma y0 v n hX hsigma hsigma1 hy0 hnv hvn hboundary
  let f : ℝ → ℝ := fun t =>
    Real.log ‖regularizedCarlsonZeroDetector X
      ((sigma : ℂ) + Complex.I * t)‖
  have hpowOne : 1 ≤ (2 : ℝ) ^ n :=
    one_le_pow₀ (by norm_num)
  have honev : 1 ≤ v := hpowOne.trans hnv
  have hboundaryLow : ∀ t ∈ Set.uIcc y0 1,
      regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hy0] at ht
    exact hboundary t ⟨ht.1, ht.2.trans honev⟩
  have hboundaryHigh : ∀ t ∈ Set.Icc 1 v,
      regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t) ≠ 0 := by
    intro t ht
    exact hboundary t ⟨hy0.trans ht.1, ht.2⟩
  have hhigh := hcover X sigma v n hX hsigma hsigma1
    hnv hvn hboundaryHigh
  have hlowInt : IntervalIntegrable f MeasureTheory.volume y0 1 :=
    intervalIntegrable_log_norm_regularizedCarlsonZeroDetector
      (by linarith) hboundaryLow
  have hhighInt : IntervalIntegrable f MeasureTheory.volume 1 v := by
    apply intervalIntegrable_log_norm_regularizedCarlsonZeroDetector
      (by linarith)
    intro t ht
    rw [Set.uIcc_of_le honev] at ht
    exact hboundaryHigh t ht
  calc
    (∫ t in y0..v, f t) =
        (∫ t in y0..1, f t) + ∫ t in 1..v, f t := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        hlowInt hhighInt).symm
    _ ≤ (∫ t in y0..1, f t) +
        ((∑ k ∈ Finset.range n,
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
              (4 * (2 : ℝ) ^ k)) +
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma ((2 : ℝ) ^ n) v (4 * (2 : ℝ) ^ n)) := by
      simpa [f] using
        (add_le_add_right hhigh (∫ t in y0..1, f t))
    _ = (∫ t in y0..1, f t) +
          (∑ k ∈ Finset.range n,
            regularizedCarlsonLogNormEndpoint
              A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
                (4 * (2 : ℝ) ^ k)) +
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma ((2 : ℝ) ^ n) v (4 * (2 : ℝ) ^ n) := by
      ring

/-- The full left edge has only one fixed low-height integral remaining; all
height-dependent endpoint terms are explicit. -/
theorem exists_integral_log_norm_regularizedCarlsonZeroDetector_le_low_add_dyadicCoverExplicit :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma y0 v : ℝ) (n : ℕ),
      1 ≤ X → 1 / 2 < sigma → sigma < 1 → y0 ≤ 1 →
      (2 : ℝ) ^ n ≤ v → v ≤ (2 : ℝ) ^ (n + 1) →
      (∀ t ∈ Set.Icc y0 v,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in y0..v,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          (∫ t in y0..1,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖) +
          (∑ k ∈ Finset.range n,
            regularizedCarlsonLogNormEndpointExplicit
              A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
                (4 * (2 : ℝ) ^ k)) +
          regularizedCarlsonLogNormEndpointExplicit
            A 4 X sigma ((2 : ℝ) ^ n) v (4 * (2 : ℝ) ^ n) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_integral_log_norm_regularizedCarlsonZeroDetector_le_low_add_dyadicCover
  refine ⟨A, hA, ?_⟩
  intro X sigma y0 v n hX hsigma hsigma1 hy0 hnv hvn hboundary
  refine (hbound X sigma y0 v n hX hsigma hsigma1 hy0 hnv hvn hboundary).trans ?_
  apply add_le_add
  · have hsum :
        (∑ k ∈ Finset.range n,
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
              (4 * (2 : ℝ) ^ k)) ≤
        ∑ k ∈ Finset.range n,
          regularizedCarlsonLogNormEndpointExplicit
            A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
              (4 * (2 : ℝ) ^ k) := by
        apply Finset.sum_le_sum
        intro k hk
        exact regularizedCarlsonLogNormEndpoint_le_explicit
          (by linarith) hsigma1 (one_le_pow₀ (by norm_num))
            (pow_le_pow_right₀ (by norm_num) (Nat.le_succ k))
    simpa [add_comm] using
      (add_le_add_right hsum
        (∫ t in y0..1,
          Real.log ‖regularizedCarlsonZeroDetector X
            ((sigma : ℂ) + Complex.I * t)‖))
  · exact regularizedCarlsonLogNormEndpoint_le_explicit
      (by linarith) hsigma1 (one_le_pow₀ (by norm_num)) hnv

end CarlsonZeroDensity
end PrimeNumberTheorem
